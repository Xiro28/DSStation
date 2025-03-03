#include "blockdecoder.h"

#include "mips_code_emiter.h"
#include "PSP/emit/psp_emit.h"
#include "armcpu.h"


#include "Disassembler.h"

#include <functional> 
#include <cmath>

bool instr_does_prefetch(u32 opcode);

inline void loadReg(psp_gpr_t psp_reg, s32 nds_reg) { if (nds_reg != -1) emit_lw(psp_reg, RCPU, _reg(nds_reg)); }
inline void storeReg(psp_gpr_t psp_reg, s32 nds_reg) { if (nds_reg != -1) emit_sw(psp_reg, RCPU, _reg(nds_reg)); }

#include "psp_sra.h"

#define offsetBetween(x, x2) (((u32)&x) - ((u32)&x2[0]))
#define offsetBetween2(x, x2) (((u32)&x2[0]) - ((u32)&x))

u32 mem_off = 0;
u32 dtcm_addr_arr = 0;
int intr_instr = 0;

u32 start_block = 0;

block currentBlock;  
//reg_allocation reg_alloc; 
register_manager regman;

const char * compiled_functions_hash = 
    ">:1:05:8FDA19B2:C2AF4F28:998B99C6:F0596DB3:2FD2AA9B" //used by yoshi island ingame
    ">:1:07:88DD1AED:096B3BDA:7857790C:6D443C78:A4ADDB58" //a lot used in pokemon diamond 
    ;



uint32_t conditional_label = 0;
uint32_t jump_sz = 0;

inline int constexpr getTypeIdx(opType op) {
    switch (op) {
        case PRE_OP_LSL_IMM: return 0;
        case PRE_OP_LSR_IMM: return 1;
        case PRE_OP_ASR_IMM: return 2;
        case PRE_OP_ROR_IMM: return 3;
        case PRE_OP_LSL_REG: return 4;
        case PRE_OP_LSR_REG: return 5;
        case PRE_OP_ASR_REG: return 6;
        case PRE_OP_ROR_REG: return 7;
        default: 
            //printf("Is this alright?\n");
            return -1; // Default or error value
    }
}

//make an array of pointers to functions of type void 
//and pass the opcode to the function
std::function<void(psp_gpr_t src, psp_gpr_t dst, opcode &op)> arm_preop[] = {
    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {    //PRE_OP_LSL_IMM
        //printf("PRE_OP_LSL_IMM %d \n", op.imm);
	    emit_sll(dst, src, op.imm);
    },

    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_LSR_IMM
        //printf("PRE_OP_LSR_IMM %d \n", op.imm);
        emit_srl(dst, src, op.imm);
    },

    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_ASR_IMM
        emit_sra(dst, src, op.imm ? op.imm : 31); 
    },

    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_ROR_IMM

        if (op.imm == 0){
            emit_srl(dst, src, 1);
            emit_ext(psp_t1, psp_gp, _flag_C8, _flag_C8);
            emit_ins(dst, psp_t1, 31, 31);
            return;
        }
        
        emit_rotr(dst, src, op.imm);
    },
    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {    //PRE_OP_LSL_REG
        //printf("PRE_OP_LSL_IMM %d \n", op.imm);
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);   
        emit_sllv(dst, src, regs[0]);
    },
    
    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_LSR_REG
        //printf("PRE_OP_LSR_IMM %d \n", op.imm);
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);      
        emit_srlv(dst, src, regs[0]);
    },
   
    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_ASR_REG
        //printf("PRE_OP_LSR_IMM %d \n", op.imm);
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);   
        emit_srav(dst, src, regs[0]);
    }, 
    
    [] (psp_gpr_t src, psp_gpr_t dst, opcode& op) -> void {   //PRE_OP_ROR_REG
        int32_t regs[1] = {op.imm};
        regman.get(1, regs); 
        emit_rotrv(dst, src, regs[0]);
    },
};

#define cpu (&ARMPROC)

template<int PROCNUM>
static u16 FASTCALL _LDRH(u32 adr)
{
	return READ16(cpu->mem_if->data, adr);
} 

template<int PROCNUM>
static void FASTCALL _STRH(u32 regs, u32 imm)
{
    u32 adr = (u32)cpu->R[regs>>8] + imm;
    u32 data = (u32)cpu->R[regs&0xFF];
	WRITE16(cpu->mem_if->data, adr, data);
}


void emit_li(u32 reg,u32 data,u32 sz=0)
{
	if (is_u16(data) && sz!=2)
	{
		emit_ori(reg,psp_zero,data&0xFFFF);
	}
	else if (is_s16(data) && sz!=2)
	{
		emit_movi(reg, data&0xFFFF);
	}
	else
	{
		emit_lui(reg,data>>16);
		if ((sz==2) || (data&0xFFFF))
		{
			emit_ori(reg,reg,data&0xFFFF);
		}
	}
}

//load upper address
inline u32 emit_lua(u32 reg,u32 data)
{
    u32 hi = data>>16;
    u32 lo = data&0xFFFF;

    if (lo&0x8000){
        hi++;
        lo = data - (hi<<16);
    }

    emit_lui(reg,u16(hi));
	return lo;
}

void generate_condition_check(int cond){
    static const uint8 cond_bit[] = {0x40, 0x40, 0x20, 0x20, 0x80, 0x80, 0x10, 0x10};

	if(cond < 8)
	{
      emit_andi(psp_s4, psp_gp, cond_bit[cond]);
      return;
    }

    switch (cond){
    
        case 8:  
        case 9:
            emit_ext(psp_a1,psp_gp,6,5);
            emit_xori(psp_s4,psp_a1,0b01);
        break;
    
        case 10:
        case 11:
    
            emit_ext(psp_a1,psp_gp,7,7);
            emit_ext(psp_at,psp_gp,4,4);
    
            emit_xor(psp_s4,psp_a1,psp_at);
        break;
    
        case 12:
        case 13:
    
            emit_ext(psp_a1,psp_gp,7,6);
            emit_ext(psp_at,psp_gp,4,3);
    
            emit_andi(psp_at,psp_at,0b10);
            emit_xor(psp_s4,psp_a1,psp_at);
        break;
    }
}

uint32 emit_Halfbranch(int cond, bool generate_condition = true)
{
    if (generate_condition) generate_condition_check(cond);

    emit_nop();
    emit_nop();
    return emit_getPointAdr() - 8;
}

void CompleteCondition(u32 cond, u32 _addr, u32 label){
    if(cond < 8)
	{
      if (cond&1)
         emit_bnelC(psp_s4,psp_zero,label,_addr);
      else
         emit_beqlC(psp_s4,psp_zero,label,_addr);
      return;
   }

   if (cond&1)
      emit_beqlC(psp_s4,psp_zero,label,_addr);
   else
      emit_bnelC(psp_s4,psp_zero,label,_addr);
}
bool saved = false;
void emit_prefetch(const u8 isize, bool saveR15, bool is_ITP){

   static int skip = 1;

   if (saveR15 || is_ITP){

        emit_addiu(psp_fp, psp_fp, isize * skip);

    if (is_ITP)
        emit_sw(psp_fp, RCPU, _next_instr);

    saved = false;

    emit_addiu(psp_at, psp_fp, isize);
    emit_sw(psp_at, RCPU, _R15);

    skip = 1;
   }else
        skip++;
} 


INLINE void emit_bic(u32 dst,u32 a0, u32 a1)
{
    emit_not(a1, a1);
	emit_and(dst, a0, a1); 
}

INLINE void emit_bici(u32 dst,u32 a0, u32 a1)
{
	emit_andi(dst, a0, ~a1);
}  

#define END_OP(_rd) \
    {\
        regman.mark_dirty((psp_gpr_t)_rd);\
        if (!rd_allocated) regman.flush((psp_gpr_t)_rd);\
    }  

#define END_OP_CHKR15(_rd) \
    {\
        regman.mark_dirty((psp_gpr_t)_rd);\
        if (op.rd == 15) \
            {op.check_condition = false; conditional(emit_sw(_rd, RCPU, _next_instr););} \
    }

#define HANDLE_CONDITIONAL(branchless_code, branch_code)                             \
    do {                                                                             \
        if (op.rd != 15) {                                                           \
            conditional_branchless(regs[0], psp_at,                                  \
                {                                                                    \
                    branchless_code                                                  \
                }                                                                    \
            );                                                                       \
            END_OP_CHKR15(regs[0]);                                                  \
        } else {                                                                     \
            conditional(                                                             \
                branch_code                                                          \
                END_OP_CHKR15(regs[0]);                                              \
            );                                                                       \
        }                                                                            \
    } while(0)
 
#define HANDLE_CONDITIONAL_NR15(branchless_code, branch_code)                        \
    do {                                                                             \
        if ((rd_allocated) && (op).condition != -1) {                                \
            conditional_branchless(regs[0], psp_at,                                  \
                {                                                                    \
                    branchless_code                                                  \
                }                                                                    \
            );                                                                       \
            END_OP(regs[0]);                                                         \
        } else {                                                                     \
            conditional(                                                             \
                branch_code                                                          \
                END_OP(regs[0]);                                                     \
            );                                                                       \
        }                                                                            \
    } while(0)
 
#define gen_nativeOP(opType, n_op, n_op_imm, sign) \
template <bool imm, bool rev> void arm_##opType(opcode &op){ \
    int32_t regs[3] = {(op.condition != -1) ? op.rd : (op.rd | 0x10), op.rs1, op.rs2};\
    const int reg_count = imm ? 2 : 3;\
    regman.get(reg_count, regs); \
    const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];\
    if (imm){ \
        if (!rev && is_##sign##16(op.imm)) { \
            conditional_branchless(regs[0], dst, \
            { \
                emit_##n_op_imm(dst, regs[1], op.imm);\
            });\
        } else{ \
            conditional_branchless(regs[0], dst, \
            { \
                emit_li(psp_at, op.imm); \
                if (!rev) \
                    emit_##n_op(dst, regs[1], psp_at); \
                else \
                    emit_##n_op(dst, psp_at, regs[1]);\
            });\
        } \
    }else{ \
        conditional_branchless(regs[0], dst,\
        { \
            arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[2], psp_at, op); \
            if (!rev) \
                    emit_##n_op(dst, regs[1], psp_at); \
            else \
                emit_##n_op(dst, psp_at, regs[1]); \
        });\
    } \
    END_OP_CHKR15(regs[0]); \
}

gen_nativeOP(and, and, andi, u);
gen_nativeOP(or, or, ori, u);
gen_nativeOP(xor, xor, xori, u);
gen_nativeOP(add, addu, addiu, s);
gen_nativeOP(sub, subu, subiu, s);
gen_nativeOP(bic, bic, bici, u);

//Do you want speed? call this function if you want to see some black magic :D

void block::optimize_basicblock(){

    // Now useless since it behaved like a SRA but without actually allocating the registers
    // Maybe we can use it for something else (like removing useless operations)


    // Check if we can merge togheter a conditional check with 2 or more opcodes
    // Example:
    // moveq r0, #0
    // moveq r1, #0
    // They both rely on the same condition (eq), so we can merge them togheter and do the check just once
    // However we can do this only the opcode that support the branchless check
    opcode *prev_op = 0;
 
    for(opcode& op : opcodes){
        if (prev_op && prev_op->_op != OP_ITP && op.condition == prev_op->condition) op.check_condition = false;
        prev_op = &op;
    } 

    return;
}

void block::optimize_basicblockThumb(){
    opcode *prev_op = 0;
    opcode *prev_ITP = 0; 

    bool savedN = false;
    bool savedZ = false;
    bool savedC = false;
    bool savedV = false;

    for (int i = opcodes.size() - 1; i >= 0; --i){
        opcode& op = opcodes[i];

        if (op.extra_flags & EXTFL_NOFLAGS) continue;

        switch (op._op)
        {
            case OP_STR:
            case OP_STRH:
            case OP_LDR:
            case OP_LDRH:
            case OP_ITP:
                savedN = false;
                savedZ = false;
                savedC = false;
                savedV = false;
            break;

            case OP_AND:
            case OP_ADD:
            case OP_EOR:
            case OP_ORR:
            case OP_TST:
            case OP_MUL:
            case OP_MOV:
            case OP_MVN:

                if (!savedC){
                    savedC = true;
                }else
                    op.saveC = false;

                if (!savedN){
                    savedN = true;
                }else
                    op.saveN = false;

                if (!savedZ){
                    savedZ = true;
                }else
                    op.saveZ = false;

            break;

            case OP_SUB:
            case OP_CMP:
                if (!savedN){
                    savedN = true;
                }else
                    op.saveN = false;

                if (!savedZ){
                    savedZ = true;
                }else
                    op.saveZ = false;

                if (!savedC){
                    savedC = true;
                }else
                    op.saveC = false;
                
                if (!savedV){
                    savedV = true;
                }else
                    op.saveV = false;

            break;

        
        default:
            break;
        }
    } 
    /*if (noReadWriteOP && branch_addr == start_addr){
        for(opcode& op : opcodes){
            if (op._op == OP_SWI){

                idleLoop = true;
                break;
            }
        }
    } */
}

extern "C" void set_sub_flags();
extern "C" void set_and_flags();
extern "C" void set_op_logic_flags(); 

#define cpu (&ARMPROC)

void lastBeforeCrash(int a0, int a1){
    printf("0x%x\n", a0);
}


void EmitReadFunction(u32 addr){
	unsigned 	o_ra;
	extern u8 *CodeCache;

	//Execute the patch at the end (overwrite ra addr inside the sp)
	asm volatile("addiu $2, $31, -8"); 
	asm volatile("sw $2, 0x14($29)");

	//Get the current ra 
	asm volatile("sw $31, %0":"=m"(o_ra));

	u32 _ptr = emit_Set((o_ra - 8) - 0x8400000);

    printf("EmitReadFunction: 0x%x 0x%x\n", o_ra, 0x8400000); 

	if((addr&(~0x3FFF)) == MMU.DTCMRegion){
        emit_li(psp_t1, (u32)MMU.ARM9_DTCM);
        emit_andi(psp_a0, psp_a0, 0x3FFC);
    }
    else{
        emit_li(psp_t1, (u32)MMU.MAIN_MEM);
        emit_ins(psp_a0, psp_zero, 31, 22);
    }

    emit_addu(psp_a0, psp_t1, psp_a0);
    emit_lw(psp_v0, psp_a0, 0);
  
	emit_Set(_ptr);

	//make_address_range_executable(o_ra - 8, o_ra - 4);
	u32 addr_start = o_ra - 8;
	__builtin_allegrex_cache(0x1a, addr_start);
	__builtin_allegrex_cache(0x08, addr_start);
}

bool flag_loaded = false;
bool use_flags = false;
bool islast_op = false;

bool flag_dirty = false;

void load_flags(){
    //if (use_flags && !flag_loaded)
    {
        emit_lbu(psp_gp, RCPU, _flags+3);
        flag_loaded = true;
    }
}

void store_flags(){
    if (use_flags && flag_loaded)
    {
        emit_sb(psp_gp, RCPU, _flags+3);
        flag_loaded = false;
    }
}
 
template <bool execute>
u32 jump_to_linked(u32 addr, u32 _r15){
    // check if the addr is already compiled
    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(addr, ARM9);

    NDS_ARM9.CPSR.bits.T = BIT0(addr);
    NDS_ARM9.R[15] = addr & (0xFFFFFFFC|(NDS_ARM9.CPSR.bits.T<<1));
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];
   
    if (flag_dirty) store_flags();
    flag_dirty = false;

    if (code_block){
        //printf("Fast jump\n");
        const u32 cycles = code_block();
        return cycles;
    }

    // compile the block
    //printf("Compile block\n");
    //const u32 cycles = arm_jit_compile<ARM9>();
	return 3;
}


u32 _read32(u32 addr, u32 addr_mem)
{
    if((addr&(~0x3FFF)) == MMU.DTCMRegion)
        return *(u32*)(MMU.ARM9_DTCM + (addr & 0x3FFC));

	return *(u32*)(MMU.MAIN_MEM + addr_mem);
}

template<int PROCNUM>
void emitARMOP(opcode& op, uint32_t reg_usage_end[17]){  

    const bool rd_allocated = regman.is_mapped(op.rd);

    //printf("OP: %d\n", op._op);
    
 
    switch(op._op){
  
        case OP_ITP:
        {

            conditional(
                if (flag_dirty) store_flags();

                flag_dirty = false;
                
                emit_li(psp_a0, op.rs1); 

                uint32_t optmizeDelaySlot = emit_SlideDelay();

                emit_jal(arm_instructions_set[INSTRUCTION_INDEX(op.rs1)]); 
                emit_Write32(optmizeDelaySlot);

                load_flags();
            )

            intr_instr++;
        }
        break; 
        case OP_AND:{ 

            if (op.preOpType == PRE_OP_IMM){
                arm_and<true, false>(op);
            }
            else {
                //printf("IMM: 0x%x\n", emit_getCurrAdr());
                arm_and<false, false>(op);
            }
        } 
        break;
 
        case OP_BIC:
            if (op.preOpType == PRE_OP_IMM)
                arm_bic<true, false>(op);
            else 
                arm_bic<false, false>(op);
        break;

        case OP_ORR:{
            
            if (op.preOpType == PRE_OP_IMM){
                arm_or<true, false>(op);
            }
            else {
                arm_or<false, false>(op);
            }
        break;
        }

        case OP_EOR:
            if (op.preOpType == PRE_OP_IMM)
                arm_xor<true, false>(op);
            else 
                arm_xor<false, false>(op);

        break;

        case OP_ADD:
        {
            if (op.preOpType == PRE_OP_IMM){
                arm_add<true, false>(op);
            }
            else {
                /*if (op.rs1 == 15 && op.rd == 15 && op.preOpType == PRE_OP_LSL_IMM){

                    int32_t regs[3] = {op.rd, op.rs1, op.rs2}; 
                    conditional(
                        regman.get(3, regs);

                        arm_preop[op.preOpType]((psp_gpr_t)regs[2], psp_at, op); 
                        emit_addu((psp_gpr_t)regs[0], (psp_gpr_t)regs[1], psp_at);

                        emit_sw((psp_gpr_t)regs[0], RCPU, _next_instr);
                    );


                    printf("Special ADD\n");
                }else*/
                    arm_add<false, false>(op);
            }
            break;
        }
       case OP_SUB:
       {
            if (op.preOpType == PRE_OP_IMM){
                arm_sub<true, false>(op);
            }
            else {
                arm_sub<false, false>(op);
            }
        break;
    }

        
        case OP_RSB:
            if (op.preOpType == PRE_OP_IMM)
                arm_sub<true, true>(op);
            else 
                arm_sub<false, true>(op);
        break;
        case OP_MUL:
        {
            int32_t regs[3] = { op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2 };

            HANDLE_CONDITIONAL_NR15(
                {
                    regman.get(3, regs);
                    
                    emit_mult(regs[1], regs[2]);
                    emit_mflo(psp_at);
                },{
                    regman.get(3, regs);
                    
                    emit_mult(regs[1], regs[2]);
                    emit_mflo(regs[0]);
                }
            );
            break; 
        }

        case OP_MLA:
        {
            int32_t regs[4] = { op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2, op.imm };
            
             HANDLE_CONDITIONAL_NR15(
                {
                    regman.get(4, regs);
                    
                    emit_mult(regs[1], regs[2]);
                    emit_mflo(psp_at);
                    emit_addu(psp_at, psp_at, regs[3]);
                },{
                    regman.get(4, regs);
                    
                    emit_mult(regs[1], regs[2]);
                    emit_mflo(psp_at);
                    emit_addu(regs[0], psp_at, regs[3]);
                }
            );
            break; 
        }

        case OP_UMUL:{
            int32_t regs[4] = { op.condition != -1 ? op.rd : (op.rd | 0x10), op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2 };
            
            HANDLE_CONDITIONAL_NR15(
                {
                    regman.get(4, regs);
                    
                    emit_multu(regs[2], regs[3]);
                    emit_mflo(psp_at);
                    emit_mfhi(regs[1]);
                    END_OP(regs[1]);
                },{
                    regman.get(4, regs);
                    
                    emit_multu(regs[2], regs[3]);
                    emit_mflo(regs[0]);
                    emit_mfhi(regs[1]);
                    END_OP(regs[1]);
                }
            );
            break; 
        }

        case OP_UMLA:{
            int32_t regs[4] = { op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2, op.imm };
            
            HANDLE_CONDITIONAL_NR15(
                {
                    regman.get(4, regs);
                    
                    emit_multu(regs[1], regs[2]);
                    emit_mflo(psp_at);
                    emit_addu(psp_at, psp_at, regs[3]);
                },{
                    regman.get(4, regs);
                    
                    emit_multu(regs[1], regs[2]);
                    emit_mflo(psp_at);
                    emit_addu(regs[0], psp_at, regs[3]);
                }
            );
            break; 
        }

        case OP_CLZ:
        {
            int32_t regs[2] = {op.rd, op.rs1};
            regman.get(2, regs);
            
            const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];
            
            conditional_branchless(regs[0], dst,{
                emit_clz(dst, regs[1]);
            });

            regman.mark_dirty((psp_gpr_t)regs[0]);
            break;
        }

        case OP_SWI:
        {
            conditional(
                emit_jal(cpu->swi_tab[op.rs1]); 
                emit_nop();
            )
        }

        case OP_MOV:
        case OP_MVN:
        {
            int32_t regs[2] = { op.condition != -1 ? op.rd : op.rd | 0x10, op.rs2};

            if (op.preOpType == PRE_OP_IMM){
                regman.get(1, regs);
                const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0]; 

                conditional_branchless(regs[0], ((op.imm == 0 && op.condition != -1) ? psp_zero : dst),
                    {
                        if (op.imm != 0) emit_li(dst, op.imm);
                        else /*if (op.imm == 0 && op.condition == -1)*/ emit_move(dst, psp_zero);
                    }
                );
            }else{ 
                regman.get(2, regs);
                const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];
                
                conditional_branchless(regs[0], dst,
                    {
                        arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[1], dst, op);

                        if (op._op == OP_MVN)
                            emit_not(dst, dst);
                    }
                );

            }
            END_OP_CHKR15(regs[0])
            break;
        }

        case OP_BXC:
        {
            regman.flush_all(false);
            regman.reset();
            
            //printf("0x%x, %d\n", (u32)emit_getCurrAdr(), op.rs1);

            emit_movi(psp_v0, 3);
            conditional(
                emit_jal(jump_to_linked<true>); 
                loadReg(psp_a0, op.rs1);
            )
            /*int32_t regs[1] = {op.rs1};

            emit_movi(psp_v0, 3);

            //printf("0x%x\n", (u32)emit_getCurrAdr());
            conditional(
                regman.get(1, regs);

                if (is_u16(op.imm)){
                    emit_addiu(regs[0], regs[0], op.imm); 
                }else{
                    emit_li(psp_a0, op.imm);             
                    emit_addu(regs[0], regs[0], psp_a0);  
                }

                printf("%d\n", (NDS_ARM9.CPSR.bits.T ));
                NDS_ARM9.CPSR.bits.T = BIT0(addr);
	            NDS_ARM9.R[15] = addr & (0xFFFFFFFC|(NDS_ARM9.CPSR.bits.T<<1));

                emit_andi(psp_a0, regs[0], 0x1);

                emit_ins(psp_gp, psp_a0, _flag_C8, _flag_C8);
                emit_li(psp_a1, 0xFFFFFFFC);

                emit_sll(psp_a0, psp_a0, 1);
                emit_or(psp_a0, psp_a0, psp_a1);
                 
                emit_and(regs[0], );  

                emit_sw(psp_a0,  RCPU, );
                emit_sw(regs[0], RCPU, _instr_adr);
                emit_sw(regs[0], RCPU, _next_instr);
                regman.mark_dirty((psp_gpr_t)regs[0]);
            )*/
        }break;

        case OP_STR:
        case OP_STRH: 
        {
            int32_t regs[3] = { op.rd, op.rs1, op.rs2};

            regman.flush_all(true); 

            conditional(
                regman.get(3, regs);

                const int special_type =  op.preOpType >> 16;
                const bool is_special_type = (special_type == PRE_OP_LSL_IMM || special_type == PRE_OP_LSR_IMM || 
                    special_type == PRE_OP_ASR_IMM || special_type == PRE_OP_ROR_IMM);
                const int type = op.preOpType & 0xff;

                const bool positive = op.imm >= 0;

                if (is_special_type){
                    const int idx = getTypeIdx((opType)special_type);

                    op.imm = op.imm < 0 ? -op.imm : op.imm;

                    if (idx >= 0) 
                        arm_preop[idx]((psp_gpr_t)regs[2], psp_t0, op);
                    else
                        printf("STR not encoded correctly: %d\n", idx);
                    //printf("Addr: %x\n", emit_getCurrAdr());
                    //printf("STR not encoded correctly: %d\n", idx);
                }
                
                if (type == PRE_OP_IMM_PRE_P || type == PRE_OP_IMM_PRE_M) { 

                    if (!is_special_type)  emit_addiu(psp_a0, regs[0], op.imm);
                    else {
                        if (positive) emit_addu(psp_a0, regs[0], psp_t0);
                        else emit_subu(psp_a0, regs[0], psp_t0);
                    }
                    
                    storeReg(psp_a0, op.rd);
                } 
                else if (type == PRE_OP_IMM_POST_P || type == PRE_OP_IMM_POST_M) {   
                    emit_move(psp_a0, regs[0]); 

                    if (!is_special_type) emit_addiu(regs[0], regs[0], op.imm);
                    else {
                        if (positive) emit_addu(regs[0], regs[0], psp_t0);
                        else emit_subu(regs[0], regs[0], psp_t0);
                    }

                    storeReg((psp_gpr_t)regs[0], op.rd);

                } else if (type == PRE_OP_IMM) {  
                    if (is_special_type) {
                        if (positive) emit_addu(psp_a0, regs[0], psp_t0);
                        else emit_subu(psp_a0, regs[0], psp_t0);
                    }else{
                        if (is_u16(op.imm)) {
                            emit_addiu(psp_a0, regs[0], op.imm); 
                        } else {
                            emit_li(psp_a0, op.imm);             
                            emit_addu(psp_a0, regs[0], psp_a0);  
                        }
                    }
                } 

                
                emit_move(psp_a1, regs[1]);
                
                if (OP_STRH == op._op) {
                    emit_jal(_MMU_write16<PROCNUM>); 
                    emit_ins(psp_a0, psp_zero, 0, 0);
                } else { 
                    emit_jal(_MMU_write32<PROCNUM>);
                    emit_ins(psp_a0, psp_zero, 1, 0);
                }

                regman.reset(); 

                /*if (op.condition == -1) {
                    //optimization: mantain those regs since they aren't affected by the storing function
                    regman.map(op.rd, (psp_gpr_t)regs[0]);
                    regman.map(op.rs1, (psp_gpr_t)regs[1]);
                    //printf("Mapped %d to %d 0x%x\n", op.rd, regs[0], (u32)emit_getCurrAdr());
                }*/
            )
        }
        break;

        case OP_LDRSH:
        case OP_LDRSB:
        case OP_LDRH:
        case OP_LDR:
        {
            const int special_type =  op.preOpType >> 16;
            const bool is_special_type = (special_type == PRE_OP_LSL_IMM || special_type == PRE_OP_LSR_IMM || 
                special_type == PRE_OP_ASR_IMM || special_type == PRE_OP_ROR_IMM);
            const int type = op.preOpType & 0xff;

            const bool positive = op.imm >= 0;

            int32_t regs[3] = { op.rd | 0x10, op.rs1, is_special_type ? op.rs2 : -1};

            bool skip = false;

            /*if (op.extra_flags & EXTFL_DIRECTMEMACCESS && op.condition == -1 && op._op == OP_LDR && !special_type) {
                skip = true;
            } else {
                regman.flush_all(true);
            }*/

           regman.flush_all(true);

            conditional(
                regman.get(3, regs);
                
                if (is_special_type){
                    const int idx = getTypeIdx((opType)special_type);

                    op.imm = op.imm < 0 ? -op.imm : op.imm;

                    if (idx >= 0) 
                        arm_preop[idx]((psp_gpr_t)regs[2], psp_t0, op);
                    else
                        printf("LDR not encoded correctly: %d\n", idx);
                }

                if (type == PRE_OP_IMM)  {
                    if (is_special_type) {
                        if (positive) emit_addu(psp_a0, regs[1], psp_t0);
                        else emit_subu(psp_a0, regs[1], psp_t0);
                    } else {
                        if (is_u16(op.imm)){
                            emit_addiu(psp_a0, regs[1], op.imm); 
                        }else{
                            emit_li(psp_a0, op.imm);             
                            emit_addu(psp_a0, regs[1], psp_a0);  
                        }
                    }
                }
                else if (type == PRE_OP_IMM_PRE_P || type == PRE_OP_IMM_PRE_M)   {
                    if (is_special_type) {
                        if (positive) emit_addu(psp_a0, regs[1], psp_t0);
                        else emit_subu(psp_a0, regs[1], psp_t0);
                    } else {
                        emit_addiu(psp_a0, regs[1], op.imm);
                    }
                        storeReg(psp_a0, op.rs1);
                }
                else if (type == PRE_OP_IMM_POST_P || type == PRE_OP_IMM_POST_M)   {
                    emit_move(psp_a0, regs[1]);

                    if (is_special_type) {
                        if (positive) emit_addu(psp_t1, psp_a0, psp_t0);
                        else emit_subu(psp_t1, psp_a0, psp_t0);
                    } else {
                        emit_addiu(psp_t1, psp_a0, op.imm);
                    }
                    
                    storeReg(psp_t1, op.rs1);
                }

                if (OP_LDR == op._op) {

                    if (op.extra_flags & EXTFL_DIRECTMEMACCESS)
                    {
                        //printf("DIRECT ACCEESS %x, %x, %x\n", MMU.ARM9_DTCM, MMU.MAIN_MEM, (u32)&MMU.DTCMRegion);
                        emit_sll(regs[0], psp_a0, 3);

                        emit_move(psp_a1, psp_a0);
                        emit_jal(_read32);
                        emit_ins(psp_a1, psp_zero, 31, 22);

                        emit_rotrv(regs[0], psp_v0, regs[0]);

                        /*emit_lui(psp_v1, 0x9DF);
                        emit_or(psp_v1, RCPU, psp_v1);*/

                        /*emit_li(psp_v1, (u32)&MMU.MAIN_MEM);

                        emit_sll(regs[0], psp_a0, 3);

                        // Load the address of the memory 
                        emit_ins(psp_a0, psp_zero, 1, 0);

                        // Load the address of the DTCM
                        emit_lw(psp_a1, psp_v1, dtcm_addr2);

                        emit_move(psp_a2, psp_a0);
                        emit_ins(psp_a0, psp_zero, 31, 22);

                        // Mask the last 14 bits for the DTCM
                        emit_ins(psp_a2, psp_zero, 13, 0);
                        emit_subu(psp_a2, psp_a1, psp_a2);

                        // If DTCM move the addr to a0
                        emit_andi(psp_a3, psp_a0, 0x3FFC);
                        emit_movz(psp_a0, psp_a3, psp_a2);

                        emit_addiu(psp_t3, psp_v1, dtcm_mem2);
                        
                        emit_movz(psp_v1, psp_t3, psp_a2);

                        emit_addu(psp_v1, psp_v1, psp_a0);

                        emit_lw(psp_v0, psp_v1, 0);

                        emit_rotrv(regs[0], psp_v0, regs[0]);
                        

                        /*emit_move(psp_a1, psp_a0);
                        emit_jal(_read32);
                        emit_ins(psp_a1, psp_zero, 31, 22);

                        emit_li(psp_a1, (u32)_read32);
                        emit_li(psp_a0, emit_getCurrAdr());
                        emit_jal(lastBeforeCrash);
                        emit_nop();*/
                        
                    }else{
                        //printf("SLOW ACCEESS\n");

                        emit_sll(regs[0], psp_a0, 3);

                        emit_jal(_MMU_read32<PROCNUM>);
                        emit_ins(psp_a0, psp_zero, 1, 0);
                        
                        emit_rotrv(regs[0], psp_v0, regs[0]);
                    }

                } else if (OP_LDRSB == op._op) {
                    u32 op = emit_SlideDelay();
                    emit_jal(_MMU_read08<PROCNUM>); 
                    emit_Write32(op);
                    emit_seb(regs[0], psp_v0);
                } else {
                    emit_jal(_MMU_read16<PROCNUM>); 
                    emit_ins(psp_a0, psp_zero, 0, 0);

                    if (op._op == OP_LDRSH) emit_seh(regs[0], psp_v0);
                    else emit_move(regs[0], psp_v0);
                }

               regman.reset(); 

                if (op.condition == -1) {
                    regman.map(op.rd, (psp_gpr_t)regs[0]);
                    regman.mark_dirty((psp_gpr_t)regs[0]);
                }
                else                    
                    storeReg((psp_gpr_t)regs[0], op.rd);
            )
            
        }
        break;


        case OP_CMP:
        case OP_STMIA:
        case OP_NOP:
        case OP_FAST_MUL:
        case OP_LSR_0:        
        case OP_TST:
        case OP_AND_S:
        case OP_EOR_S:
        case OP_ORR_S:
        case OP_ADD_S:
        case OP_SUB_S:
        case OP_MOV_S:
        case OP_MVN_S:
        case OP_NEG:
        default:
        printf("WTF? No opcode defined\n");

        break;

    }
}

#include "thumb_jit.h"

//Already compiled and optimized block
#include "precompiled_ops.h"

template<int PROCNUM>
bool block::emitThumbBlock(){ 

    use_flags = true;

    //reg_alloc.reset(); 

    emit_li(psp_fp, opcodes.front().op_pc);

    opcode last_op = opcodes.back();
    const bool islastITP = last_op._op == OP_ITP;

    load_flags();

    for(opcode op : opcodes){

        const u8 isize = 2;

        //reg_alloc.alloc_regs(op); 

        if (last_op.op_pc != op.op_pc)
            emit_prefetch(isize, op.rs1 == 15 || op.rs2 == 15, op._op == OP_ITP);
        else
            //Last op has always to save 
            emit_prefetch(isize, true, true); 

        emitThumbOP<PROCNUM>(op); 
    } 
     
    if(flag_dirty) store_flags();
    flag_dirty = false;
  
    regman.flush_all();
    regman.reset();

    //possible idle loop, do more checks here
    return idleLoop;

}

static bool instr_is_conditional(u32 opcode)
{
	return !(CONDITION(opcode) == 0xE
	         || (CONDITION(opcode) == 0xF && CODE(opcode) == 5));
}

template<int PROCNUM>
bool block::emitArmBlock(){

    opcode last_op = opcodes.back();

    intr_instr = 0;

    use_flags = uses_flags;

    //char * found = strstr(compiled_functions_hash, block_hash);

    /*if (found != NULL) {
        return arm_compiledOP[(found - compiled_functions_hash) / 51](PROCNUM);
    }*/

   //StartCodeDump();

    start_block = emit_getCurrAdr();
    emit_li(psp_fp, opcodes.front().op_pc);
    
    load_flags();

    regman.reset();

    const u8 isize =  4;
    for(opcode op : opcodes){ 

        if ((op._op == OP_ITP || op._op == OP_SWI)) 
        {
            regman.flush_all();  
            regman.reset();  
        }

        if (op.condition != -1) {
            // not sure if this is the only one to flush... might be that rs1 and rs2 are also needed to be flushed
            // TODO: check if rs1 and rs2 are needed to be flushed
            //regman.flush_nds(op.rd);  
        }


        if (last_op.op_pc != op.op_pc)
            emit_prefetch(isize, op.rs1 == 15 || op.rs2 == 15, op._op == OP_ITP);
        else {
            //Last op has always to save 
            emit_prefetch(isize, true, true);
        }

        emitARMOP<PROCNUM>(op, this->reg_usage_end);         
    } 

    regman.flush_all();
    regman.reset();
    if (flag_dirty) store_flags();
    flag_dirty = false;

    /*if (!JumpOP){
        ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(last_op.op_pc, ARM9);
        if (code_block){
            //printf("fast path\n");
            const u32 op = emit_SlideDelay();
            emit_jal(code_block); 
            emit_Write32(op);

            JumpOP = true;
        }
    }*/



   /* if (opcodes.size() > 30)
        CodeDump("30_ops.bin");*/
   
 
    //possible idle loop, do more checks here
    return idleLoop;
}


template<int PROCNUM>
void block::emitArmBranch(){
    uint32_t conditional_label = 0;
    uint32_t jump_sz = 0;

    opcode op = opcodes.back();

    emit_li(psp_fp, op.op_pc + 4);
    emit_sw(psp_fp, psp_k0, _next_instr);

    emit_addiu(psp_at, psp_fp, 4);  
    emit_sw(psp_at, psp_k0, _R15);

    //conditional(emitARMOP<PROCNUM>(op))
}

// define the template 
template bool block::emitArmBlock<0>();
template bool block::emitArmBlock<1>();

template void block::emitArmBranch<0>();
template void block::emitArmBranch<1>();


