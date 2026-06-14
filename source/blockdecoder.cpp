#include "blockdecoder.h"

#include "mips_code_emiter.h"
#include "PSP/emit/psp_emit.h"
#include "armcpu.h"
#include "MMU.h"

#include "Disassembler.h"

#include <functional>
#include <cmath>

bool instr_does_prefetch(u32 opcode);

inline void loadReg(psp_gpr_t psp_reg, s32 nds_reg)
{
    if (nds_reg != -1)
        emit_lw(psp_reg, RCPU, _reg(nds_reg));
}
inline void storeReg(psp_gpr_t psp_reg, s32 nds_reg)
{
    if (nds_reg != -1)
        emit_sw(psp_reg, RCPU, _reg(nds_reg));
}

#include "psp_sra.h"

#define offsetBetween(x, x2) (((u32) & x) - ((u32) & x2[0]))
#define offsetBetween2(x, x2) (((u32) & x2[0]) - ((u32) & x))

u32 mem_off = 0;
u32 dtcm_addr_arr = 0;
int intr_instr = 0;

u32 start_block = 0;

block currentBlock;
register_manager regman;

bool flag_loaded = false;
bool use_flags = false;
bool islast_op = false;

bool flag_dirty = false;

void load_flags()
{
    if (use_flags /*&& !flag_loaded*/)
    {
        emit_lbu(psp_gp, RCPU, _flags + 3);
        flag_loaded = true;
    }
}

void store_flags()
{
    if (use_flags /*&& flag_loaded*/)
    {
        emit_sb(psp_gp, RCPU, _flags + 3);
        flag_loaded = false;
    }
}

#define check_flags()       \
    if (flag_dirty)         \
    {                       \
        store_flags();      \
        flag_dirty = false; \
    }

#define force_flag_storage() \
    {                        \
        store_flags();       \
        flag_dirty = false;  \
    }

#define set_flag_dirty() flag_dirty = true;

const char *compiled_functions_hash =
    ">:1:05:8FDA19B2:C2AF4F28:998B99C6:F0596DB3:2FD2AA9B" // used by yoshi island ingame
    ">:1:07:88DD1AED:096B3BDA:7857790C:6D443C78:A4ADDB58" // a lot used in pokemon diamond
    ;

uint32_t conditional_label = 0;
uint32_t jump_sz = 0;

inline int constexpr getTypeIdx(opType op)
{
    switch (op)
    {
    case PRE_OP_LSL_IMM:
        return 0;
    case PRE_OP_LSR_IMM:
        return 1;
    case PRE_OP_ASR_IMM:
        return 2;
    case PRE_OP_ROR_IMM:
        return 3;
    case PRE_OP_LSL_REG:
        return 4;
    case PRE_OP_LSR_REG:
        return 5;
    case PRE_OP_ASR_REG:
        return 6;
    case PRE_OP_ROR_REG:
        return 7;
    default:
        printf("Is this alright? Return 0 as value to not make the emulator crash\n %d\n", op);
        return 0; // Default or error value
    }
}

// make an array of pointers to functions of type void
// and pass the opcode to the function
std::function<void(psp_gpr_t src, psp_gpr_t dst, opcode &op)> arm_preop[] = {
    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_LSL_IMM
        // printf("PRE_OP_LSL_IMM %d \n", op.imm);
        emit_sll(dst, src, op.imm);
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_LSR_IMM
        // printf("PRE_OP_LSR_IMM %d \n", op.imm);
        if (op.imm)
            emit_srl(dst, src, op.imm);
        else
            emit_move(dst, psp_zero);
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_ASR_IMM
        emit_sra(dst, src, op.imm ? op.imm : 31);
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_ROR_IMM
        if (op.imm == 0)
        {
            // RRX: dst = (C << 31) | (src >> 1). Read the carry straight from the
            // CPSR byte in the CPU struct so we don't depend on psp_gp having
            // been loaded (non-S/unconditional ALU ops don't load flags).
            emit_srl(dst, src, 1);
            emit_lbu(psp_t1, RCPU, _flags + 3);       // CPSR top byte (NZCV at 7..4)
            emit_ext(psp_t1, psp_t1, _flag_C8, _flag_C8);  // isolate C (bit 5)
            emit_ins(dst, psp_t1, 31, 31);
            return;
        }

        emit_rotr(dst, src, op.imm);
    },
    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_LSL_REG
        // ARM: amount = Rs & 0xFF; if amount >= 32 result is 0 (MIPS sllv only
        // uses low 5 bits, so we must zero the result for amount >= 32).
        // NOTE: dst is often psp_at, so amount/compare must use OTHER scratch.
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);
        emit_andi(psp_v0, (psp_gpr_t)regs[0], 0xFF);   // v0 = amt8
        emit_sllv(dst, src, psp_v0);                   // src << (amt8 & 31)
        emit_sltiu(psp_v1, psp_v0, 32);                // v1 = (amt8 < 32)
        emit_movz(dst, psp_zero, psp_v1);              // amt8 >= 32 -> 0
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_LSR_REG
        // ARM: amount = Rs & 0xFF; if amount >= 32 result is 0.
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);
        emit_andi(psp_v0, (psp_gpr_t)regs[0], 0xFF);
        emit_srlv(dst, src, psp_v0);
        emit_sltiu(psp_v1, psp_v0, 32);
        emit_movz(dst, psp_zero, psp_v1);              // amt8 >= 32 -> 0
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_ASR_REG
        // ARM: amount = Rs & 0xFF; if amount >= 32 result is sign-extension
        // (src >> 31, arithmetic). MIPS srav masks to 5 bits, so clamp.
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);
        emit_andi(psp_v0, (psp_gpr_t)regs[0], 0xFF);   // v0 = amt8
        emit_srav(dst, src, psp_v0);                   // src >>a (amt8 & 31)
        emit_sra(psp_v1, src, 31);                     // sign fill
        emit_sltiu(psp_v0, psp_v0, 32);                // v0 = (amt8 < 32)
        emit_movz(dst, psp_v1, psp_v0);                // amt8 >= 32 -> sign fill
    },

    [](psp_gpr_t src, psp_gpr_t dst, opcode &op) -> void { // PRE_OP_ROR_REG
        // ARM: amount = Rs & 0xFF; rotate uses amount & 31. MIPS rotrv masks to
        // 5 bits, which matches ARM exactly (ROR by a multiple of 32 = no-op).
        int32_t regs[1] = {op.imm};
        regman.get(1, regs);
        emit_rotrv(dst, src, (psp_gpr_t)regs[0]);
    },
};

#define cpu (&ARMPROC)

template <int PROCNUM>
static u16 FASTCALL _LDRH(u32 adr)
{
    return READ16(cpu->mem_if->data, adr);
}

template <int PROCNUM>
static void FASTCALL _STRH(u32 regs, u32 imm)
{
    u32 adr = (u32)cpu->R[regs >> 8] + imm;
    u32 data = (u32)cpu->R[regs & 0xFF];
    WRITE16(cpu->mem_if->data, adr, data);
}

void emit_li(u32 reg, u32 data, u32 sz)
{
    if (data == 0 && sz == 0) {           // FAST PATH
        emit_move(reg, psp_zero);
        return;
    }
    if (is_u16(data) && sz != 2)
        emit_ori(reg, psp_zero, data & 0xFFFF);
    else if (is_s16(data) && sz != 2)
        emit_movi(reg, data & 0xFFFF);
    else {
        emit_lui(reg, data >> 16);
        if ((sz == 2) || (data & 0xFFFF))
            emit_ori(reg, reg, data & 0xFFFF);
    }
}

// load upper address
inline u32 emit_lua(u32 reg, u32 data)
{
    u32 hi = data >> 16;
    u32 lo = data & 0xFFFF;

    if (lo & 0x8000)
    {
        hi++;
        lo = data - (hi << 16);
    }

    emit_lui(reg, u16(hi));
    return lo;
}

void generate_condition_check(int cond)
{
    static const uint8 cond_bit[] = {0x40, 0x40, 0x20, 0x20, 0x80, 0x80, 0x10, 0x10};

    if (cond < 8)
    {
        emit_andi(psp_s4, psp_gp, cond_bit[cond]);
        return;
    }

    switch (cond)
    {

    case 8:
    case 9:
        emit_ext(psp_a1, psp_gp, 6, 5);
        emit_xori(psp_s4, psp_a1, 0b01);
        break;

    case 10:
    case 11:

        emit_ext(psp_a1, psp_gp, 7, 7);
        emit_ext(psp_at, psp_gp, 4, 4);

        emit_xor(psp_s4, psp_a1, psp_at);
        break;

    case 12:
    case 13:

        emit_ext(psp_a1, psp_gp, 7, 6);
        emit_ext(psp_at, psp_gp, 4, 3);

        emit_andi(psp_at, psp_at, 0b10);
        emit_xor(psp_s4, psp_a1, psp_at);
        break;
    }
}

uint32 emit_Halfbranch(int cond, bool generate_condition = true)
{
    if (generate_condition)
        generate_condition_check(cond);

    emit_nop();
    emit_nop();
    return emit_getPointAdr() - 8;
}

void CompleteCondition(u32 cond, u32 _addr, u32 label)
{
    if (cond < 8)
    {
        if (cond & 1)
            emit_bnelC(psp_s4, psp_zero, label, _addr);
        else
            emit_beqlC(psp_s4, psp_zero, label, _addr);
        return;
    }

    if (cond & 1)
        emit_beqlC(psp_s4, psp_zero, label, _addr);
    else
        emit_bnelC(psp_s4, psp_zero, label, _addr);
}
bool saved = false;

static int prefetch_skip = 1;
void emit_prefetch_reset() { prefetch_skip = 1; }

void emit_prefetch(const u8 isize, bool updateR15, bool store)
{

    if (updateR15 || store)
    {

        emit_addiu(psp_fp, psp_fp, isize * prefetch_skip);

        if (store)
            emit_sw(psp_fp, RCPU, _next_instr);

        saved = false;

        emit_addiu(psp_at, psp_fp, isize);
        if (store)
            emit_sw(psp_at, RCPU, _R15);

        emit_prefetch_reset();
    }
    else
        prefetch_skip++;
}

INLINE void emit_bic(u32 dst, u32 a0, u32 a1)
{
    emit_not(a1, a1);
    emit_and(dst, a0, a1);
}

INLINE void emit_bici(u32 dst, u32 a0, u32 a1)
{
    emit_andi(dst, a0, ~a1);
}

#define END_OP(_rd)                               \
    {                                             \
        if (!op.dead_rd)                          \
            regman.mark_dirty((psp_gpr_t)_rd);    \
        if (!rd_allocated && !op.dead_rd)         \
            regman.flush((psp_gpr_t)_rd);         \
    }

#define END_OP_CHKR15(_rd)                                 \
    {                                                      \
        if (!op.dead_rd)                                   \
            regman.mark_dirty((psp_gpr_t)_rd);             \
        if (op.rd == 15)                                   \
        {                                                  \
            op.check_condition = false;                    \
            conditional(emit_sw(_rd, RCPU, _next_instr);); \
        }                                                  \
    }

#define HANDLE_CONDITIONAL(branchless_code, branch_code) \
    do                                                   \
    {                                                    \
        if (op.rd != 15)                                 \
        {                                                \
            conditional_branchless(regs[0], psp_at,      \
                                   {branchless_code});   \
            END_OP_CHKR15(regs[0]);                      \
        }                                                \
        else                                             \
        {                                                \
            conditional(                                 \
                branch_code                              \
                    END_OP_CHKR15(regs[0]););            \
        }                                                \
    } while (0)

#define HANDLE_CONDITIONAL_NR15(branchless_code, branch_code) \
    do                                                        \
    {                                                         \
        if ((rd_allocated) && (op).condition != -1)           \
        {                                                     \
            conditional_branchless(regs[0], psp_at,           \
                                   {branchless_code});        \
            END_OP(regs[0]);                                  \
        }                                                     \
        else                                                  \
        {                                                     \
            conditional(                                      \
                branch_code                                   \
                    END_OP(regs[0]););                        \
        }                                                     \
    } while (0)

#define gen_nativeOP(opType, n_op, n_op_imm, sign)                                                          \
    template <bool imm, bool rev>                                                                           \
    void arm_##opType(opcode &op)                                                                           \
    {                                                                                                       \
        int32_t regs[3] = {(op.condition != -1) ? op.rd : (op.rd | 0x10), op.rs1, op.rs2};                  \
        const int reg_count = imm ? 2 : 3;                                                                  \
        regman.get(reg_count, regs);                                                                        \
        const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];                           \
        if (imm)                                                                                            \
        {                                                                                                   \
            if (!rev && is_##sign##16(op.imm))                                                              \
            {                                                                                               \
                conditional_branchless(regs[0], dst,                                                        \
                                       {                                                                    \
                                           emit_##n_op_imm(dst, regs[1], op.imm);                           \
                                       });                                                                  \
            }                                                                                               \
            else                                                                                            \
            {                                                                                               \
                conditional_branchless(regs[0], dst,                                                        \
                                       {                                                                    \
                                           emit_li(psp_at, op.imm);                                         \
                                           if (!rev)                                                        \
                                               emit_##n_op(dst, regs[1], psp_at);                           \
                                           else                                                             \
                                               emit_##n_op(dst, psp_at, regs[1]);                           \
                                       });                                                                  \
            }                                                                                               \
        }                                                                                                   \
        else                                                                                                \
        {                                                                                                   \
            conditional_branchless(regs[0], dst,                                                            \
                                   {                                                                       \
                                       arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[2], psp_at, op); \
                                       if (!rev)                                                            \
                                           emit_##n_op(dst, regs[1], psp_at);                               \
                                       else                                                                 \
                                           emit_##n_op(dst, psp_at, regs[1]);                               \
                                   });                                                                      \
        }                                                                                                   \
        END_OP_CHKR15(regs[0]);                                                                             \
    }

gen_nativeOP(and, and, andi, u);
gen_nativeOP(or, or, ori, u);
gen_nativeOP(xor, xor, xori, u);
gen_nativeOP(add, addu, addiu, s);
gen_nativeOP(sub, subu, subiu, s);
gen_nativeOP(bic, bic, bici, u);

// Apply an IMM-shift to a compile-time constant.
// Returns false for RRX (shift=0 ROR), which needs the carry flag at runtime.
static bool apply_const_shift(opType preOp, uint32_t src, uint32_t shift, uint32_t &out)
{
    switch (preOp) {
    case PRE_OP_LSL_IMM:
        out = src << shift;
        return true;
    case PRE_OP_LSR_IMM:
        out = shift ? (src >> shift) : 0u;
        return true;
    case PRE_OP_ASR_IMM:
        out = (uint32_t)((int32_t)src >> (shift ? shift : 31));
        return true;
    case PRE_OP_ROR_IMM:
        if (!shift) return false; // RRX — depends on carry
        out = (src >> shift) | (src << (32u - shift));
        return true;
    default:
        return false;
    }
}

// Evaluate a binary IR opcode with two known constants.
// lhs = consts[rs1], rhs = op.imm.
// Returns false for ops whose result can't be folded (flag-setters, mem, etc.).
static bool eval_const_binop(op _op, uint32_t lhs, uint32_t rhs, uint32_t &out)
{
    switch (_op) {
    case OP_ADD: out = lhs + rhs;  return true;
    case OP_SUB: out = lhs - rhs;  return true;
    case OP_RSB: out = rhs - lhs;  return true; // RSB: rd = imm - rs1
    case OP_AND: out = lhs & rhs;  return true;
    case OP_ORR: out = lhs | rhs;  return true;
    case OP_EOR: out = lhs ^ rhs;  return true;
    case OP_BIC: out = lhs & ~rhs; return true;
    default:     return false;
    }
}

// Do you want speed? call this function if you want to see some black magic :D

void block::optimize_basicblock()
{
    // === Pass 1: Condition merging ===
    // Consecutive ops with the same condition can skip re-evaluating the flags.
    {
        opcode *prev = nullptr;
        for (opcode &op : opcodes) {
            if (prev && prev->_op != OP_ITP && op.condition == prev->condition)
                op.check_condition = false;
            prev = &op;
        }
    }

    // === Pass 2: Constant propagation ===
    // Forward pass: track registers whose values are compile-time constants and
    // fold arithmetic/shift expressions into immediate MOVs where possible.
    // Toggle: set to 0 to disable. Steps A/B are now guarded to ALU ops only —
    // previously they rewrote memory ops, dropping GX-FIFO stores (3D vanished).
    #define JIT_ENABLE_CONSTPROP 1
    if (JIT_ENABLE_CONSTPROP)
    {
        struct ConstVal { bool known; uint32_t val; };
        ConstVal consts[16] = {};

        for (opcode &op : opcodes)
        {
            // ITP is an interpreted instruction — it can read/write any register.
            if (op._op == OP_ITP) {
                memset(consts, 0, sizeof(consts));
                continue;
            }

            // LDM defines every register in its list; STM only its writeback base.
            // Invalidate all written regs so later folds don't use stale constants.
            if (op._op == OP_LDM || op._op == OP_STM) {
                if (op._op == OP_LDM) {
                    const uint16_t rlist = op.bytes & 0xFFFF;
                    for (int r = 0; r < 16; r++)
                        if (rlist & (1u << r)) consts[r].known = false;
                }
                if (op.rs1 >= 0 && op.rs1 < 16) consts[op.rs1].known = false; // writeback base
                continue;
            }

            const bool unconditional = (op.condition == (uint32_t)-1);

            // Folding (Steps A/B) is only valid for pure ALU ops. For memory ops
            // (OP_LDR/OP_STR/OP_LDM/...) preOpType encodes the ADDRESSING MODE and
            // op.imm is the offset, NOT an ALU operand — rewriting them corrupts
            // the access (and Step B would turn a store into a MOV, dropping it:
            // that silently kills GX-FIFO / 3D stores). ALU opcodes are the range
            // (OP_ITP, OP_LDR); compare/etc. (>= OP_CMP) also excluded.
            const bool is_alu_op = (op._op > OP_ITP && op._op < OP_LDR);

            // Step A: rs2 is const + IMM shift → fold the shift into an immediate.
            // e.g. "ADD rd, rn, rm LSL #n" → "ADD rd, rn, #(rm_val << n)"
            if (is_alu_op &&
                (op.preOpType == PRE_OP_LSL_IMM || op.preOpType == PRE_OP_LSR_IMM ||
                 op.preOpType == PRE_OP_ASR_IMM || op.preOpType == PRE_OP_ROR_IMM) &&
                op.rs2 >= 0 && op.rs2 < 16 && consts[op.rs2].known)
            {
                uint32_t shifted;
                if (apply_const_shift(op.preOpType, consts[op.rs2].val, (uint32_t)op.imm, shifted)) {
                    op.preOpType = PRE_OP_IMM;
                    op.imm       = (int32_t)shifted;
                    op.rs2       = -1;
                }
            }

            // Step B: rs1 is const + PRE_OP_IMM → fold to a pure MOV #imm.
            // e.g. "ADD rd, rn, #k" where rn==const → "MOV rd, #(rn_val + k)"
            // Only safe for unconditional ALU ops (never memory ops).
            if (is_alu_op &&
                unconditional &&
                op.preOpType == PRE_OP_IMM &&
                op._op != OP_MOV &&
                op.rs1 >= 0 && op.rs1 < 16 && consts[op.rs1].known)
            {
                uint32_t folded;
                if (eval_const_binop(op._op, consts[op.rs1].val, (uint32_t)op.imm, folded)) {
                    op._op  = OP_MOV;
                    op.imm  = (int32_t)folded;
                    op.rs1  = -1;
                    // preOpType stays PRE_OP_IMM — the emitter emits "li rd, folded"
                }
            }

            // Step C: update const table for the destination register.
            if (op.rd >= 0 && op.rd < 15) { // never track r15 (PC)
                consts[op.rd].known = false;  // pessimistically invalidate first

                // Only a plain unconditional MOV #imm produces a known compile-time value.
                if (unconditional && op._op == OP_MOV && op.preOpType == PRE_OP_IMM) {
                    consts[op.rd] = {true, (uint32_t)op.imm};
                }
            }
        }
    }

    // === Pass 3: Dead store elimination ===
    // Backward liveness pass: if rd is overwritten before any subsequent read,
    // the writeback to RCPU is dead — suppress mark_dirty so flush emits no sw.
    // Conservative: all regs are live at block exit (next block may read anything).
    // We can only catch intra-block kills (reg written twice without a read between).
    {
        uint16_t live = 0xFFFF; // bits 0-15: live ARM registers

        for (int i = (int)opcodes.size() - 1; i >= 0; --i) {
            opcode &op = opcodes[i];

            if (op._op == OP_ITP) {
                live = 0xFFFF; // interpreted instr: conservatively uses everything
                continue;
            }

            if (op._op == OP_LDM || op._op == OP_STM) {
                const uint16_t rlist = op.bytes & 0xFFFF;
                if (op._op == OP_LDM) live &= ~rlist;   // loaded regs are defined
                else                  live |= rlist;     // stored regs are used
                if (op.rs1 >= 0 && op.rs1 < 16) live |= (1u << op.rs1); // base
                continue;
            }

            const bool unconditional = (op.condition == (uint32_t)-1);

            // Only pure ALU ops (no memory side-effects) can be dead-stored.
            const bool is_alu = (op._op > OP_ITP && op._op < OP_LDR);

            if (is_alu && unconditional && op.rd < 15 && op.rd >= 0) {
                if (!(live & (1u << op.rd))) {
                    op.dead_rd = true; // nobody reads this value before it's overwritten
                }
                // Definition kills liveness regardless of whether it's dead.
                live &= ~(1u << op.rd);
            }

            // Mark sources as live.
            if (op.rs1 >= 0 && op.rs1 < 16) live |= (1u << op.rs1);
            if (op.rs2 >= 0 && op.rs2 < 16) live |= (1u << op.rs2);
            // REG-shift and MLA: shift-amount / accumulator register lives in imm field.
            if (op.preOpType == PRE_OP_LSL_REG || op.preOpType == PRE_OP_LSR_REG ||
                op.preOpType == PRE_OP_ASR_REG || op.preOpType == PRE_OP_ROR_REG ||
                op._op == OP_MLA || op._op == OP_UMLA) {
                if (op.imm >= 0 && op.imm < 16) live |= (1u << op.imm);
            }
        }
    }

    return;
}

void block::optimize_basicblockThumb()
{
    opcode *prev_op = 0;
    opcode *prev_ITP = 0;

    bool savedN = false;
    bool savedZ = false;
    bool savedC = false;
    bool savedV = false;

    for (int i = opcodes.size() - 1; i >= 0; --i)
    {
        opcode &op = opcodes[i];

        if (op.extra_flags & EXTFL_NOFLAGS)
            continue;

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

            if (!savedC)
            {
                savedC = true;
            }
            else
                op.saveC = false;

            if (!savedN)
            {
                savedN = true;
            }
            else
                op.saveN = false;

            if (!savedZ)
            {
                savedZ = true;
            }
            else
                op.saveZ = false;

            break;

        case OP_SUB:
        case OP_CMP:
            if (!savedN)
            {
                savedN = true;
            }
            else
                op.saveN = false;

            if (!savedZ)
            {
                savedZ = true;
            }
            else
                op.saveZ = false;

            if (!savedC)
            {
                savedC = true;
            }
            else
                op.saveC = false;

            if (!savedV)
            {
                savedV = true;
            }
            else
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

    // Dead store elimination (same pass as ARM mode).
    {
        uint16_t live = 0xFFFF;

        for (int i = (int)opcodes.size() - 1; i >= 0; --i) {
            opcode &op = opcodes[i];

            if (op._op == OP_ITP) { live = 0xFFFF; continue; }

            if (op._op == OP_LDM || op._op == OP_STM) {
                const uint16_t rlist = op.bytes & 0xFFFF;
                if (op._op == OP_LDM) live &= ~rlist;   // loaded regs are defined
                else                  live |= rlist;     // stored regs are used
                if (op.rs1 >= 0 && op.rs1 < 16) live |= (1u << op.rs1); // base
                continue;
            }

            const bool unconditional = (op.condition == (uint32_t)-1);
            const bool is_alu = (op._op > OP_ITP && op._op < OP_LDR);

            if (is_alu && unconditional && op.rd < 15 && op.rd >= 0) {
                if (!(live & (1u << op.rd)))
                    op.dead_rd = true;
                live &= ~(1u << op.rd);
            }

            if (op.rs1 >= 0 && op.rs1 < 16) live |= (1u << op.rs1);
            if (op.rs2 >= 0 && op.rs2 < 16) live |= (1u << op.rs2);
            if (op.preOpType == PRE_OP_LSL_REG || op.preOpType == PRE_OP_LSR_REG ||
                op.preOpType == PRE_OP_ASR_REG || op.preOpType == PRE_OP_ROR_REG ||
                op._op == OP_MLA || op._op == OP_UMLA) {
                if (op.imm >= 0 && op.imm < 16) live |= (1u << op.imm);
            }
        }
    }
}

extern "C" void set_sub_flags();
extern "C" void set_and_flags();
extern "C" void set_op_logic_flags();

#define cpu (&ARMPROC)

void lastBeforeCrash(int a0, int a1)
{
    printf("0x%x\n", a0);
}

void EmitReadFunction(u32 addr)
{
    unsigned o_ra;
    extern u8 *CodeCache;

    // Execute the patch at the end (overwrite ra addr inside the sp)
    asm volatile("addiu $2, $31, -16");
    asm volatile("sw $2, 0x14($29)");

    // Get the current ra
    asm volatile("sw $31, %0" : "=m"(o_ra));

    u32 _ptr = emit_Set((o_ra - 16) - 0x8400000);

    printf("EmitReadFunction: 0x%x 0x%x\n", o_ra, 0x8400000);

    if ((addr & (~0x3FFF)) == MMU.DTCMRegion)
    {
        emit_li(psp_t1, (u32)MMU.ARM9_DTCM);
        emit_andi(psp_a0, psp_a0, 0x3FFC);
    }
    else
    {
        emit_li(psp_t1, (u32)MMU.MAIN_MEM);
        emit_ins(psp_a0, psp_zero, 31, 22);
    }

    emit_addu(psp_a0, psp_t1, psp_a0);
    emit_lw(psp_v0, psp_a0, 0);

    emit_Set(_ptr);

    // make_address_range_executable(o_ra - 8, o_ra - 4);
    u32 addr_start = o_ra - 16;
    __builtin_allegrex_cache(0x1a, addr_start);
    __builtin_allegrex_cache(0x08, addr_start);
}

#define NDS_ReschedulePtr (*(bool *)(0x0010080))
template <bool execute>
u32 jump_to_linked_bc(u32 off)
{
    // check if the addr is already compiled
    u32 addr = NDS_ARM9.R[15] + off;

    NDS_ARM9.R[15] += off;
    NDS_ARM9.R[15] &= (0xFFFFFFFC | (NDS_ARM9.CPSR.bits.T << 1));
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];

    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(NDS_ARM9.next_instruction, ARM9);

    if (code_block && NDS_ReschedulePtr == 0)
    {
        // printf("Fast jump\n");
        const u32 cycles = code_block();
        return cycles;
    }

    // compile the block
    // printf("Compile block\n");
    // const u32 cycles = arm_jit_compile<ARM9>();
    return 3;
}

template <bool execute>
u32 jump_to_linked_blc(u32 off)
{
    // check if the addr is already compiled
    u32 addr = NDS_ARM9.R[15] + off;

    NDS_ARM9.R[14] = NDS_ARM9.next_instruction;
    NDS_ARM9.R[15] += off;
    NDS_ARM9.R[15] &= (0xFFFFFFFC | (NDS_ARM9.CPSR.bits.T << 1));
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];

    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(NDS_ARM9.next_instruction, ARM9);

    if (code_block && NDS_ReschedulePtr == 0)
    {
        // printf("Fast jump\n");
        const u32 cycles = code_block();
        return cycles;
    }

    // compile the block
    // printf("Compile block\n");
    // const u32 cycles = arm_jit_compile<ARM9>();
    return 3;
}

template <bool execute>
u32 jump_to_linked(u32 addr)
{
    // check if the addr is already compiled

    NDS_ARM9.CPSR.bits.T = BIT0(addr);
    NDS_ARM9.R[15] = addr & (0xFFFFFFFC | (NDS_ARM9.CPSR.bits.T << 1));
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];

    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(NDS_ARM9.next_instruction, ARM9);

    if (NDS_ARM9.CPSR.bits.T == BIT0(addr) && code_block && NDS_ReschedulePtr == 0)
    {
        // printf("Fast jump\n");
        const u32 cycles = code_block();
        return cycles;
    }

    // compile the block
    // printf("Compile block\n");
    // const u32 cycles = arm_jit_compile<ARM9>();
    return 3;
}

template <bool execute>
u32 jump_to_linked_br(u32 addr)
{
    // check if the addr is already compiled
    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(addr, ARM9);

    /*if (NDS_ARM9.CPSR.bits.T == BIT0(addr) && code_block){
        //printf("Fast jump\n");
        const u32 cycles = code_block();
        return cycles;
    }*/

    NDS_ARM9.R[14] = NDS_ARM9.next_instruction;
    NDS_ARM9.CPSR.bits.T = BIT0(addr);
    NDS_ARM9.R[15] = addr & (0xFFFFFFFC | (NDS_ARM9.CPSR.bits.T << 1));
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];
    return 3;
}

u32 jump_to_linked_uncod_thumb(u32 addr)
{
    // check if the addr is already compiled

    NDS_ARM9.R[15] += addr;
    NDS_ARM9.next_instruction = NDS_ARM9.R[15];

    ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(NDS_ARM9.next_instruction, ARM9);

    if (code_block && NDS_ReschedulePtr == 0)
    {
        // printf("Fast jump thumb\n");
        const u32 cycles = code_block();
        return cycles;
    }
    return 1;
}

u32 _read32(u32 addr, u32 addr_mem)
{
    if ((addr & (~0x3FFF)) == MMU.DTCMRegion)
        return *(u32 *)(MMU.ARM9_DTCM + (addr & 0x3FFC));

    return *(u32 *)(MMU.MAIN_MEM + addr_mem);
}

void _write16(u32 addr, u16 val)
{
    if ((addr & (~0x3FFF)) == MMU.DTCMRegion)
    {
        T1WriteWord(MMU.ARM9_DTCM, addr & 0x3FFE, (u16)val);
        return;
    }
    const WritePageEntry &e = mmu_write_lut_arm9[addr >> 24];
    if (e.base)
    {
        if (e.flags & WPE_JIT_INVAL)
            JIT_COMPILED_FUNC_KNOWNBANK(addr, MAIN_MEM, _MMU_MAIN_MEM_MASK16, 0) = 0;
        T1WriteWord(e.base, addr & (e.mask & ~1u), val);
        return;
    }
    _MMU_ARM9_write16(addr, val);
}

void _write32(u32 addr, u32 val)
{
    if ((addr & (~0x3FFF)) == MMU.DTCMRegion)
    {
        T1WriteLong(MMU.ARM9_DTCM, addr & 0x3FFC, val);
        return;
    }
    const WritePageEntry &e = mmu_write_lut_arm9[addr >> 24];
    if (e.base)
    {
        if (e.flags & WPE_JIT_INVAL)
        {
            JIT_COMPILED_FUNC_KNOWNBANK(addr, MAIN_MEM, _MMU_MAIN_MEM_MASK32, 0) = 0;
            JIT_COMPILED_FUNC_KNOWNBANK(addr, MAIN_MEM, _MMU_MAIN_MEM_MASK32, 1) = 0;
        }
        T1WriteLong(e.base, addr & (e.mask & ~3u), val);
        return;
    }
    _MMU_ARM9_write32(addr, val);
}

#include "FIFO.h"
#include "NDSSystem.h"

void write_3D_cmd(u32 addr, u32 data)
{
    extern void gfx3d_sendCommand(u32 cmd, u32 param);

    /*case 0x400044:
    case 0x400045:
    case 0x400046:
    case 0x400047:
    case 0x400048:
    case 0x400049:
    case 0x40004A:
    case 0x40004B:
    case 0x40004C:
    case 0x40004D:
    case 0x40004E:
    case 0x40004F:
    case 0x400050:
    case 0x400051:
    case 0x400052:
    case 0x400053:
    case 0x400054:
    case 0x400055:
    case 0x400056:
    case 0x400057:
    case 0x400058:
    case 0x400059:
    case 0x40005A:
    case 0x40005B:
    case 0x40005C:		// Individual Commands*/
    if (gxFIFO.size > 254)
        nds.freezeBus |= 1;

    ((u32 *)(MMU.MMU_MEM[ARMCPU_ARM9][0x40]))[(addr & 0xFFF) >> 2] = data;
    gfx3d_sendCommand(addr, data);
}

void write_3D_fifo(u32 addr, u32 data)
{
    extern void gfx3d_sendCommandToFIFO(u32 val);
    ((u32 *)(MMU.MMU_MEM[ARMCPU_ARM9][0x40]))[addr] = data;
    gfx3d_sendCommandToFIFO(data);
}

template <uint32_t size>
void write_dma(u32 val, u32 i, s32 shift_op, u32 type)
{

    extern u32 get_addr(u32 addr, s32 shift_op, u32 type, u32 i);

    u32 adr = get_addr(_ARMPROC.R[REG_POS(i, 16)], shift_op, type, i);
    MMU_new.write_dma<ARM9, size>(static_cast<DmaRegister>(adr), val);
}

void arm_halt_hack()
{
    static u32 prevIE = 0;
    if (MMU.reg_IE[0] != prevIE) {
        printf("WFI IE changed: %08X -> %08X (IF=%08X)\n", prevIE, MMU.reg_IE[0], MMU.gen_IF<0>());
        prevIE = MMU.reg_IE[0];
    }
    NDS_ARM9.CPSR.bits.I = 0;
	NDS_ARM9.freeze |= CPU_FREEZE_WAIT_IRQ;
	NDS_Reschedule();
}

template <int PROCNUM>
void emitARMOP(opcode &op, const bool last_op)
{

    const bool rd_allocated = regman.is_mapped(op.rd);

    // printf("OP: %d\n", op._op);

    switch (op._op)
    {

    case OP_3D_CMD:
    {
        int32_t regs[1] = {op.rs1};

        conditional(

            regman.get(1, regs);

            emit_li(psp_a0, op.imm);
            emit_jal(write_3D_cmd);
            emit_move(psp_a1, regs[0]););
        break;
    }

    case OP_3D_FIFO:
    {
        int32_t regs[1] = {op.rs1};

        conditional(

            regman.get(1, regs);

            emit_movi(psp_a0, ((op.imm & 0xFFF) >> 2));
            emit_jal(write_3D_fifo);
            emit_move(psp_a1, regs[0]););
        break;
    }

    case OP_DMA:
    {

        int32_t regs[] = {op.rs1};

        printf("DMA: %d\n", op.imm);

        conditional(

            regman.get(1, regs);

            emit_li(psp_a1, op.op_pc);
            emit_li(psp_a2, op.imm);
            emit_li(psp_a3, op.preOpType);

            {
                emit_jal((write_dma<32>));
            }

            emit_move(psp_a0, regs[0]););

        break;
    }

    case OP_ITP:
    {
        if (last_op)
        {
            check_flags();
        }

        conditional(

            if (!last_op) {
                check_flags();
            }

            emit_li(psp_a0, op.rs1);

            uint32_t optmizeDelaySlot = emit_SlideDelay();

            emit_jal(arm_instructions_set[ARM9][INSTRUCTION_INDEX(op.rs1)]);
            emit_Write32(optmizeDelaySlot);

            if (!last_op) load_flags();)

            intr_instr++;
    }
    break;
    case OP_AND:
    {

        if (op.preOpType == PRE_OP_IMM)
        {
            arm_and<true, false>(op);
        }
        else
        {
            // printf("IMM: 0x%x\n", emit_getCurrAdr());
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

    case OP_ORR:
    {

        if (op.preOpType == PRE_OP_IMM)
        {
            arm_or<true, false>(op);
        }
        else
        {
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
        if (op.preOpType == PRE_OP_IMM)
        {
            arm_add<true, false>(op);
        }
        else
        {
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
        if (op.preOpType == PRE_OP_IMM)
        {
            arm_sub<true, false>(op);
        }
        else
        {
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
        int32_t regs[3] = {op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2};

        HANDLE_CONDITIONAL_NR15(
            {
                regman.get(3, regs);

                emit_mult(regs[1], regs[2]);
                emit_mflo(psp_at);
            },
            {
                regman.get(3, regs);

                emit_mult(regs[1], regs[2]);
                emit_mflo(regs[0]);
            });
        break;
    }

    case OP_MLA:
    {
        int32_t regs[4] = {op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2, op.imm};

        HANDLE_CONDITIONAL_NR15(
            {
                regman.get(4, regs);

                emit_mult(regs[1], regs[2]);
                emit_mflo(psp_at);
                emit_addu(psp_at, psp_at, regs[3]);
            },
            {
                regman.get(4, regs);

                emit_mult(regs[1], regs[2]);
                emit_mflo(psp_at);
                emit_addu(regs[0], psp_at, regs[3]);
            });
        break;
    }

    case OP_UMUL:
    {
        int32_t regs[4] = {op.condition != -1 ? op.rd : (op.rd | 0x10), op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2};

        HANDLE_CONDITIONAL_NR15(
            {
                regman.get(4, regs);

                emit_multu(regs[2], regs[3]);
                emit_mflo(psp_at);
                emit_mfhi(regs[1]);
                END_OP(regs[1]);
            },
            {
                regman.get(4, regs);

                emit_multu(regs[2], regs[3]);
                emit_mflo(regs[0]);
                emit_mfhi(regs[1]);
                END_OP(regs[1]);
            });
        break;
    }

    case OP_UMLA:
    {
        int32_t regs[4] = {op.condition != -1 ? op.rd : (op.rd | 0x10), op.rs1, op.rs2, op.imm};

        HANDLE_CONDITIONAL_NR15(
            {
                regman.get(4, regs);

                emit_multu(regs[1], regs[2]);
                emit_mflo(psp_at);
                emit_addu(psp_at, psp_at, regs[3]);
            },
            {
                regman.get(4, regs);

                emit_multu(regs[1], regs[2]);
                emit_mflo(psp_at);
                emit_addu(regs[0], psp_at, regs[3]);
            });
        break;
    }

    case OP_CLZ:
    {
        int32_t regs[2] = {op.rd, op.rs1};
        regman.get(2, regs);

        const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];

        conditional_branchless(regs[0], dst, {
            emit_clz(dst, regs[1]);
        });

        regman.mark_dirty((psp_gpr_t)regs[0]);
        break;
    }

    case OP_SWI:
    {
        conditional(
            emit_jal(cpu->swi_tab[op.rs1]);

            if (flag_dirty) {
                store_flags();
                flag_dirty = false;
            } else emit_nop();)
        break;
    }

    case OP_MOV:
    case OP_MVN:
    {
        int32_t regs[2] = {op.condition != -1 ? op.rd : op.rd | 0x10, op.rs2};

        if (op.preOpType == PRE_OP_IMM)
        {
            regman.get(1, regs);
            const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];

            conditional_branchless(regs[0], ((op.imm == 0 && op.condition != -1) ? psp_zero : dst),
                                   {
                                       if (op.imm != 0)
                                           emit_li(dst, op.imm);
                                       else /*if (op.imm == 0 && op.condition == -1)*/
                                           emit_move(dst, psp_zero);
                                   });
        }
        else
        {
            regman.get(2, regs);
            const psp_gpr_t dst = (op.condition != -1) ? psp_at : (psp_gpr_t)regs[0];

            conditional_branchless(regs[0], dst,
                                   {
                                       arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[1], dst, op);

                                       if (op._op == OP_MVN)
                                           emit_not(dst, dst);
                                   });
        }
        END_OP_CHKR15(regs[0])
        break;
    }

    case OP_BXRC:
    {
        regman.flush_all(false);
        regman.reset();

        check_flags()

            emit_movi(psp_v0, 1);
        conditional(
            emit_jal(jump_to_linked_br<true>);
            loadReg(psp_a0, op.rs1);) break;
    }

    case OP_BC:
    {
        regman.flush_all(false);
        regman.reset();

        check_flags()

            emit_movi(psp_v0, 1);
        conditional(
            emit_li(psp_a0, op.imm);
            u32 op = emit_SlideDelay();
            emit_jal(jump_to_linked_bc<true>);
            emit_Write32(op);)
    }
    break;

    case OP_BLC:
    {
        regman.flush_all(false);
        regman.reset();

        check_flags()

        conditional(
            // R[14] = next_instruction (return address)
            emit_lw(psp_at, RCPU, _next_instr);
            emit_sw(psp_at, RCPU, _reg(14));
            // next_instruction = R[15] + off (branch target); ARM targets are always word-aligned
            emit_lw(psp_at, RCPU, _R15);
            emit_li(psp_a0, op.imm);
            emit_addu(psp_a0, psp_a0, psp_at);
            emit_sw(psp_a0, RCPU, _R15);
            emit_sw(psp_a0, RCPU, _next_instr);)
    }
    break;

    case OP_BXC:
    {
        regman.flush_all(false);
        regman.reset();

        check_flags()

            // printf("0x%x, %d\n", (u32)emit_getCurrAdr(), op.rs1);

            emit_movi(psp_v0, 1);
        conditional(
            emit_jal(jump_to_linked<true>);
            loadReg(psp_a0, op.rs1);)
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
    }
    break;

    case OP_STR:
    case OP_STRH:
    {
        int32_t regs[3] = {op.rd, op.rs1, op.rs2};

        regman.flush_all(true);

        check_flags()

            conditional(
                regman.get(3, regs);

                const int special_type = op.preOpType >> 16;
                const bool is_special_type = (special_type == PRE_OP_LSL_IMM || special_type == PRE_OP_LSR_IMM ||
                                              special_type == PRE_OP_ASR_IMM || special_type == PRE_OP_ROR_IMM);
                const int type = op.preOpType & 0xff;

                const bool positive = op.imm >= 0;

                if (is_special_type) {
                    const int idx = getTypeIdx((opType)special_type);

                    op.imm = op.imm < 0 ? -op.imm : op.imm;

                    if (idx >= 0)
                        arm_preop[idx]((psp_gpr_t)regs[2], psp_t0, op);
                    else
                        printf("STR not encoded correctly: %d\n", idx);
                    // printf("Addr: %x\n", emit_getCurrAdr());
                    // printf("STR not encoded correctly: %d\n", idx);
                }

                if (type == PRE_OP_IMM_PRE_P || type == PRE_OP_IMM_PRE_M) {
                    if (!is_special_type)
                        emit_addiu(psp_a0, regs[0], op.imm);
                    else
                    {
                        if (positive)
                            emit_addu(psp_a0, regs[0], psp_t0);
                        else
                            emit_subu(psp_a0, regs[0], psp_t0);
                    }

                    storeReg(psp_a0, op.rd);
                } else if (type == PRE_OP_IMM_POST_P || type == PRE_OP_IMM_POST_M) {
                    emit_move(psp_a0, regs[0]);

                    if (!is_special_type)
                        emit_addiu(regs[0], regs[0], op.imm);
                    else
                    {
                        if (positive)
                            emit_addu(regs[0], regs[0], psp_t0);
                        else
                            emit_subu(regs[0], regs[0], psp_t0);
                    }

                    storeReg((psp_gpr_t)regs[0], op.rd);
                } else if (type == PRE_OP_IMM) {
                    if (is_special_type)
                    {
                        if (positive)
                            emit_addu(psp_a0, regs[0], psp_t0);
                        else
                            emit_subu(psp_a0, regs[0], psp_t0);
                    }
                    else
                    {
                        if (is_u16(op.imm))
                        {
                            emit_addiu(psp_a0, regs[0], op.imm);
                        }
                        else
                        {
                            emit_li(psp_a0, op.imm);
                            emit_addu(psp_a0, regs[0], psp_a0);
                        }
                    }
                }

                emit_move(psp_a1, regs[1]);

                if (OP_STRH == op._op) {
                    /*if (op.extra_flags & EXTFL_DIRECTMEMACCESS){
                        u32 op = emit_SlideDelay();
                        emit_jal(_write16);
                        emit_Write32(op);
                    }else*/
                    {
                        emit_jal(_write16);
                        emit_ins(psp_a0, psp_zero, 0, 0);
                    }
                } else {
                    /* if (op.extra_flags & EXTFL_DIRECTMEMACCESS){
                         u32 op = emit_SlideDelay();
                         emit_jal(_write32);
                         emit_Write32(op);
                     }else*/
                    {
                        emit_jal(_write32);
                        emit_ins(psp_a0, psp_zero, 1, 0);
                    }
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
        const int special_type = op.preOpType >> 16;
        const bool is_special_type = (special_type == PRE_OP_LSL_IMM || special_type == PRE_OP_LSR_IMM ||
                                      special_type == PRE_OP_ASR_IMM || special_type == PRE_OP_ROR_IMM);
        const int type = op.preOpType & 0xff;

        const bool positive = op.imm >= 0;

        int32_t regs[3] = {op.rd | 0x10, op.rs1, is_special_type ? op.rs2 : -1};

        bool skip = false;

        /*if (op.extra_flags & EXTFL_DIRECTMEMACCESS && op.condition == -1 && op._op == OP_LDR && !special_type) {
            skip = true;
        } else {
            regman.flush_all(true);
        }*/

        regman.flush_all(true);

        check_flags()

            conditional(
                regman.get(3, regs);

                if (is_special_type) {
                    const int idx = getTypeIdx((opType)special_type);

                    op.imm = op.imm < 0 ? -op.imm : op.imm;

                    if (idx >= 0)
                        arm_preop[idx]((psp_gpr_t)regs[2], psp_t0, op);
                    else
                        printf("LDR not encoded correctly: %d\n", idx);
                }

                if (type == PRE_OP_IMM) {
                    if (is_special_type)
                    {
                        if (positive)
                            emit_addu(psp_a0, regs[1], psp_t0);
                        else
                            emit_subu(psp_a0, regs[1], psp_t0);
                    }
                    else
                    {
                        if (is_u16(op.imm))
                        {
                            emit_addiu(psp_a0, regs[1], op.imm);
                        }
                        else
                        {
                            emit_li(psp_a0, op.imm);
                            emit_addu(psp_a0, regs[1], psp_a0);
                        }
                    }
                } else if (type == PRE_OP_IMM_PRE_P || type == PRE_OP_IMM_PRE_M) {
                    if (is_special_type)
                    {
                        if (positive)
                            emit_addu(psp_a0, regs[1], psp_t0);
                        else
                            emit_subu(psp_a0, regs[1], psp_t0);
                    }
                    else
                    {
                        emit_addiu(psp_a0, regs[1], op.imm);
                    }
                    storeReg(psp_a0, op.rs1);
                } else if (type == PRE_OP_IMM_POST_P || type == PRE_OP_IMM_POST_M) {
                    emit_move(psp_a0, regs[1]);

                    if (is_special_type)
                    {
                        if (positive)
                            emit_addu(psp_t1, psp_a0, psp_t0);
                        else
                            emit_subu(psp_t1, psp_a0, psp_t0);
                    }
                    else
                    {
                        emit_addiu(psp_t1, psp_a0, op.imm);
                    }

                    storeReg(psp_t1, op.rs1);
                }

                if (OP_LDR == op._op) {
                    if (op.extra_flags & EXTFL_DIRECTMEMACCESS)
                    {
                        // printf("DIRECT ACCEESS %x, %x, %x\n", MMU.ARM9_DTCM, MMU.MAIN_MEM, (u32)&MMU.DTCMRegion);
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
                    }
                    else
                    {
                        // printf("SLOW ACCEESS\n");

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

                    if (op._op == OP_LDRSH)
                        emit_seh(regs[0], psp_v0);
                    else
                        emit_move(regs[0], psp_v0);
                }

                regman.reset();

                if (op.condition == -1) {
                    regman.map(op.rd, (psp_gpr_t)regs[0]);
                    regman.mark_dirty((psp_gpr_t)regs[0]);
                } else storeReg((psp_gpr_t)regs[0], op.rd);)
    }
    break;

    case OP_LDM:
    case OP_STM:
    {
        // op.bytes = full ARM opcode. Decode addressing form here.
        const u32 insn   = op.bytes;
        const bool load  = (op._op == OP_LDM);
        const bool P     = (insn >> 24) & 1;   // pre/post
        const bool U     = (insn >> 23) & 1;   // up/down
        const bool W     = (insn >> 21) & 1;   // writeback
        const u32  rlist = insn & 0xFFFF;
        const u32  rn    = op.rs1;

        int n = 0;
        for (u32 b = 0; b < 16; b++)
            if (rlist & (1u << b)) n++;

        // psp_s5 holds the running effective address across the memory calls
        // (callee-saved, survives _read32/_write32). All NDS regs live in the
        // CPU struct here (flushed below), so we load/store them directly.
        regman.flush_all(false);
        regman.reset();

        check_flags()

        conditional(
            // base address into s5
            loadReg(psp_s5, rn);

            // Lowest register goes to lowest address. Compute address of the
            // lowest-numbered register's slot, then walk upward by +4.
            // IA: base ; IB: base+4 ; DA: base-(n-1)*4 ; DB: base-n*4
            int first_off;
            if (U)  first_off = P ? 4 : 0;
            else    first_off = P ? -(n * 4) : -((n - 1) * 4);

            if (first_off != 0)
                emit_addiu(psp_s5, psp_s5, first_off);

            // Writeback value computed up front (before any load can clobber rn).
            // n*4 <= 64, fits a signed 16-bit addiu immediate.
            if (W) {
                loadReg(psp_s7, rn);
                emit_addiu(psp_s7, psp_s7, U ? (n * 4) : -(n * 4));
                storeReg(psp_s7, rn);
            }

            int idx = 0;
            for (u32 b = 0; b < 16; b++) {
                if (!(rlist & (1u << b))) continue;

                if (load) {
                    // Mirror OP_LDR's proven read sequence (rotate is a no-op when aligned).
                    // Rotate amount must survive the call → use callee-saved s6.
                    emit_sll(psp_s6, psp_s5, 3);          // rotate amount = (addr&3)*8
                    emit_move(psp_a0, psp_s5);
                    emit_jal(_MMU_read32<PROCNUM>);
                    emit_ins(psp_a0, psp_zero, 1, 0);     // word-align addr (delay slot)
                    emit_rotrv(psp_v0, psp_v0, psp_s6);
                    storeReg(psp_v0, b);
                } else {
                    emit_move(psp_a0, psp_s5);
                    loadReg(psp_a1, b);
                    emit_jal(_write32);
                    emit_ins(psp_a0, psp_zero, 1, 0);     // word-align addr (delay slot)
                }

                idx++;
                if (idx < n)
                    emit_addiu(psp_s5, psp_s5, 4);
            }

            regman.reset();
        )
    }
    break;

    case OP_TST:
    {

        int32_t regs[2] = {op.rs1, op.rs2};

        conditional(
            regman.get(2, regs);

            if (op.preOpType == PRE_OP_IMM) {
                if (is_u16(op.imm))
                {
                    emit_andi(psp_v0, (psp_gpr_t)regs[0], op.imm);
                }
                else
                {
                    emit_li(psp_a0, op.imm);
                    emit_and(psp_v0, (psp_gpr_t)regs[0], psp_a0);
                }

                if ((op.rd >> 8) & 0xF)
                {
                    emit_ext(psp_t0, psp_a0, 31, 31);
                    emit_ins(psp_gp, psp_t0, _flag_C8, _flag_C8);
                }
            } else {
                arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[1], psp_t0, op);
                emit_and(psp_v0, (psp_gpr_t)regs[0], psp_t0);
            }

            emit_srl(psp_t0, psp_v0, 31);
            emit_ins(psp_gp, psp_t0, _flag_N8, _flag_N8);

            emit_sltiu(psp_t0, psp_v0, 1);
            emit_ins(psp_gp, psp_t0, _flag_Z8, _flag_Z8);

            // store_flags();

            set_flag_dirty();) 
            break;
    }

    case OP_CMN:
    {
        int32_t regs[2] = {op.rs1, op.rs2};
        
        printf("Cmn: 0x%x\n", (u32)emit_getCurrAdr());

        conditional(
            if (op.preOpType == PRE_OP_IMM) {
                regman.get(1, regs);
                emit_li(psp_a1, op.imm);
                emit_subu(psp_v0, (psp_gpr_t)regs[0], psp_a1);
            } else {
                regman.get(2, regs);
                arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[1], psp_a1, op);
                emit_subu(psp_v0, (psp_gpr_t)regs[0], psp_a1);
            }

            emit_srl(psp_t1, psp_v0, 31);
            emit_sltiu(psp_t3, psp_v0, 1);
 
            // t0 = c
            emit_not(psp_t0, (psp_gpr_t)regs[0]);
            emit_sltu(psp_t0, psp_t0, psp_a1);

            // V
            emit_slt(psp_t2, psp_a1, psp_zero);
            emit_slt(psp_t4, psp_v0, psp_t0);
            emit_xor(psp_t2, psp_t2, psp_t4);


            emit_ins(psp_gp, psp_t0, _flag_C8, _flag_C8);
            emit_ins(psp_gp, psp_t2, _flag_V8, _flag_V8);

            emit_ins(psp_gp, psp_t1, _flag_N8, _flag_N8);
            emit_ins(psp_gp, psp_t3, _flag_Z8, _flag_Z8);
            set_flag_dirty();
        )
        break;
    }

    case OP_CMP:
    {

        int32_t regs[2] = {op.rs1, op.rs2};

           // printf("Cmp: 0x%x\n", op.op_pc);
        conditional(

            if (op.preOpType == PRE_OP_IMM) {
                regman.get(1, regs);
                emit_li(psp_a1, op.imm);
                emit_subu(psp_v0, (psp_gpr_t)regs[0], psp_a1);
            } else {
                regman.get(2, regs);
                arm_preop[getTypeIdx(op.preOpType)]((psp_gpr_t)regs[1], psp_a1, op);
                emit_subu(psp_v0, (psp_gpr_t)regs[0], psp_a1);
            }

            /*if (op.op_pc == 0x01FF8014){
                emit_move(psp_a0, psp_zero);
                emit_move(psp_a1, psp_zero);
                emit_subu(psp_v0, psp_a0, psp_a1);
                printf("PATCHED CMP\n");
            }*/

            // t0 = c
            // t1 = n
            // t2 = v
            // t3 = z

            /*emit_srl(psp_t1, psp_v0, 31);
            emit_sltiu(psp_t3, psp_v0, 1);
 

            {
                emit_sltu(psp_t0, (psp_gpr_t)regs[0], psp_a0);
                emit_xori(psp_t0, psp_t0, 1);

                // V
                emit_slt(psp_t2, (psp_gpr_t)regs[0], psp_a0);
                emit_xor(psp_t2, psp_t2, psp_t1);


                emit_ins(psp_gp, psp_t0, _flag_C8, _flag_C8);
                emit_ins(psp_gp, psp_t2, _flag_V8, _flag_V8);
            }



            emit_ins(psp_gp, psp_t1, _flag_N8, _flag_N8);
            emit_ins(psp_gp, psp_t3, _flag_Z8, _flag_Z8);*/

            emit_jal(set_sub_flags);
            emit_move(psp_a0, (psp_gpr_t)regs[0]);

            // store_flags();

            set_flag_dirty();
        ) break;
    }

    case OP_HALT_HACK:
    {
        emit_jal(arm_halt_hack);
        emit_nop(); 
        break;
    }

    case OP_STMIA:
    case OP_NOP:
    case OP_LSR_0:
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

// Already compiled and optimized block
#include "precompiled_ops.h"


template <int PROCNUM>
bool block::emitThumbBlock()
{

    use_flags = true;

    // reg_alloc.reset(); 

    regman.reset(true);
    emit_li(psp_fp, opcodes.front().op_pc);

    opcode last_op = opcodes.back();
    const bool islastITP = last_op._op == OP_ITP;

    load_flags();

    for (opcode op : opcodes)
    {

        const u8 isize = 2;

        int32_t regs[]{op.rs1, op.rs2, op.rd};

        if ((op._op == OP_ITP || op._op == OP_SWI))
        {
            regman.flush_all();
            regman.reset(true);
        }
        /*else
        regman.push_sp_reg(3, regs);*/

        // reg_alloc.alloc_regs(op);

        if (last_op.op_pc != op.op_pc)
            emit_prefetch(isize, op.rs1 == 15 || op.rs2 == 15, op._op == OP_ITP);
        else
            // Last op has always to save
            emit_prefetch(isize, true, true);

        emitThumbOP<PROCNUM>(op);
    }

    if (flag_dirty)
        store_flags();
    flag_dirty = false;

    emit_prefetch_reset();
    regman.flush_all();
    regman.reset(true);

    // regman.pull_sp_regs();

    // possible idle loop, do more checks here
    return idleLoop;
}

static bool instr_is_conditional(u32 opcode)
{
    return !(CONDITION(opcode) == 0xE || (CONDITION(opcode) == 0xF && CODE(opcode) == 5));
}

template <int PROCNUM>
bool block::emitArmBlock()
{

    opcode last_op = opcodes.back();

    intr_instr = 0;

    use_flags = uses_flags;

    /*char * found = strstr(compiled_functions_hash, block_hash);

    if (found != NULL) {
        return arm_compiledOP[(found - compiled_functions_hash) / 51](PROCNUM);
    }*/
    //printf("JIT %s at %08X, %08X\n", PROCNUM?"ARM7":"ARM9", emit_getCurrAdr(), opcodes.front().op_pc);
    StartCodeDump();

    start_block = emit_getCurrAdr();
    emit_li(psp_fp, opcodes.front().op_pc);

    load_flags();

    regman.reset();

    const u8 isize = 4;
    for (opcode op : opcodes)
    {
        if ((op._op == OP_ITP || op._op == OP_SWI))
        {
            regman.flush_all();
            regman.reset();
        }

        if (last_op.op_pc != op.op_pc)
            emit_prefetch(isize, op.rs1 == 15 || op.rs2 == 15, op._op == OP_ITP);
        else
        {
            // Last op has always to save
            emit_prefetch(isize, true, true);
        }

        emitARMOP<PROCNUM>(op, last_op.op_pc == op.op_pc);
    }

    check_flags()

    emit_prefetch_reset();
    regman.flush_all();
    regman.reset();

    /*if (!JumpOP)
    {
        ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(last_op.op_pc + 4, ARM9);

        if (code_block)
        {
            // printf("Fast jump\n");
            emit_jal(code_block);
            emit_nop();
            JumpOP = true;
        }
    }*/

    // regman.pull_sp_regs();

    /*if (opcodes.size() > 30)
        CodeDump("30_ops.bin");
   */

    // possible idle loop, do more checks here
    return idleLoop;
}

template <int PROCNUM>
void block::emitArmBranch()
{
    uint32_t conditional_label = 0;
    uint32_t jump_sz = 0;

    opcode op = opcodes.back();

    emit_li(psp_fp, op.op_pc + 4);
    emit_sw(psp_fp, psp_k0, _next_instr);

    emit_addiu(psp_at, psp_fp, 4);
    emit_sw(psp_at, psp_k0, _R15);

    // conditional(emitARMOP<PROCNUM>(op))
}

// define the template
template bool block::emitArmBlock<0>();
template bool block::emitArmBlock<1>();

template void block::emitArmBranch<0>();
template void block::emitArmBranch<1>();
