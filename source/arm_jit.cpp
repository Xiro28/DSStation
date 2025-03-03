/*	Copyright (C) 2006 yopyop
	Copyright (C) 2011 Loren Merritt
	Copyright (C) 2012 DeSmuME team

	This file is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	This file is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with the this software.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "types.h"

#include <unistd.h>
#include <stddef.h>
#include <stdint.h>
#include <vector>
#include <unordered_map>


#include "MMU.h"
#include "MMU_timing.h"

#include "bios.h"

#include "PSP/FrontEnd.h"
#include "blockdecoder.h"

#include "PSP/emit/psp_emit.h"
#include "mips_code_emiter.h"

#include "Disassembler.h"

#include <pspsuspend.h>

u32 saveBlockSizeJIT = 0;
uint32_t interpreted_cycles = 0;
uint32_t base_adr = 0;

CACHE_ALIGN JIT_struct JIT;

uintptr_t *JIT_struct::JIT_MEM[0x4000] = {0};

//static u8 recompile_counts[(1<<26)/16];

static uintptr_t *JIT_MEM[32] = {
   //arm9
      /* 0X*/  DUP2(JIT.ARM9_ITCM),
      /* 1X*/  DUP2(JIT.ARM9_ITCM), // mirror
      /* 2X*/  DUP2(JIT.MAIN_MEM),
      /* 3X*/  DUP2(JIT.SWIRAM),
      /* 4X*/  DUP2(NULL),
      /* 5X*/  DUP2(NULL),
      /* 6X*/      NULL, 
                JIT.ARM9_LCDC,   // Plain ARM9-CPU Access (LCDC mode) (max 656KB)
      /* 7X*/  DUP2(NULL),
      /* 8X*/  DUP2(NULL),
      /* 9X*/  DUP2(NULL),
      /* AX*/  DUP2(NULL),
      /* BX*/  DUP2(NULL),
      /* CX*/  DUP2(NULL),
      /* DX*/  DUP2(NULL),
      /* EX*/  DUP2(NULL),
      /* FX*/  DUP2(JIT.ARM9_BIOS)  
};

static u32 JIT_MASK[32] = {
   //arm9
      /* 0X*/  DUP2(0x00007FFF),
      /* 1X*/  DUP2(0x00007FFF),
      /* 2X*/  DUP2(0x003FFFFF), // FIXME _MMU_MAIN_MEM_MASK
      /* 3X*/  DUP2(0x00007FFF),
      /* 4X*/  DUP2(0x00000000),
      /* 5X*/  DUP2(0x00000000),
      /* 6X*/      0x00000000,
                0x000FFFFF,
      /* 7X*/  DUP2(0x00000000),
      /* 8X*/  DUP2(0x00000000),
      /* 9X*/  DUP2(0x00000000),
      /* AX*/  DUP2(0x00000000),
      /* BX*/  DUP2(0x00000000),
      /* CX*/  DUP2(0x00000000),
      /* DX*/  DUP2(0x00000000),
      /* EX*/  DUP2(0x00000000),
      /* FX*/  DUP2(0x00007FFF)
};

// create hashmap for fast lookup of code blocks
std::unordered_map<uint32_t, uint32_t> generated_blocks;

static void init_jit_mem()
{
   static bool inited = false;  
  
      for(int i=0; i<0x4000; i++)
         JIT.JIT_MEM[i] = JIT_MEM[i>>9] + (((i<<14) & JIT_MASK[i>>9]) >> 1);
   
   if (inited) return;

   inited = true;
   initCodeCache();
   currentBlock.init(); 
} 

static bool thumb = false;
static uint32_t pc = 0;

static u32 instr_attributes(u32 opcode)
{
   return thumb ? thumb_attributes[opcode>>6]
                : instruction_attributes[INSTRUCTION_INDEX(opcode)];
}

static bool instr_is_conditional(u32 opcode)
{
	if(thumb) return false;
	
	return !(CONDITION(opcode) == 0xE
	         || (CONDITION(opcode) == 0xF && CODE(opcode) == 5));
}

static bool instr_is_branch(u32 opcode)
{ 
   u32 x = instr_attributes(opcode);
   if(thumb)
      return (x & BRANCH_ALWAYS)
          || ((x & BRANCH_POS0) && ((opcode&7) | ((opcode>>4)&8)) == 15)
          || (x & BRANCH_SWI)
          || (x & JIT_BYPASS);
   else
      return (x & BRANCH_ALWAYS)
          || ((x & BRANCH_POS12) && REG_POS(opcode,12) == 15)
          || ((x & BRANCH_LDM) && BIT15(opcode))
          || (x & BRANCH_SWI)
          || (x & JIT_BYPASS);
}

static int instr_cycles(u32 opcode)
{
	u32 x = instr_attributes(opcode);
	u32 c = (x & INSTR_CYCLES_MASK);
	if(c == INSTR_CYCLES_VARIABLE)
	{
		if ((x & BRANCH_SWI))
			return 3;
		
		return 0;
	}
	if(instr_is_branch(opcode) && !(instr_attributes(opcode) & (BRANCH_ALWAYS|BRANCH_LDM)))
		c += 2;
	return c;
}

enum INSTR_R { DYNAREC, DYNAREC_BRANCH, INTERPRET };

typedef INSTR_R (*DynaCompiler)(uint32_t pc, uint32_t opcode);

#define disable_op(name, PREOP, ...) static INSTR_R ARM_OP_##name##_##PREOP (uint32_t pc, const u32 i) { return INTERPRET; }

#define ARM_OP_REG_(name, PREOP, _rd) \
   static INSTR_R ARM_OP_##name##_##PREOP (uint32_t pc, const u32 i)\
   {\
      currentBlock.addOP(OP_##name, pc, _rd, REG_POS(i,16), REG_POS(i,0), REG_POS(i, 8), PRE_OP_##PREOP, instr_is_conditional(i) ? CONDITION(i) : -1);\
      return DYNAREC; \
   }

#define ARM_OP_IMM_(name, PREOP, _rd) \
   static INSTR_R ARM_OP_##name##_##PREOP (uint32_t pc, const u32 i)\
   {\
      currentBlock.addOP(OP_##name, pc, _rd, REG_POS(i,16), REG_POS(i, 0), ((i>>7)&0x1F), PRE_OP_##PREOP, instr_is_conditional(i) ? CONDITION(i) : -1);\
      return DYNAREC; \
   }


#define ARM_OP_IMM(name, PREOP) ARM_OP_IMM_(name, PREOP, REG_POS(i,12))
#define ARM_OP_REG(name, PREOP) ARM_OP_REG_(name, PREOP, REG_POS(i,12))

#define ARM_OP_UNDEF(T) \
   static const DynaCompiler ARM_OP_##T##_LSL_IMM = 0; \
   static const DynaCompiler ARM_OP_##T##_LSL_REG = 0; \
   static const DynaCompiler ARM_OP_##T##_LSR_IMM = 0; \
   static const DynaCompiler ARM_OP_##T##_LSR_REG = 0; \
   static const DynaCompiler ARM_OP_##T##_ASR_IMM = 0; \
   static const DynaCompiler ARM_OP_##T##_ASR_REG = 0; \
   static const DynaCompiler ARM_OP_##T##_ROR_IMM = 0; \
   static const DynaCompiler ARM_OP_##T##_ROR_REG = 0; \
   static const DynaCompiler ARM_OP_##T##_IMM_VAL = 0

ARM_OP_IMM(AND, LSL_IMM)
ARM_OP_REG(AND, LSL_REG)
ARM_OP_IMM(AND, LSR_IMM)
ARM_OP_REG(AND, LSR_REG)
ARM_OP_IMM(AND, ASR_IMM)
ARM_OP_REG(AND, ASR_REG)
ARM_OP_IMM(AND, ROR_IMM)
ARM_OP_REG(AND, ROR_REG)
static INSTR_R ARM_OP_AND_IMM_VAL (uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_AND, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}


ARM_OP_IMM(EOR, LSL_IMM)
ARM_OP_REG(EOR, LSL_REG)
ARM_OP_IMM(EOR, LSR_IMM)
ARM_OP_REG(EOR, LSR_REG)
ARM_OP_IMM(EOR, ASR_IMM)
ARM_OP_REG(EOR, ASR_REG)
ARM_OP_IMM(EOR, ROR_IMM)
ARM_OP_REG(EOR, ROR_REG)
static INSTR_R ARM_OP_EOR_IMM_VAL (uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_EOR, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}


ARM_OP_IMM(ORR, LSL_IMM)
ARM_OP_REG(ORR, LSL_REG)
ARM_OP_IMM(ORR, LSR_IMM)
ARM_OP_REG(ORR, LSR_REG)
ARM_OP_IMM(ORR, ASR_IMM)
ARM_OP_REG(ORR, ASR_REG)
ARM_OP_IMM(ORR, ROR_IMM)
ARM_OP_REG(ORR, ROR_REG)
static INSTR_R ARM_OP_ORR_IMM_VAL (uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_ORR, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}
 
ARM_OP_IMM(ADD, LSL_IMM)
ARM_OP_REG(ADD, LSL_REG)
ARM_OP_IMM(ADD, LSR_IMM)
ARM_OP_REG(ADD, LSR_REG)
ARM_OP_IMM(ADD, ASR_IMM)
ARM_OP_REG(ADD, ASR_REG)
ARM_OP_IMM(ADD, ROR_IMM)
ARM_OP_REG(ADD, ROR_REG)
static INSTR_R ARM_OP_ADD_IMM_VAL (uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_ADD, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC; 
}

ARM_OP_IMM(SUB, LSL_IMM)
ARM_OP_REG(SUB, LSL_REG)
ARM_OP_IMM(SUB, LSR_IMM) 
ARM_OP_REG(SUB, LSR_REG)
ARM_OP_IMM(SUB, ASR_IMM)
ARM_OP_REG(SUB, ASR_REG)
ARM_OP_IMM(SUB, ROR_IMM)
ARM_OP_REG(SUB, ROR_REG)
static INSTR_R ARM_OP_SUB_IMM_VAL(uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_SUB, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC; 
}

ARM_OP_IMM(BIC, LSL_IMM)
ARM_OP_REG(BIC, LSL_REG)
ARM_OP_IMM(BIC, LSR_IMM) 
ARM_OP_REG(BIC, LSR_REG)
ARM_OP_IMM(BIC, ASR_IMM)
ARM_OP_REG(BIC, ASR_REG)
ARM_OP_IMM(BIC, ROR_IMM)
ARM_OP_REG(BIC, ROR_REG)
static INSTR_R ARM_OP_BIC_IMM_VAL(uint32_t pc, const u32 i)
{ 
   currentBlock.addOP(OP_AND, pc, REG_POS(i,12), REG_POS(i,16), -1, ~ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC; 
}



static INSTR_R ARM_OP_SBC_LSL_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_LSL_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_LSR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_LSR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_ASR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_ASR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_ROR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_IMM_VAL(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_SBC_ROR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }



ARM_OP_IMM(RSB, LSL_IMM)
ARM_OP_REG(RSB, LSL_REG)
ARM_OP_IMM(RSB, LSR_IMM)
ARM_OP_REG(RSB, LSR_REG)
ARM_OP_IMM(RSB, ASR_IMM)
ARM_OP_REG(RSB, ASR_REG)
ARM_OP_IMM(RSB, ROR_IMM)
ARM_OP_REG(RSB, ROR_REG)
static INSTR_R ARM_OP_RSB_IMM_VAL(uint32_t pc, const u32 i) 
{
   currentBlock.addOP(OP_RSB, pc, REG_POS(i,12), REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC;
}



static INSTR_R ARM_OP_RSC_LSL_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_LSL_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_LSR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_LSR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_ASR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_ASR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_ROR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_ROR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_RSC_IMM_VAL(uint32_t pc, const u32 i) { return INTERPRET; }

static INSTR_R ARM_OP_ADC_LSL_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_LSL_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_LSR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_LSR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_ASR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_ASR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_ROR_IMM(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_ROR_REG(uint32_t pc, const u32 i) { return INTERPRET; }
static INSTR_R ARM_OP_ADC_IMM_VAL(uint32_t pc, const u32 i) { return INTERPRET; }
 
//-----------------------------------------------------------------------------
//   MOV
//-----------------------------------------------------------------------------
 
static INSTR_R ARM_OP_MOV_LSL_IMM (uint32_t pc, const u32 i)
{
   if (i != 0xE1A00000){
      currentBlock.addOP(OP_MOV, pc, REG_POS(i,12), REG_POS(i,16), REG_POS(i, 0), ((i>>7)&0x1F), PRE_OP_LSL_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
   }

   return DYNAREC; 
}


ARM_OP_REG(MOV, LSL_REG)
ARM_OP_IMM(MOV, LSR_IMM)
ARM_OP_REG(MOV, LSR_REG)
ARM_OP_IMM(MOV, ASR_IMM)
ARM_OP_REG(MOV, ASR_REG)
ARM_OP_IMM(MOV, ROR_IMM)
ARM_OP_REG(MOV, ROR_REG)
static INSTR_R ARM_OP_MOV_IMM_VAL(uint32_t pc, const u32 i) 
{
   currentBlock.addOP(OP_MOV, pc, REG_POS(i,12), -1, -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC; 
}

//-----------------------------------------------------------------------------
//   MVN
//-----------------------------------------------------------------------------

ARM_OP_IMM(MVN, LSL_IMM)
ARM_OP_REG(MVN, LSL_REG)
ARM_OP_IMM(MVN, LSR_IMM)
ARM_OP_REG(MVN, LSR_REG)
ARM_OP_IMM(MVN, ASR_IMM)
ARM_OP_REG(MVN, ASR_REG)
ARM_OP_IMM(MVN, ROR_IMM)
ARM_OP_REG(MVN, ROR_REG)
static INSTR_R ARM_OP_MVN_IMM_VAL(uint32_t pc, const u32 i) 
{ 
   currentBlock.addOP(OP_MOV, pc, REG_POS(i,12), -1, -1, ~ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC; 
}


//-----------------------------------------------------------------------------
//   CMP
//-----------------------------------------------------------------------------

   

ARM_OP_UNDEF(CMP );
ARM_OP_UNDEF(TST );

 
ARM_OP_UNDEF(AND_S);
ARM_OP_UNDEF(EOR_S);
ARM_OP_UNDEF(SUB_S);
ARM_OP_UNDEF(RSB_S);
ARM_OP_UNDEF(ADD_S);
ARM_OP_UNDEF(ADC_S);
ARM_OP_UNDEF(SBC_S);
ARM_OP_UNDEF(RSC_S);
ARM_OP_UNDEF(TEQ  );
ARM_OP_UNDEF(CMN  );
ARM_OP_UNDEF(ORR_S);
ARM_OP_UNDEF(MOV_S);
ARM_OP_UNDEF(BIC_S);
ARM_OP_UNDEF(MVN_S);

static INSTR_R ARM_OP_MUL(uint32_t pc, const u32 i) 
{
   interpreted_cycles += 2;
   currentBlock.addOP(OP_MUL, pc, REG_POS(i,16), REG_POS(i,0), REG_POS(i,8), -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
} 

static INSTR_R ARM_OP_MLA(uint32_t pc, const u32 i) {
   interpreted_cycles += 2;
   currentBlock.addOP(OP_MLA, pc, REG_POS(i,16), REG_POS(i,0), REG_POS(i,8), REG_POS(i,12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}


static INSTR_R ARM_OP_UMULL(uint32_t pc, const u32 i) {
    return INTERPRET;
   interpreted_cycles += 6;
   currentBlock.addOP(OP_UMUL, pc, REG_POS(i,16), REG_POS(i,0), REG_POS(i,8), REG_POS(i,12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}

static INSTR_R ARM_OP_SMULL(uint32_t pc, const u32 i) {
   return INTERPRET;
}

static INSTR_R ARM_OP_UMLAL(uint32_t pc, const u32 i) {
   return INTERPRET;
   currentBlock.addOP(OP_UMLA, pc, REG_POS(i,16), REG_POS(i,0), REG_POS(i,8), REG_POS(i,12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}

#define ARM_OP_MUL_S 0
#define ARM_OP_MLA_S 0
#define ARM_OP_MLA_S 0
#define ARM_OP_MUL_S 0

#define ARM_OP_UMULL_S     0
#define ARM_OP_UMLAL_S     0
#define ARM_OP_SMULL_S     0
#define ARM_OP_SMLAL       0
#define ARM_OP_SMLAL_S     0

#define ARM_OP_SMUL_B_B    0
#define ARM_OP_SMUL_T_B    0
#define ARM_OP_SMUL_B_T    0
#define ARM_OP_SMUL_T_T    0

#define ARM_OP_SMLA_B_B    0
#define ARM_OP_SMLA_T_B    0
#define ARM_OP_SMLA_B_T    0
#define ARM_OP_SMLA_T_T    0

#define ARM_OP_SMULW_B     0
#define ARM_OP_SMULW_T     0
#define ARM_OP_SMLAW_B     0
#define ARM_OP_SMLAW_T     0

#define ARM_OP_SMLAL_B_B   0
#define ARM_OP_SMLAL_T_B   0
#define ARM_OP_SMLAL_B_T   0
#define ARM_OP_SMLAL_T_T   0

#define ARM_OP_QADD        0
#define ARM_OP_QSUB        0
#define ARM_OP_QDADD       0
#define ARM_OP_QDSUB       0

//#define ARM_OP_CLZ         0
static INSTR_R ARM_OP_CLZ(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_CLZ, pc, REG_POS(i,12), REG_POS(i,0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC; 
}

inline bool isMainMemory(u32 addr)
{
   return ((addr & 0x0F000000) == 0x02000000) && !((addr&(~0x3FFF)) == MMU.DTCMRegion);
}

#define ARM_MEM_OP_DEF2(T, Q) \
   static const DynaCompiler ARM_OP_##T##_M_LSL_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_LSL_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_LSR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_LSR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_ASR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_ASR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_ROR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_ROR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_##Q = 0

#define ARM_MEM_OP_DEF(T) \
   ARM_MEM_OP_DEF2(T, IMM_OFF_PREIND); \
   ARM_MEM_OP_DEF2(T, IMM_OFF); \
   ARM_MEM_OP_DEF2(T, IMM_OFF_POSTIND)

ARM_MEM_OP_DEF(STRB);
ARM_MEM_OP_DEF(LDRB);

// Helpers to choose positive or negative offset:
#define POS(x) (x)
#define NEG(x) (-(x))

#define GEN_ARM_STR_OP_FUNC(Name, MODE, VAL)                                  \
static INSTR_R Name(uint32_t pc, const u32 i){             \
   currentBlock.WriteOP = true; \
   return INTERPRET; \
   interpreted_cycles += 2; \
    currentBlock.addOP(OP_STR, pc, REG_POS(i,16), REG_POS(i,12), REG_POS(i, 0),         \
         VAL,                            \
         (opType)MODE,                                                     \
         instr_is_conditional(i) ? CONDITION(i) : -1,                        \
         EXTFL_NONE);                                                       \
    return DYNAREC;                                                          \
}

#define LSR_IMM \
	u32 shift_op = ((i>>7)&0x1F); \
	if(shift_op!=0) \
		shift_op = cpu->R[REG_POS(i,0)]>>shift_op;

u32 get_addr(u32 addr, u32 shift_op, u32 type, u32 i){
   u32 sign = 1;

   if ((type & 0xfff) == PRE_OP_IMM_POST_M || (type & 0xfff) == PRE_OP_IMM_POST_P) return addr;
   if (type == 1) return addr + shift_op;

   shift_op = shift_op < 0 ? -shift_op : shift_op;

   if ((type & 0xfff) == PRE_OP_IMM_PRE_M) sign = -1;
   

   switch (type >> 16){
      case PRE_OP_LSL_IMM: return addr + (sign * (_ARMPROC.R[REG_POS(i,0)] << shift_op));
      case PRE_OP_LSR_IMM: return (shift_op != 0) ? addr + (sign * (_ARMPROC.R[REG_POS(i,0)] >> shift_op)) : 0;
      case PRE_OP_ASR_IMM: {
         if(shift_op==0) 
		      return addr + (sign * BIT31(_ARMPROC.R[REG_POS(i,0)])*0xFFFFFFFF);
	      else 
		      return addr + (sign * (u32)((s32)_ARMPROC.R[REG_POS(i,0)]>>shift_op));
      }
      case PRE_OP_ROR_IMM: return (shift_op != 0) ? addr + (sign * shift_op) : 0;
   }
}

#define GEN_ARM_LDR_OP_FUNC(Name, MODE, VAL)                                    \
static INSTR_R Name(uint32_t pc, const u32 i){             \
    if (REG_POS(i,12)==15)                                                   \
        return INTERPRET;                                                  \
        return INTERPRET; \
   interpreted_cycles += 2; \
   u32 val = get_addr(_ARMPROC.R[REG_POS(i,16)], VAL, MODE, i); \
    currentBlock.addOP(OP_LDR, pc, REG_POS(i,12), REG_POS(i,16), REG_POS(i, 0),         \
          VAL,                                                   \
         (opType)MODE,                                                     \
         instr_is_conditional(i) ? CONDITION(i) : -1,                        \
         isMainMemory(val) ? EXTFL_DIRECTMEMACCESS : EXTFL_NONE);            \
    return DYNAREC;                                                          \
}

#define CONCAT(a, b) a##b
#define EXPAND_AND_CONCAT(a, b) CONCAT(a, b)


#define gen_ldr_sub(G, TP, TM) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_, G), (TP), POS((i)&0xFFF)) \
GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_, G), (TM), NEG((i)&0xFFF))


#define gen_ldr()
   gen_ldr_sub(IMM_OFF_PREIND, PRE_OP_IMM_PRE_P, PRE_OP_IMM_PRE_M) \
   gen_ldr_sub(IMM_OFF_POSTIND, PRE_OP_IMM_POST_P, PRE_OP_IMM_POST_M) \
   gen_ldr_sub(IMM_OFF, 1, 1)  


#define gen_str_sub(G, TP, TM) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TP), POS(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TM), NEG(((i>>7)&0x1F))) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_, G), (TP), POS((i)&0xFFF)) \
GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_, G), (TM), NEG((i)&0xFFF))


#define gen_str()
   gen_str_sub(IMM_OFF_PREIND, PRE_OP_IMM_PRE_P, PRE_OP_IMM_PRE_M) \
   gen_str_sub(IMM_OFF_POSTIND, PRE_OP_IMM_POST_P, PRE_OP_IMM_POST_M) \
   gen_str_sub(IMM_OFF, 1, 1) 


gen_str()
gen_ldr()





#define DEFINE_ARM_OP_LDR(NAME, OP_TYPE, PRE_OP, IMM, FLAG) \
static INSTR_R NAME(uint32_t pc, const u32 i) \
{ \
    if (PRE_OP == PRE_OP_IMM || PRE_OP == PRE_OP_IMM_PRE_P || PRE_OP == PRE_OP_IMM_PRE_M || PRE_OP == PRE_OP_IMM_POST_P || PRE_OP == PRE_OP_IMM_POST_M) { \
        currentBlock.addOP(OP_TYPE, pc, REG_POS(i, 12), REG_POS(i, 16), -1, \
            IMM, PRE_OP, \
            instr_is_conditional(i) ? CONDITION(i) : -1, FLAG); \
        return DYNAREC; \
    } else { \
        return INTERPRET; \
    } \
}

#define DEFINE_ARM_OP_STR(NAME, OP_TYPE, PRE_OP, IMM, FLAG) \
static INSTR_R NAME(uint32_t pc, const u32 i) \
{ \
   currentBlock.WriteOP = true; \
    if (PRE_OP == PRE_OP_IMM || PRE_OP == PRE_OP_IMM_PRE_P || PRE_OP == PRE_OP_IMM_PRE_M || PRE_OP == PRE_OP_IMM_POST_P || PRE_OP == PRE_OP_IMM_POST_M) { \
        currentBlock.addOP(OP_TYPE, pc, REG_POS(i,  16), REG_POS(i, 12), -1, \
            IMM, PRE_OP, \
            instr_is_conditional(i) ? CONDITION(i) : -1, FLAG); \
            interpreted_cycles += 2; \
        return DYNAREC; \
    } else { \
        return INTERPRET; \
    } \
}



#define DEFINE_ARM_OP_STR_HB(OP_TYPE, IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_P_IMM_OFF, OP_TYPE, PRE_OP_IMM,  IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_M_IMM_OFF, OP_TYPE, PRE_OP_IMM, -IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_P_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_M_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_P, IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_M, -IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_P_REG_OFF, OP_TYPE,PRE_OP_NONE, IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_M_REG_OFF, OP_TYPE,PRE_OP_NONE, -IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_P, IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_M, -IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG) \
DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)

#define DEFINE_ARM_OP_LDR_HB(OP_TYPE, IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_P_IMM_OFF, OP_TYPE, PRE_OP_IMM,  IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_M_IMM_OFF, OP_TYPE, PRE_OP_IMM, -IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_P_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_M_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_P, IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_M, -IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_P, IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_M, -IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG) \
DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)


DEFINE_ARM_OP_STR_HB(OP_STRH,  (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)

DEFINE_ARM_OP_LDR_HB(OP_LDRH,  (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)
DEFINE_ARM_OP_LDR_HB(OP_LDRSB, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)
DEFINE_ARM_OP_LDR_HB(OP_LDRSH, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)





#define SIGNEXTEND_24(i) (((s32)i<<8)>>8)

static INSTR_R ARM_OP_B(uint32_t pc, const u32 i)
{
   return INTERPRET;

	if(instr_is_conditional(i) || CONDITION(i)==0xF || _ARMPROC.CPSR.bits.T == 1)
	{
		return INTERPRET;
	}

	u32 off = SIGNEXTEND_24(i);
   
   if (currentBlock.branch_addr == currentBlock.start_addr) 
      printf("WARNING: B to self\n");

   
   currentBlock.addOP(OP_BXC, pc, 15, -1, -1, (off<<2), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   
   return DYNAREC_BRANCH;
}

#define ARM_OP_BL 0

//-----------------------------------------------------------------------------
//   MRS / MSR
//-----------------------------------------------------------------------------
static INSTR_R ARM_OP_MRS_CPSR(uint32_t pc, const u32 i)
{
   currentBlock.MCROP = true;
   return INTERPRET;
}


static INSTR_R ARM_OP_MRS_SPSR(uint32_t pc, const u32 i)
{
   currentBlock.MCROP = true;
   return INTERPRET;
}


//-----------------------------------------------------------------------------
//   SWP/SWPB
//-----------------------------------------------------------------------------

#define _ARMPROC (block_procnum ? NDS_ARM7:NDS_ARM9)

static INSTR_R ARM_OP_SWP (uint32_t pc, const u32 i) { return INTERPRET;  };
static INSTR_R ARM_OP_SWPB(uint32_t pc, const u32 i) { return INTERPRET;  };

static INSTR_R ARM_OP_MCR(uint32_t pc, const u32 i){ 
   currentBlock.MCROP = true;
   return INTERPRET;
}
static INSTR_R ARM_OP_MRC(uint32_t pc, const u32 i){ 
   currentBlock.MCROP = true;
   return INTERPRET;
}
 


static INSTR_R ARM_OP_SWI(uint32_t pc, const u32 i){
   currentBlock.addOP(OP_SWI, pc, -1, ((i>>16)&0x1F), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

bool abc = false;

static INSTR_R ARM_OP_BX(uint32_t pc, const u32 i){
   //u32 tmp = _ARMPROC.R[REG_POS(i, 0)];
	//currentBlock.branch_addr = tmp & (0xFFFFFFFC|(BIT0(tmp)<<1));

   //if (currentBlock.branch_addr == currentBlock.start_addr) printf("WARNING: BX to self\n");

   //ArmOpCompiled f = (ArmOpCompiled)JIT_COMPILED_FUNC(currentBlock.branch_addr, ARM9);

   //if (f && codeCacheLinked[currentBlock.branch_addr] == 0 && codeCacheLinked[currentBlock.start_addr] == 0)
   /*if (currentBlock.branch_addr == currentBlock.start_addr && !codeCacheLinked[currentBlock.branch_addr] && !BIT0(tmp))
   {
      //printf("BX to its self\n");
      codeCacheLinked[currentBlock.branch_addr] = currentBlock.start_addr;
      currentBlock.addOP(OP_BXC, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      //currentBlock.addOP(OP_BXC, pc, interpreted_cycles, -1, -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      return DYNAREC_BRANCH;
   }*/

   /*currentBlock.addOP(OP_BXC, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC_BRANCH;*/

   currentBlock.addOP(OP_BXC, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   LDRD / STRD
//-----------------------------------------------------------------------------

static INSTR_R ARM_OP_LDRD_STRD_POST_INDEX(uint32_t pc, const u32 i){
   return INTERPRET;
}

static INSTR_R ARM_OP_STMIA(uint32_t pc, const u32 i){
   return INTERPRET;
   currentBlock.addOP(OP_STMIA, pc, -1, i, REG_POS(i,16), -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}


#define ARM_OP_LDRD_STRD_OFFSET_PRE_INDEX 0
#define ARM_OP_MSR_CPSR 0
//#define ARM_OP_BX 0
#define ARM_OP_BLX_REG 0
#define ARM_OP_BKPT 0
#define ARM_OP_MSR_SPSR 0
#define ARM_OP_STREX 0
#define ARM_OP_LDREX 0
#define ARM_OP_MSR_CPSR_IMM_VAL 0
#define ARM_OP_MSR_SPSR_IMM_VAL 0
#define ARM_OP_STMDA 0
#define ARM_OP_LDMDA 0
#define ARM_OP_STMDA_W 0
#define ARM_OP_LDMDA_W 0
#define ARM_OP_STMDA2 0
#define ARM_OP_LDMDA2 0
#define ARM_OP_STMDA2_W 0
#define ARM_OP_LDMDA2_W 0
//#define ARM_OP_STMIA 0
#define ARM_OP_LDMIA 0
#define ARM_OP_STMIA_W 0
#define ARM_OP_LDMIA_W 0
#define ARM_OP_STMIA2 0
#define ARM_OP_LDMIA2 0
#define ARM_OP_STMIA2_W 0
#define ARM_OP_LDMIA2_W 0
#define ARM_OP_STMDB 0
#define ARM_OP_LDMDB 0
#define ARM_OP_STMDB_W 0
#define ARM_OP_LDMDB_W 0
#define ARM_OP_STMDB2 0
#define ARM_OP_LDMDB2 0
#define ARM_OP_STMDB2_W 0
#define ARM_OP_LDMDB2_W 0
#define ARM_OP_STMIB 0
#define ARM_OP_LDMIB 0
#define ARM_OP_STMIB_W 0
#define ARM_OP_LDMIB_W 0
#define ARM_OP_STMIB2 0
#define ARM_OP_LDMIB2 0
#define ARM_OP_STMIB2_W 0
#define ARM_OP_LDMIB2_W 0
#define ARM_OP_STC_OPTION 0
#define ARM_OP_LDC_OPTION 0
#define ARM_OP_STC_M_POSTIND 0
#define ARM_OP_LDC_M_POSTIND 0
#define ARM_OP_STC_P_POSTIND 0
#define ARM_OP_LDC_P_POSTIND 0
#define ARM_OP_STC_M_IMM_OFF 0
#define ARM_OP_LDC_M_IMM_OFF 0
#define ARM_OP_STC_M_PREIND 0
#define ARM_OP_LDC_M_PREIND 0
#define ARM_OP_STC_P_IMM_OFF 0
#define ARM_OP_LDC_P_IMM_OFF 0
#define ARM_OP_STC_P_PREIND 0
#define ARM_OP_LDC_P_PREIND 0
#define ARM_OP_CDP 0
#define ARM_OP_UND 0
static const DynaCompiler arm_instruction_compilers[4096] = {
#define TABDECL(x) ARM_##x
#include "instruction_tabdef.inc"
#undef TABDECL
};

////////
// THUMB
////////

static INSTR_R THUMB_OP_ASR(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_LSL_0(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MOV, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_LSL(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static INSTR_R THUMB_OP_LSR_0(uint32_t pc, const u32 i)
{
   return INTERPRET;

   printf("OP_LSR_0 not tested\n");
   currentBlock.addOP(OP_LSR_0, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_LSR(uint32_t pc, const u32 i)
{
   return INTERPRET; 
}


static INSTR_R THUMB_OP_MOV_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MOV, pc, _REG_NUM(i, 8), -1, -1, i&0xff, PRE_OP_IMM);
   return DYNAREC;
}
 

static INSTR_R THUMB_OP_ADD_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, pc, _REG_NUM(i, 8), _REG_NUM(i, 8), -1, i&0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_IMM3(uint32_t pc, const u32 i)
{
   u32 imm = (i>>6)&0x07;
   if (imm == 0)
      currentBlock.addOP(OP_MOV, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   else
      currentBlock.addOP(OP_ADD, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, imm, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6));
   return DYNAREC;
}

static INSTR_R THUMB_OP_SUB_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SUB, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6));
   return DYNAREC;
}

static INSTR_R THUMB_OP_CMP_IMM8(uint32_t pc, const u32 i)
{
   return INTERPRET; 
   currentBlock.addOP(OP_CMP, pc, -1, _REG_NUM(i, 8), -1, i&0xff, PRE_OP_IMM);
   return DYNAREC; 
}

static INSTR_R THUMB_OP_SUB_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SUB, pc, _REG_NUM(i, 8), _REG_NUM(i, 8), -1, i&0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_SUB_IMM3(uint32_t pc, const u32 i)
{
   return INTERPRET;
   u32 imm = (i>>6)&0x07;
   currentBlock.addOP(OP_SUB, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, imm, PRE_OP_IMM);
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   AND
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_AND(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_AND, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_BIC(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static INSTR_R THUMB_OP_CMN(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_NEG(uint32_t pc, const u32 i)
{
   return INTERPRET; 
   currentBlock.addOP(OP_NEG, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}



//-----------------------------------------------------------------------------
//   EOR
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_EOR(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_EOR, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

//-----------------------------------------------------------------------------
//   MVN
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_MVN(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MVN, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_ORR(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ORR, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

//-----------------------------------------------------------------------------
//   TST
//-----------------------------------------------------------------------------
static INSTR_R THUMB_OP_TST(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_TST, pc, -1, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_CMP(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_CMP, pc, -1, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_ROR_REG(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_MOV_SPE(uint32_t pc, const u32 i)
{
   u32 Rd = _REG_NUM(i, 0) | ((i>>4)&8);
   
   currentBlock.addOP(OP_MOV, pc, Rd, REG_POS(i, 3));
   return DYNAREC; 
}

static INSTR_R THUMB_OP_ADD_SPE(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_MUL_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MUL, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC; 
}


static INSTR_R THUMB_OP_CMP_SPE(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_B_COND(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_B_UNCOND(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_ADJUST_P_SP(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, pc, 13, 13, -1, ((i&0x7F)<<2), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADJUST_M_SP(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, pc, 13, 13, -1, -((i&0x7F)<<2), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
} 

static INSTR_R THUMB_OP_ADD_2PC(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_ADD_2SP(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_ADD, pc, _REG_NUM(i, 8), 13, -1, ((i&0xFF)<<2), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
}

static INSTR_R THUMB_OP_BL_10(uint32_t pc, const u32 i)
{
   return INTERPRET; 
}

static INSTR_R THUMB_OP_POP(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_PUSH(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_SWI_THUMB(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SWI, pc, -1, i&0x1F);
   return DYNAREC;
}

static INSTR_R THUMB_OP_STRB_REG_OFF(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_LDRB_REG_OFF(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static INSTR_R THUMB_OP_STRH_REG_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_STRH, pc, _REG_NUM(i, 3), _REG_NUM(i,0), _REG_NUM(i,6), 0, PRE_OP_REG, -2);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDRH_REG_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + _ARMPROC.R[_REG_NUM(i, 6)];

   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_LDRH, pc, _REG_NUM(i,0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG, -1, EXTFL_DIRECTMEMACCESS);
   else*/
      currentBlock.addOP(OP_LDRH, pc, _REG_NUM(i,0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG);

   return DYNAREC;
}

static INSTR_R THUMB_OP_STRB_IMM_OFF(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_LDRB_IMM_OFF(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_STRH_IMM_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i>>5)&0x3E);


   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_STRH, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>5)&0x3E), PRE_OP_IMM, -2, EXTFL_DIRECTMEMACCESS);
   else*/
      currentBlock.addOP(OP_STRH, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>5)&0x3E), PRE_OP_IMM, -2);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDRH_IMM_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i>>5)&0x3E);

   currentBlock.addOP(OP_LDRH, pc, _REG_NUM(i,0), _REG_NUM(i, 3), -1, ((i>>5)&0x3E), PRE_OP_IMM);
   return DYNAREC;
}


static INSTR_R THUMB_OP_STR_IMM_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i>>4)&0x7C);

   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_STR, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>4)&0x7C), PRE_OP_IMM, -1, EXTFL_DIRECTMEMACCESS);
   else*/
      currentBlock.addOP(OP_STR, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>4)&0x7C), PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_STR_REG_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_STR, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), _REG_NUM(i, 6), -1, PRE_OP_REG);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDR_REG_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_LDR, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDR_IMM_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_LDR, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, ((i>>4)&0x7C), PRE_OP_IMM);
   return DYNAREC;
}



static INSTR_R THUMB_OP_BL_11(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static INSTR_R THUMB_OP_BLX(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_BLX_THUMB(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static INSTR_R THUMB_OP_BX_THUMB(uint32_t pc, const u32 i)
{
   return INTERPRET;
}



#define THUMB_OP_INTERPRET       0

#define THUMB_OP_ASR             THUMB_OP_INTERPRET

#define THUMB_OP_UND_THUMB       THUMB_OP_INTERPRET

#define THUMB_OP_ASR_0           THUMB_OP_INTERPRET

#define THUMB_OP_LSL_REG         THUMB_OP_INTERPRET
#define THUMB_OP_LSR_REG         THUMB_OP_INTERPRET
#define THUMB_OP_ASR_REG         THUMB_OP_INTERPRET
#define THUMB_OP_ADC_REG         THUMB_OP_INTERPRET
#define THUMB_OP_SBC_REG         THUMB_OP_INTERPRET
#define THUMB_OP_ROR_REG         THUMB_OP_INTERPRET

#define THUMB_OP_LDR_SPREL       THUMB_OP_INTERPRET
#define THUMB_OP_STR_SPREL       THUMB_OP_INTERPRET
#define THUMB_OP_LDR_PCREL       THUMB_OP_INTERPRET


#define THUMB_OP_LDRSB_REG_OFF   THUMB_OP_INTERPRET
#define THUMB_OP_LDRSH_REG_OFF   THUMB_OP_INTERPRET


// UNDEFINED OPS
#define THUMB_OP_PUSH_LR         THUMB_OP_INTERPRET
#define THUMB_OP_BKPT_THUMB      THUMB_OP_INTERPRET

static INSTR_R THUMB_OP_POP_PC(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_STMIA_THUMB(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_LDMIA_THUMB(uint32_t pc, const u32 i)
{
   return INTERPRET;
}


static const DynaCompiler thumb_instruction_compilers[1024] = {
#define TABDECL(x) THUMB_##x
#include "thumb_tabdef.inc"
#undef TABDECL
};

// ============================================================================================= IMM

//-----------------------------------------------------------------------------
//   Generic instruction wrapper
//-----------------------------------------------------------------------------

template<int PROCNUM, int thumb>
static u32 FASTCALL OP_DECODE()
{
	u32 cycles;
	u32 adr = ARMPROC.instruct_adr;
	if(thumb)
	{
		ARMPROC.next_instruction = adr + 2;
		ARMPROC.R[15] = adr + 4;
		u32 opcode = _MMU_read16<PROCNUM, MMU_AT_CODE>(adr);
		cycles = thumb_instructions_set[opcode>>6](opcode);
	}
	else
	{
		ARMPROC.next_instruction = adr + 4;
		ARMPROC.R[15] = adr + 8;
		u32 opcode = _MMU_read32<PROCNUM, MMU_AT_CODE>(adr);
		if(CONDITION(opcode) == 0xE || TEST_COND(CONDITION(opcode), CODE(opcode), ARMPROC.CPSR))
			cycles = arm_instructions_set[INSTRUCTION_INDEX(opcode)](opcode);
		else
			cycles = 1;
	}
	ARMPROC.instruct_adr = ARMPROC.next_instruction;
	return cycles;
}

static const ArmOpCompiled op_decode[2][2] = { OP_DECODE<0,0>, OP_DECODE<0,1>, OP_DECODE<1,0>, OP_DECODE<1,1> };


bool instr_does_prefetch(u32 opcode)
{
	u32 x = instr_attributes(opcode);
	if(thumb)
		return thumb_instruction_compilers[opcode>>6]
			   && (x & BRANCH_ALWAYS);
	else
		return instr_is_branch(opcode) && arm_instruction_compilers[INSTRUCTION_INDEX(opcode)]
			   && ((x & BRANCH_ALWAYS) || (x & BRANCH_LDM));
}


//-----------------------------------------------------------------------------
//   Compiler
//-----------------------------------------------------------------------------


template<int PROCNUM>
static u32 compile_basicblock()
{
   uint32_t opcode = 0;
   void* code_ptr = emit_GetPtr();

   // insert here the value if we are using a idle block
   // we're going to use it when taking the code from memory
   // since we don't save the block with the necessary info
      
   const bool isIdle = currentBlock.IsIdleLoop(thumb);

   emit_mpush(9,
            reg_gpr+psp_s0,
            reg_gpr+psp_s1,
            reg_gpr+psp_s2,
            reg_gpr+psp_s3,
            reg_gpr+psp_s4,
				reg_gpr+psp_gp,
				reg_gpr+psp_k0,
				reg_gpr+psp_fp,
				reg_gpr+psp_ra); 

   //StartCodeDump();

   emit_li(psp_k0,((u32)&ARMPROC), 2);
   //emit_move(psp_k1, psp_zero);


   if (thumb){
      currentBlock.emitThumbBlock<PROCNUM>();
         //printf("idle loop thumb\n");
   }else{
      currentBlock.emitArmBlock<PROCNUM>();
         // printf("idle loop arm\n");
   }


   if (currentBlock.manualPrefetch || currentBlock.JumpOP)  
   {
      emit_lw(psp_at, RCPU, _next_instr);
      emit_sw(psp_at, RCPU, _instr_adr);
   }

   const float multiplier = isIdle ? 1.5f : 1.1f;
   if (currentBlock.JumpOP)
   {
      emit_addiu(psp_v0, psp_v0, interpreted_cycles * multiplier);
   }else{
      emit_addiu(psp_v0, psp_zero, interpreted_cycles * multiplier);
   }

   emit_mpop(9,
            reg_gpr+psp_s0,
            reg_gpr+psp_s1,
            reg_gpr+psp_s2,
            reg_gpr+psp_s3,
            reg_gpr+psp_s4,
				reg_gpr+psp_gp,
				reg_gpr+psp_k0,
				reg_gpr+psp_fp,
				reg_gpr+psp_ra);
   
   emit_jra();
   emit_movi(psp_v1,  isIdle ? 1 : 0);

   // Align the code to 64 bytes
   while(emit_getCurrAdr() & 0x3F) emit_nop();
   
   make_address_range_executable((u32)code_ptr, (u32)emit_GetPtr());
   JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)code_ptr;

   return interpreted_cycles;
}


#define _SHA1_DIGEST_LENGTH 5

inline bool is_ldr(uint32_t opcode) {
    return ((opcode & 0x0E500000) == 0x04100000);
}

inline bool is_lhu(uint32_t opcode) {
    return ((opcode & 0x0E700000) == 0x08500000);
}

inline bool is_lbu(uint32_t opcode) {
    return ((opcode & 0x0E700000) == 0x08700000);
}

inline bool is_str(uint32_t opcode) {
    return ((opcode & 0x0E500000) == 0x04000000);
}

inline bool is_sh(uint32_t opcode) {
    return ((opcode & 0x0E700000) == 0x08400000);
}

inline bool is_sb(uint32_t opcode) {
    return ((opcode & 0x0E700000) == 0x08600000);
}

// Check if the opcode is a B (Branch) instruction
inline bool is_b(uint32_t opcode) {
    // Match the pattern: cond 1010 (B) with link bit 0
    return ((opcode & 0x0F000000) == 0x0A000000);
}

// Check if the opcode is a BL (Branch with Link) instruction
inline bool is_bl(uint32_t opcode) {
    // Match the pattern: cond 1011 (BL) with link bit 1
    return ((opcode & 0x0F000000) == 0x0B000000);
}

// Check if the opcode is a BX (Branch Exchange) instruction
inline bool is_bx(uint32_t opcode) {
    // Match the pattern: cond 0001 0010 1111 1111 1111 reg
    return ((opcode & 0x0FFFFFF0) == 0x012FFF10);
}

inline bool isARMBranchInstruction(u32 opcode)
{
   return is_b(opcode) || is_bl(opcode) || is_bx(opcode);
}


inline bool isARMWritingInstruction(u32 opcode)
{
   return is_sb(opcode) || is_sh(opcode) || is_str(opcode);
}

inline bool is_mcr_mrc(uint32_t opcode) {
    return (opcode & 0x0F000010) == 0x0E000000;
}

template<int PROCNUM>
void build_ArmBasicblock(){

   uint32_t opnum = 0;
   const u32 isize = 4;
   const uint32_t imask = 0xFFFFFFFC;

   uint32_t digest[_SHA1_DIGEST_LENGTH];

	SceKernelUtilsSha1Context ctx;
	sceKernelUtilsSha1BlockInit(&ctx);

   bool contains_intr = false;

   for (uint32_t has_ended = 0; has_ended == 0; opnum ++, pc += isize){
      
      uint32_t op = _MMU_read32<PROCNUM, MMU_AT_CODE>(pc&imask);

      DynaCompiler fc = arm_instruction_compilers[INSTRUCTION_INDEX(op)];
      INSTR_R res = fc == 0 ? INTERPRET : fc(pc,op);

      has_ended = (instr_is_branch(op) /*&& res == INTERPRET*/) || (opnum >= 16);

      currentBlock.WriteOP = currentBlock.WriteOP || isARMWritingInstruction(op);
      currentBlock.MCROP = currentBlock.MCROP || is_mcr_mrc(op);

      if (res == INTERPRET) {
         currentBlock.addOP(OP_ITP, pc, -1, op, -1, -1, PRE_OP_NONE, instr_is_conditional(op) ? CONDITION(op) : -1);
         if (!has_ended) contains_intr = true;
      }
      

      sceKernelUtilsSha1BlockUpdate(&ctx, (u8*)&op, 4);
      
      if (has_ended && (!instr_does_prefetch(op) || res == INTERPRET)) //prefetch next instruction
         currentBlock.manualPrefetch = true;

      interpreted_cycles += op_decode[PROCNUM][false]() + instr_cycles(op);
   }

   sceKernelUtilsSha1BlockResult(&ctx, (u8*)digest);

	sprintf(currentBlock.block_hash,">:1:%02X:%08X:%08X:%08X:%08X:%08X",opnum, digest[0]
																			, digest[1]
																			, digest[2]
																			, digest[3]
																			, digest[4]);
   
   //#define save_hash
   #ifdef save_hash
      extern void WriteHash(char* msg);
      if (!contains_intr) WriteHash(currentBlock.block_hash);
   #endif
   //printf("Block hash: %s\n", currentBlock.block_hash);
}

template<int PROCNUM>
void build_ThumbBasicblock(){

   const u32 isize = 2;
   const uint32_t imask = 0xFFFFFFFE;

   for (uint32_t i = 0, has_ended = 0; has_ended == 0; i ++, pc += isize){

      uint32_t op = _MMU_read16<PROCNUM, MMU_AT_CODE>(pc&imask);
   
      DynaCompiler fc = thumb_instruction_compilers[op>>6];
      INSTR_R res = fc == 0 ? INTERPRET : fc(pc,op);

      if (res == INTERPRET)
         currentBlock.addOP(OP_ITP, pc, -1, op, -1, -1, PRE_OP_NONE, false);

      has_ended = instr_is_branch(op) || (i >= 64);
      
      if (has_ended && (!instr_does_prefetch(op) || res == INTERPRET)) //prefetch next instruction
         currentBlock.manualPrefetch = true;

      interpreted_cycles += op_decode[PROCNUM][true]() + instr_cycles(op);
   }
}

void checkAndDeleteLinkedBLock(u32 addr){

   /*auto it = codeCacheLinked[addr];

   if (it == 0) return;

   if (JIT_COMPILED_FUNC(it, ARM9) != 0 && JIT_COMPILED_FUNC(addr, ARM9) == 0){
      printf("Linked block deleted\n");
      JIT_COMPILED_FUNC(it, PROCNUM) = 0;
      codeCacheLinked[addr] = 0;
      codeCacheLinked[it] = 0;
   }*/


   /*if (it != 0  && *(u32*)JIT_COMPILED_FUNC(it, ARM9) != codeCacheLinkedByte[it]) {
      
      JIT_COMPILED_FUNC(addr, PROCNUM) = 0;
      codeCacheLinked[addr] = 0;
      codeCacheLinked[it] = 0;
      codeCacheLinkedByte[it] = 0;
   }*/
}

void test_jit_func(){
   const int PROCNUM = 1;

   printf("Start test\n");

   // store R0 R1 R2
   int R0 = ARMPROC.R[0];
   int R1 = ARMPROC.R[1];
   int R2 = ARMPROC.R[2];

   int _R0 = 5;
   int _R1 = 2;
   int _R2 = 13;

   // set R0 R1 R2
   ARMPROC.R[0] = _R0;
   ARMPROC.R[1] = _R1;
   ARMPROC.R[2] = _R2;

   base_adr = 0;

   int res = (_R1 + _R1);

   currentBlock.clearBlock(); 
   currentBlock.addOP(OP_ADD, pc, 0, 1, 1,  0, PRE_OP_LSL_IMM);
   currentBlock.addOP(OP_ADD, pc, 2, 2, 0,  1, PRE_OP_LSL_IMM);
   compile_basicblock<PROCNUM>();

   ArmOpCompiled f = (ArmOpCompiled)JIT_COMPILED_FUNC(base_adr, 1);
   f();

   printf("0x%x\n", f);
   printf("R0: %d %d\n", ARMPROC.R[0], res);

   currentBlock.clearBlock(); 

   // restore R0 R1 R2
   ARMPROC.R[0] = R0;
   ARMPROC.R[1] = R1;
   ARMPROC.R[2] = R2;   
   
}

template<int PROCNUM> u32 arm_jit_compile()
{
	block_procnum = PROCNUM;
   interpreted_cycles = 0;

   thumb = ARMPROC.CPSR.bits.T == 1;
   base_adr = ARMPROC.instruct_adr;
   pc = base_adr; 


   if (GetFreeSpace() < 16 * 1024){
      //printf("Dynarec code reset\n");
      arm_jit_reset(true,true);
   }

   currentBlock.clearBlock(); 

   /*ArmOpCompiled f = op_decode[PROCNUM][thumb];
		JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
		return f();*/

   
   currentBlock.start_addr = base_adr;
   /*if (generated_blocks[currentBlock.start_addr] > 7)
   {
      // Too many blocks generated with the same start address
      // Self-modifying code detected

      //printf("Self-modifying code detected\n");

      //generated_blocks.remove(currentBlock.start_addr);

      ArmOpCompiled f = op_decode[PROCNUM][thumb];
		JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
		return f();
   }*/

   generated_blocks[currentBlock.start_addr]++;

   if (!thumb) {
      build_ArmBasicblock<PROCNUM>(); 
      currentBlock.optimize_basicblock();
      /*ArmOpCompiled f = op_decode[PROCNUM][thumb];
		JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
		return f();*/
   }else{
      /*ArmOpCompiled f = op_decode[PROCNUM][thumb];
		JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
		return f();*/

      build_ThumbBasicblock<PROCNUM>();
      currentBlock.optimize_basicblockThumb();
   }
   
   //printf("Compiling...\n");
   return compile_basicblock<PROCNUM>();
}

template u32 arm_jit_compile<0>();
template u32 arm_jit_compile<1>();

void arm_jit_reset(bool enable, bool suppress_msg)
{
   if (!suppress_msg)
	   printf("CPU mode: %s\n", enable?"JIT":"Interpreter");

   saveBlockSizeJIT = my_config.DynarecBlockSize; //CommonSettings.jit_max_block_size;

   if (enable)
   {
      //printf("JIT: max block size %d instruction(s)\n", CommonSettings.jit_max_block_size);

      #define JITFREE(x) memset(x,0,sizeof(x));
         JITFREE(JIT.MAIN_MEM);
         JITFREE(JIT.SWIRAM);
         JITFREE(JIT.ARM9_ITCM);
         JITFREE(JIT.ARM9_LCDC);
         JITFREE(JIT.ARM9_BIOS);
      #undef JITFREE

      //memset(recompile_counts, 0, sizeof(recompile_counts));
      init_jit_mem();

     resetCodeCache();
   }
}

void arm_jit_close()
{
   resetCodeCache();
}