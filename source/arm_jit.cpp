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
#include "gfx3d.h"

#include "Disassembler.h"

#include <pspsuspend.h>

u32 saveBlockSizeJIT = 0;
uint32_t interpreted_cycles = 0;
uint32_t base_adr = 0;

bool full_block = false;

CACHE_ALIGN JIT_struct JIT;

uintptr_t *JIT_struct::JIT_MEM[0x4000] = {0};

// static u8 recompile_counts[(1<<26)/16];
#include <cstdint>

constexpr uint32_t GX_FIFO_NOP_CLEAR128[37] = {
    0xe3a01000,
    0xe3a02000,
    0xe3a03000,
    0xe3a0c000,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe880100e,
    0xe12fff1e,
};

constexpr uint32_t GX_FIFO_SEND48B[9] = {
    0xe8b0100c, 0xe881100c, 0xe8b0100c, 0xe881100c, 0xe8b0100c,
    0xe881100c, 0xe8b0100c, 0xe881100c, 0xe12fff1e};

constexpr uint32_t GX_FIFO_SEND64B[7] = {
    0xe92d01f0, 0xe8b011fc, 0xe88111fc, 0xe8b011fc,
    0xe88111fc, 0xe8bd01f0, 0xe12fff1e};

constexpr uint32_t GX_FIFO_SEND128B[11] = {
    0xe92d01f0, 0xe8b011fc, 0xe88111fc, 0xe8b011fc, 0xe88111fc,
    0xe8b011fc, 0xe88111fc, 0xe8b011fc, 0xe88111fc, 0xe8bd01f0, 0xe12fff1e};

constexpr uint32_t MI_CPU_CLEAR16[6] = {
    0xe3a03000, 0xe1530002, 0xb18100b3, 0xb2833002, 0xbafffffb, 0xe12fff1e};

constexpr uint32_t MI_CPU_CLEAR32[5] = {
    0xe081c002, 0xe151000c, 0xb8a10001, 0xbafffffc, 0xe12fff1e};

constexpr uint32_t MI_CPU_CLEARFAST[19] = {
    0xe92d03f0, 0xe0819002, 0xe1a0c2a2, 0xe081c28c, 0xe1a02000, 0xe1a03002, 0xe1a04002, 0xe1a05002,
    0xe1a06002, 0xe1a07002, 0xe1a08002, 0xe151000c, 0xb8a101fd, 0xbafffffc, 0xe1510009, 0xb8a10001,
    0xbafffffc, 0xe8bd03f0, 0xe12fff1e};

constexpr uint32_t MI_CPU_COPY16[7] = {
    0xe3a0c000, 0xe15c0002, 0xb19030bc, 0xb18130bc, 0xb28cc002, 0xbafffffa, 0xe12fff1e};

constexpr uint32_t MI_CPU_COPY32[6] = {
    0xe081c002, 0xe151000c, 0xb8b00004, 0xb8a10004, 0xbafffffb, 0xe12fff1e};

constexpr uint32_t MI_CPU_SEND32[6] = {
    0xe080c002, 0xe150000c, 0xb8b00004, 0xb5812000, 0xbafffffb, 0xe12fff1e};

constexpr uint32_t MI_CPU_FILL8[37] = {
    0xe3520000, 0x012fff1e, 0xe3100001, 0x0a000006, 0xe150c0b1, 0xe20cc0ff, 0xe18c3401, 0xe14030b1,
    0xe2800001, 0xe2522001, 0x012fff1e, 0xe3520002, 0x3a00000f, 0xe1811401, 0xe3100002, 0x0a000002,
    0xe0c010b2, 0xe2522002, 0x012fff1e, 0xe1811801, 0xe3d23003, 0x0a000004, 0xe0422003, 0xe083c000,
    0xe4801004, 0xe150000c, 0x3afffffc, 0xe3120002, 0x10c010b2, 0xe3120001, 0x012fff1e, 0xe1d030b0,
    0xe2033cff, 0xe20110ff, 0xe1811003, 0xe1c010b0, 0xe12fff1e};

constexpr uint32_t MI_COPY64B[11] = {
    0xe8b0100c, 0xe8a1100c, 0xe8b0100c, 0xe8a1100c, 0xe8b0100c,
    0xe8a1100c, 0xe8b0100c, 0xe8a1100c, 0xe890100d, 0xe8a1100d, 0xe12fff1e};

constexpr uint32_t CP_SAVE_CONTEXT[15] = {
    0xe59f1034, 0xe92d0010, 0xe891101c, 0xe8a0101c, 0xe151c1b0, 0xe2811028, 0xe891000c, 0xe8a0000c,
    0xe20cc003, 0xe15120b8, 0xe1c0c0b0, 0xe2022001, 0xe1c020b2, 0xe8bd0010, 0xe12fff1e};

constexpr uint32_t CP_RESTORE_CONTEXT[14] = {
    0xe92d0010, 0xe59f102c, 0xe890101c, 0xe881101c, 0xe1d021b8, 0xe1d031ba, 0xe14121b0,
    0xe1c132b0, 0xe2800010, 0xe2811028, 0xe890000c, 0xe881000c, 0xe8bd0010, 0xe12fff1e};

const uint32_t MICROCODE_SHAKEHAND[10] = {
    0xe1d120b0, 0xe1d030b0, 0xe2833001, 0xe1c030b0, 0xe1d1c0b0,
    0xe152000c, 0x0afffffa, 0xe2833001, 0xe1c030b0, 0xe12fff1e};

const uint32_t MICROCODE_WAIT_AGREEMENT[7] = {
    0xe1d020b0, 0xe1510002, 0x012fff1e, 0xe3a03010,
    0xe2533001, 0x1afffffd, 0xeafffff8};

struct Function
{
   const uint32_t *opcodes;
   size_t opcode_count;
   s32 cycles;
   const char *name;
   void (*hle_function)(u32); // extern "C" se serve ABI compatibile

   constexpr Function(
       const uint32_t *_opcodes,
       size_t _count,
       const char *_name,
       void (*_hle_function)(u32),
         s32 _cycles = 0
      ) : opcodes(_opcodes), opcode_count(_count), cycles(_cycles), name(_name), hle_function(_hle_function) {}

   // Equivalente di PartialEq<[InstInfo]> per test del pattern
   bool equals(const std::vector<opcode> &other) const
   {
      if (opcode_count != other.size())
         return false;
      for (size_t i = 0; i < opcode_count; ++i)
         if (opcodes[i] != other[i].bytes)
            return false;
      return true;
   }
};

// gp_regs = >R8

extern "C" void post_hle(u32 cycles = 1)
{
   uint32_t addr = NDS_ARM9.R[14];

   NDS_ARM9.CPSR.bits.T = BIT0(addr);
   NDS_ARM9.R[15] = addr;
   NDS_ARM9.next_instruction = NDS_ARM9.R[15];
   NDS_ARM9.instruct_adr = NDS_ARM9.R[15];

   // assign to v0 the return value of the HLE function, if any
   register u32 v0 asm("v0") = cycles; 
}

extern "C" void hle_mi_cpu_clear32(uint32_t guest_pc)
{
   /*
       let value = regs.gp_regs[0];
    let dst = regs.gp_regs[1];
    let len = regs.gp_regs[2] >> 2;

    if likely(len > 0) {
        asm.emu.mem_write_multiple_memset::<CPU, true, u32>(dst, value, len as usize);
    }

    hle_post_function::<CPU>(asm, 1 + len * 6 + 3, guest_pc);
   */

   uint32_t value = NDS_ARM9.R[0];
   uint32_t dst = NDS_ARM9.R[1];
   uint32_t len = NDS_ARM9.R[2] >> 2;

   if (len > 0)
   {
      for (uint32_t i = 0; i < len; ++i)
      {
         _MMU_ARM9_write32(dst + i * 4, value);
      }
   }

   register u32 v0 asm("v0") = 1 + len * 6 + 3; 
}

extern "C" void hle_mi_gx_fifo_send48b(u32 guest_pc)
{

   uint32_t src = NDS_ARM9.R[0];
   uint32_t dst = NDS_ARM9.R[1];

   uint32_t aligned_addr = src & ~0x3u;       // allineamento a 4 byte
   aligned_addr = aligned_addr & 0x0FFFFFFFu; // maschera a 28 bit

   for (int i = 0; i < 12; ++i)
   {

      uint32_t adr_dst = dst + i * 4;

      uint32_t val = _MMU_ARM9_read32(aligned_addr + i * 4);

      ((u32 *)(MMU.MMU_MEM[ARMCPU_ARM9][0x40]))[(adr_dst & 0xFFF) >> 2] = val;
      gfx3d_sendCommandToFIFO(val);
   }

   post_hle();
}

static const std::vector<Function> FUNCTIONS_ARM9 = {
    //{GX_FIFO_SEND48B, std::size(GX_FIFO_SEND48B), "GX_FIFO_SEND48B", hle_mi_gx_fifo_send48b},
      {MI_CPU_CLEAR32, std::size(MI_CPU_CLEAR32), "MI_CPU_CLEAR32", hle_mi_cpu_clear32, 0},
      /*{CP_SAVE_CONTEXT, std::size(CP_SAVE_CONTEXT), "CP_SAVE_CONTEXT", hle_mi_cpu_clear32},
      {CP_RESTORE_CONTEXT, std::size(CP_RESTORE_CONTEXT), "CP_RESTORE_CONTEXT", hle_mi_cpu_clear32}*/

};

/*

   unsafe extern "C" fn hle_microcode_shakehand(guest_pc: u32) {
 let asm = get_jit_asm_ptr::<{ ARM9 }>().as_mut_unchecked();
 hle_post_function::<{ ARM9 }>(asm, 20, guest_pc);
}

unsafe extern "C" fn hle_microcode_wait_agreement(guest_pc: u32) {
 let asm = get_jit_asm_ptr::<{ ARM9 }>().as_mut_unchecked();
 hle_post_function::<{ ARM9 }>(asm, 7, guest_pc);
}

*/

void hle_microcode_shakehand(uint32_t guest_pc)
{
   post_hle(20);
}

void hle_microcode_wait_agreement(uint32_t guest_pc)
{
   post_hle(7);
}

static constexpr std::array<Function, 2> MICROCODE_FUNCTIONS = {
    Function(MICROCODE_SHAKEHAND, std::size(MICROCODE_SHAKEHAND), "MICROCODE_SHAKEHAND", hle_microcode_shakehand, 20),
    Function(MICROCODE_WAIT_AGREEMENT, std::size(MICROCODE_WAIT_AGREEMENT), "MICROCODE_WAIT_AGREEMENT", hle_microcode_wait_agreement, 7),
};

static uintptr_t *JIT_MEM[32] = {
    // arm9
    /* 0X*/ DUP2(JIT.ARM9_ITCM),
    /* 1X*/ DUP2(JIT.ARM9_ITCM), // mirror
    /* 2X*/ DUP2(JIT.MAIN_MEM),
    /* 3X*/ DUP2(JIT.SWIRAM),
    /* 4X*/ DUP2(NULL),
    /* 5X*/ DUP2(NULL),
    /* 6X*/ NULL,
    JIT.ARM9_LCDC, // Plain ARM9-CPU Access (LCDC mode) (max 656KB)
    /* 7X*/ DUP2(NULL),
    /* 8X*/ DUP2(NULL),
    /* 9X*/ DUP2(NULL),
    /* AX*/ DUP2(NULL),
    /* BX*/ DUP2(NULL),
    /* CX*/ DUP2(NULL),
    /* DX*/ DUP2(NULL),
    /* EX*/ DUP2(NULL),
    /* FX*/ DUP2(JIT.ARM9_BIOS)};

static u32 JIT_MASK[32] = {
    // arm9
    /* 0X*/ DUP2(0x00007FFF),
    /* 1X*/ DUP2(0x00007FFF),
    /* 2X*/ DUP2(0x003FFFFF), // FIXME _MMU_MAIN_MEM_MASK
    /* 3X*/ DUP2(0x00007FFF),
    /* 4X*/ DUP2(0x00000000),
    /* 5X*/ DUP2(0x00000000),
    /* 6X*/ 0x00000000,
    0x000FFFFF,
    /* 7X*/ DUP2(0x00000000),
    /* 8X*/ DUP2(0x00000000),
    /* 9X*/ DUP2(0x00000000),
    /* AX*/ DUP2(0x00000000),
    /* BX*/ DUP2(0x00000000),
    /* CX*/ DUP2(0x00000000),
    /* DX*/ DUP2(0x00000000),
    /* EX*/ DUP2(0x00000000),
    /* FX*/ DUP2(0x00007FFF)};

static void init_jit_mem()
{
   static bool inited = false;

   if (inited)
      return;

   for (int i = 0; i < 0x4000; i++)
      JIT.JIT_MEM[i] = JIT_MEM[i >> 9] + (((i << 14) & JIT_MASK[i >> 9]) >> 1);

   

   inited = true;
   initCodeCache();
   currentBlock.init();
}

static bool thumb = false;
static uint32_t pc = 0;

static u32 instr_attributes(u32 opcode)
{
   return thumb ? thumb_attributes[opcode >> 6]
                : instruction_attributes[INSTRUCTION_INDEX(opcode)];
}

static bool instr_is_conditional(u32 opcode)
{
   if (thumb)
      return false;

   return !(CONDITION(opcode) == 0xE || (CONDITION(opcode) == 0xF && CODE(opcode) == 5));
}

static bool instr_is_branch(u32 opcode)
{
   u32 x = instr_attributes(opcode);
   if (thumb)
      return (x & BRANCH_ALWAYS) || ((x & BRANCH_POS0) && ((opcode & 7) | ((opcode >> 4) & 8)) == 15) || (x & BRANCH_SWI) || (x & JIT_BYPASS);
   else
      return (x & BRANCH_ALWAYS) || ((x & BRANCH_POS12) && REG_POS(opcode, 12) == 15) || ((x & BRANCH_LDM) && BIT15(opcode)) || (x & BRANCH_SWI) || (x & JIT_BYPASS);
}

static int instr_cycles(u32 opcode)
{
   u32 x = instr_attributes(opcode);
   u32 c = (x & INSTR_CYCLES_MASK);
   if (c == INSTR_CYCLES_VARIABLE)
   {
      if ((x & BRANCH_SWI))
         return 3;

      return 0;
   }
   if (instr_is_branch(opcode) && !(instr_attributes(opcode) & (BRANCH_ALWAYS | BRANCH_LDM)))
      c += 2;
   return c;
}

enum INSTR_R
{
   DYNAREC,
   DYNAREC_BRANCH,
   INTERPRET
};

typedef INSTR_R (*DynaCompiler)(uint32_t pc, uint32_t opcode);

#define disable_op(name, PREOP, ...) \
   static INSTR_R ARM_OP_##name##_##PREOP(uint32_t pc, const u32 i) { return INTERPRET; }

#define ARM_OP_REG_(name, PREOP, _rd, cond)                                                                                                                 \
   static INSTR_R ARM_OP_##name##_##PREOP(uint32_t pc, const u32 i)                                                                                         \
   {                                                                                                                                                        \
      if (instr_is_conditional(i) && !cond)                                                                                                                 \
         return INTERPRET;                                                                                                                                  \
      currentBlock.addOP(OP_##name, i, pc, _rd, REG_POS(i, 16), REG_POS(i, 0), REG_POS(i, 8), PRE_OP_##PREOP, instr_is_conditional(i) ? CONDITION(i) : -1); \
      return DYNAREC;                                                                                                                                       \
   }

#define ARM_OP_IMM_(name, PREOP, _rd, cond)                                                                                                                     \
   static INSTR_R ARM_OP_##name##_##PREOP(uint32_t pc, const u32 i)                                                                                             \
   {                                                                                                                                                            \
      if (instr_is_conditional(i) && !cond)                                                                                                                     \
         return INTERPRET;                                                                                                                                      \
      currentBlock.addOP(OP_##name, i, pc, _rd, REG_POS(i, 16), REG_POS(i, 0), ((i >> 7) & 0x1F), PRE_OP_##PREOP, instr_is_conditional(i) ? CONDITION(i) : -1); \
      return DYNAREC;                                                                                                                                           \
   }

#define ARM_OP_IMM(name, PREOP) ARM_OP_IMM_(name, PREOP, REG_POS(i, 12), true)
#define ARM_OP_REG(name, PREOP) ARM_OP_REG_(name, PREOP, REG_POS(i, 12), true)

#define ARM_OP_IMM_NC(name, PREOP) ARM_OP_IMM_(name, PREOP, REG_POS(i, 12), false)
#define ARM_OP_REG_NC(name, PREOP) ARM_OP_REG_(name, PREOP, REG_POS(i, 12), false)

#define ARM_OP_UNDEF(T)                                \
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
static INSTR_R ARM_OP_AND_IMM_VAL(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_AND, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
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
static INSTR_R ARM_OP_EOR_IMM_VAL(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_EOR, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
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
static INSTR_R ARM_OP_ORR_IMM_VAL(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ORR, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1);
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
static INSTR_R ARM_OP_ADD_IMM_VAL(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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
   currentBlock.addOP(OP_SUB, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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
   currentBlock.addOP(OP_AND, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ~ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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
   currentBlock.addOP(OP_RSB, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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

// TS3 crasha qui
static INSTR_R ARM_OP_MOV_LSL_IMM(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MOV, i, pc, REG_POS(i, 12), REG_POS(i, 16), REG_POS(i, 0), ((i >> 7) & 0x1F), PRE_OP_LSL_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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
   currentBlock.addOP(OP_MOV, i, pc, REG_POS(i, 12), -1, -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
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
   currentBlock.addOP(OP_MOV, i, pc, REG_POS(i, 12), -1, -1, ~ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   CMP
//-----------------------------------------------------------------------------

ARM_OP_IMM(TST, LSL_IMM)
ARM_OP_REG(TST, LSL_REG)
ARM_OP_IMM(TST, LSR_IMM)
ARM_OP_REG(TST, LSR_REG)
ARM_OP_IMM(TST, ASR_IMM)
ARM_OP_REG(TST, ASR_REG)
ARM_OP_IMM(TST, ROR_IMM)
ARM_OP_REG(TST, ROR_REG)
static INSTR_R ARM_OP_TST_IMM_VAL(uint32_t pc, const u32 i) // TS3 crasha qui
{
   if (!full_block)
      return INTERPRET;
   currentBlock.addOP(OP_TST, i, pc, i, REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
   return DYNAREC;
}

ARM_OP_IMM_NC(CMP, LSL_IMM)
ARM_OP_REG(CMP, LSL_REG)
ARM_OP_IMM(CMP, LSR_IMM)
ARM_OP_REG(CMP, LSR_REG)
ARM_OP_IMM(CMP, ASR_IMM)
ARM_OP_REG(CMP, ASR_REG)
ARM_OP_IMM(CMP, ROR_IMM)
ARM_OP_REG(CMP, ROR_REG)
static INSTR_R ARM_OP_CMP_IMM_VAL(uint32_t pc, const u32 i)
{
   /*if (instr_is_conditional(i))
   return INTERPRET; */

   if (!full_block)
      return INTERPRET;

   currentBlock.addOP(OP_CMP, i, pc, i, REG_POS(i, 16), -1, ROR((i & 0xFF), (i >> 7) & 0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);
   return DYNAREC;
}

ARM_OP_IMM(CMN, LSL_IMM)
ARM_OP_REG(CMN, LSL_REG)
ARM_OP_IMM(CMN, LSR_IMM)
ARM_OP_REG(CMN, LSR_REG)
ARM_OP_IMM(CMN, ASR_IMM)
ARM_OP_REG(CMN, ASR_REG)
ARM_OP_IMM(CMN, ROR_IMM)
ARM_OP_REG(CMN, ROR_REG)
static INSTR_R ARM_OP_CMN_IMM_VAL(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_CMN, i, pc, i, REG_POS(i,16), -1, ROR((i&0xFF), (i>>7)&0x1E), PRE_OP_IMM, instr_is_conditional(i) ? CONDITION(i) : -1,EXTFL_NONE);
   return DYNAREC;
}

// ARM_OP_UNDEF(CMP );
// ARM_OP_UNDEF(TST );

ARM_OP_UNDEF(AND_S);
ARM_OP_UNDEF(EOR_S);
ARM_OP_UNDEF(SUB_S);
ARM_OP_UNDEF(RSB_S);
ARM_OP_UNDEF(ADD_S);
ARM_OP_UNDEF(ADC_S);
ARM_OP_UNDEF(SBC_S);
ARM_OP_UNDEF(RSC_S);
ARM_OP_UNDEF(TEQ);
//ARM_OP_UNDEF(CMN);
ARM_OP_UNDEF(ORR_S);
ARM_OP_UNDEF(MOV_S);
ARM_OP_UNDEF(BIC_S);
ARM_OP_UNDEF(MVN_S);

static INSTR_R ARM_OP_MUL(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MUL, i, pc, REG_POS(i, 16), REG_POS(i, 0), REG_POS(i, 8), -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

static INSTR_R ARM_OP_MLA(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MLA, i, pc, REG_POS(i, 16), REG_POS(i, 0), REG_POS(i, 8), REG_POS(i, 12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

static INSTR_R ARM_OP_UMULL(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_UMUL, i, pc, REG_POS(i, 16), REG_POS(i, 0), REG_POS(i, 8), REG_POS(i, 12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

static INSTR_R ARM_OP_SMULL(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R ARM_OP_UMLAL(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_UMLA, i, pc, REG_POS(i, 16), REG_POS(i, 0), REG_POS(i, 8), REG_POS(i, 12), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

#define ARM_OP_MUL_S 0
#define ARM_OP_MLA_S 0
#define ARM_OP_MLA_S 0
#define ARM_OP_MUL_S 0

#define ARM_OP_UMULL_S 0
#define ARM_OP_UMLAL_S 0
#define ARM_OP_SMULL_S 0
#define ARM_OP_SMLAL 0
#define ARM_OP_SMLAL_S 0

#define ARM_OP_SMUL_B_B 0
#define ARM_OP_SMUL_T_B 0
#define ARM_OP_SMUL_B_T 0
#define ARM_OP_SMUL_T_T 0

#define ARM_OP_SMLA_B_B 0
#define ARM_OP_SMLA_T_B 0
#define ARM_OP_SMLA_B_T 0
#define ARM_OP_SMLA_T_T 0

#define ARM_OP_SMULW_B 0
#define ARM_OP_SMULW_T 0
#define ARM_OP_SMLAW_B 0
#define ARM_OP_SMLAW_T 0

#define ARM_OP_SMLAL_B_B 0
#define ARM_OP_SMLAL_T_B 0
#define ARM_OP_SMLAL_B_T 0
#define ARM_OP_SMLAL_T_T 0

#define ARM_OP_QADD 0
#define ARM_OP_QSUB 0
#define ARM_OP_QDADD 0
#define ARM_OP_QDSUB 0

// #define ARM_OP_CLZ         0
static INSTR_R ARM_OP_CLZ(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_CLZ, i, pc, REG_POS(i, 12), REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

inline bool isMainMemory(u32 addr)
{
   return ((addr & 0x0F000000) == 0x02000000) && !((addr & (~0x3FFF)) == MMU.DTCMRegion);
}

inline bool is3DCMD(u32 addr)
{
   addr = addr >> 4;
   return (addr >= 0x400044 && addr <= 0x40005C);
}

inline bool is3DFIFO(u32 addr)
{
   addr = addr >> 4;
   return (addr >= 0x400040 && addr <= 0x400043);
}

inline bool isDMA(u32 addr)
{
   return MMU_new.is_dma(addr);
}

#define ARM_MEM_OP_DEF2(T, Q)                            \
   static const DynaCompiler ARM_OP_##T##_M_LSL_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_LSL_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_LSR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_LSR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_ASR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_ASR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_ROR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_P_ROR_##Q = 0; \
   static const DynaCompiler ARM_OP_##T##_M_##Q = 0;     \
   static const DynaCompiler ARM_OP_##T##_P_##Q = 0

#define ARM_MEM_OP_DEF(T)              \
   ARM_MEM_OP_DEF2(T, IMM_OFF_PREIND); \
   ARM_MEM_OP_DEF2(T, IMM_OFF);        \
   ARM_MEM_OP_DEF2(T, IMM_OFF_POSTIND)

ARM_MEM_OP_DEF(STRB);
ARM_MEM_OP_DEF(LDRB);

// Helpers to choose positive or negative offset:
#define POS(x) (x)
#define NEG(x) (-(x))

#define GEN_ARM_STR_OP_FUNC(Name, MODE, VAL)                                                                                                                \
   static INSTR_R Name(uint32_t pc, const u32 i)                                                                                                            \
   {                                                                                                                                                        \
      currentBlock.WriteOP = true;                                                                                                                          \
      u32 val = get_addr(_ARMPROC.R[REG_POS(i, 16)], VAL, MODE, i);                                                                                         \
      /*if (is3DCMD(val))                                                                                                                                   \
      {                                                                                                                                                     \
         currentBlock.addOP(OP_3D_CMD, i, pc, -1, REG_POS(i, 12), -1, val, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);           \
      }                                                                                                                                                     \
      else if (is3DFIFO(val))                                                                                                                               \
      {                                                                                                                                                     \
         currentBlock.addOP(OP_3D_FIFO, i, pc, -1, REG_POS(i, 12), -1, val, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);          \
      }                                                                                                                                                     \
      else if (isDMA(val))                                                                                                                                  \
      {                                                                                                                                                     \
         currentBlock.addOP(OP_DMA, i, pc, -1, REG_POS(i, 12), REG_POS(i, 16), VAL, (opType)MODE, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE); \
      }                                                                                                                                                     \
      else*/                                                                                                                                                \
      {                                                                                                                                                     \
         currentBlock.addOP(OP_STR, i, pc, REG_POS(i, 16), REG_POS(i, 12), REG_POS(i, 0),                                                                   \
                            VAL,                                                                                                                            \
                            (opType)MODE,                                                                                                                   \
                            instr_is_conditional(i) ? CONDITION(i) : -1,                                                                                    \
                            isMainMemory(val) ? EXTFL_DIRECTMEMACCESS : EXTFL_NONE);                                                                        \
      }                                                                                                                                                     \
      return DYNAREC;                                                                                                                                       \
   }

u32 get_addr(u32 addr, s32 shift_op, u32 type, u32 i)
{
   u32 sign = 1;

   if ((type & 0xfff) == PRE_OP_IMM_POST_M || (type & 0xfff) == PRE_OP_IMM_POST_P)
      return addr;
   if (type == 1)
      return addr + shift_op;

   shift_op = shift_op < 0 ? -shift_op : shift_op;

   if ((type & 0xfff) == PRE_OP_IMM_PRE_M)
      sign = -1;

   switch (type >> 16)
   {
   case PRE_OP_LSL_IMM:
      return addr + (sign * (_ARMPROC.R[REG_POS(i, 0)] << shift_op));
   case PRE_OP_LSR_IMM:
      return (shift_op != 0) ? addr + (sign * (_ARMPROC.R[REG_POS(i, 0)] >> shift_op)) : 0;
   case PRE_OP_ASR_IMM:
   {
      if (shift_op == 0)
         return addr + (sign * BIT31(_ARMPROC.R[REG_POS(i, 0)]) * 0xFFFFFFFF);
      else
         return addr + (sign * (u32)((s32)_ARMPROC.R[REG_POS(i, 0)] >> shift_op));
   }
   case PRE_OP_ROR_IMM:
      return (shift_op != 0) ? addr + (sign * shift_op) : 0;
   default:
      return 0;
   }
}

#define GEN_ARM_LDR_OP_FUNC(Name, MODE, VAL)                                           \
   static INSTR_R Name(uint32_t pc, const u32 i)                                       \
   {                                                                                   \
      if (!full_block || (MODE != PRE_OP_IMM && MODE != PRE_OP_IMM_PRE_P && MODE != PRE_OP_IMM_PRE_M && MODE != PRE_OP_IMM_POST_P && MODE != PRE_OP_IMM_POST_M))                                                                 \
         return INTERPRET;                                                             \
      interpreted_cycles += 2;                                                         \
      u32 val = get_addr(_ARMPROC.R[REG_POS(i, 16)], VAL, MODE, i);                    \
      currentBlock.addOP(OP_LDR, i, pc, REG_POS(i, 12), REG_POS(i, 16), REG_POS(i, 0), \
                         VAL,                                                          \
                         (opType)MODE,                                                 \
                         instr_is_conditional(i) ? CONDITION(i) : -1,                  \
                         isMainMemory(val) ? EXTFL_DIRECTMEMACCESS : EXTFL_NONE);      \
      return DYNAREC;                                                                  \
   }

#define CONCAT(a, b) a##b
#define EXPAND_AND_CONCAT(a, b) CONCAT(a, b)

#define gen_ldr_sub(G, TP, TM)                                                                                         \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_P_, G), (TP), POS((i) & 0xFFF))                                    \
   GEN_ARM_LDR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_LDR_M_, G), (TM), NEG((i) & 0xFFF))

#define gen_ldr()
gen_ldr_sub(IMM_OFF_PREIND, PRE_OP_IMM_PRE_P, PRE_OP_IMM_PRE_M)
    gen_ldr_sub(IMM_OFF_POSTIND, PRE_OP_IMM_POST_P, PRE_OP_IMM_POST_M)
        gen_ldr_sub(IMM_OFF, 1, 1)

#define gen_str_sub(G, TP, TM)                                                                                         \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_LSL_, G), ((PRE_OP_LSL_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_LSR_, G), ((PRE_OP_LSR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_ASR_, G), ((PRE_OP_ASR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TP), POS(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_ROR_, G), ((PRE_OP_ROR_IMM << 16) | TM), NEG(((i >> 7) & 0x1F))) \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_P_, G), (TP), POS((i) & 0xFFF))                                    \
   GEN_ARM_STR_OP_FUNC(EXPAND_AND_CONCAT(ARM_OP_STR_M_, G), (TM), NEG((i) & 0xFFF))

#define gen_str()
            gen_str_sub(IMM_OFF_PREIND, PRE_OP_IMM_PRE_P, PRE_OP_IMM_PRE_M)
                gen_str_sub(IMM_OFF_POSTIND, PRE_OP_IMM_POST_P, PRE_OP_IMM_POST_M)
                    gen_str_sub(IMM_OFF, 1, 1)

                        gen_str()
                            gen_ldr()

#define DEFINE_ARM_OP_LDR(NAME, OP_TYPE, PRE_OP, IMM, FLAG)                                                                                                               \
   static INSTR_R NAME(uint32_t pc, const u32 i)                                                                                                                          \
   {                                                                                                                                                                      \
      if (full_block || (PRE_OP == PRE_OP_IMM || PRE_OP == PRE_OP_IMM_PRE_P || PRE_OP == PRE_OP_IMM_PRE_M || PRE_OP == PRE_OP_IMM_POST_P || PRE_OP == PRE_OP_IMM_POST_M)) \
      {                                                                                                                                                                   \
         u32 val = get_addr(_ARMPROC.R[REG_POS(i, 16)], IMM, PRE_OP, i);                                                                                                  \
         currentBlock.addOP(OP_TYPE, i, pc, REG_POS(i, 12), REG_POS(i, 16), -1,                                                                                           \
                            IMM, PRE_OP,                                                                                                                                  \
                            instr_is_conditional(i) ? CONDITION(i) : -1, /*isMainMemory(val) ? EXTFL_DIRECTMEMACCESS :*/ FLAG);                                           \
         return DYNAREC;                                                                                                                                                  \
      }                                                                                                                                                                   \
      else                                                                                                                                                                \
      {                                                                                                                                                                   \
         return INTERPRET;                                                                                                                                                \
      }                                                                                                                                                                   \
   }

#define DEFINE_ARM_OP_STR(NAME, OP_TYPE, PRE_OP, IMM, FLAG)                                                                                                    \
   static INSTR_R NAME(uint32_t pc, const u32 i)                                                                                                               \
   {                                                                                                                                                           \
      currentBlock.WriteOP = true;                                                                                                                             \
      u32 val = get_addr(_ARMPROC.R[REG_POS(i, 16)], IMM, PRE_OP, i);                                                                                          \
      if (!full_block)                                                                                                                                         \
         return INTERPRET;                                                                                                                                     \
      if (is3DCMD(val))                                                                                                                                        \
      {                                                                                                                                                        \
         currentBlock.addOP(OP_3D_CMD, i, pc, -1, REG_POS(i, 12), -1, val, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);              \
         return DYNAREC;                                                                                                                                       \
      }                                                                                                                                                        \
      else if (is3DFIFO(val))                                                                                                                                  \
      {                                                                                                                                                        \
         currentBlock.addOP(OP_3D_FIFO, i, pc, -1, REG_POS(i, 12), -1, val, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1, EXTFL_NONE);             \
         return DYNAREC;                                                                                                                                       \
      }                                                                                                                                                        \
      else if (PRE_OP == PRE_OP_IMM || PRE_OP == PRE_OP_IMM_PRE_P || PRE_OP == PRE_OP_IMM_PRE_M || PRE_OP == PRE_OP_IMM_POST_P || PRE_OP == PRE_OP_IMM_POST_M) \
      {                                                                                                                                                        \
         u32 val = get_addr(_ARMPROC.R[REG_POS(i, 16)], IMM, PRE_OP, i);                                                                                       \
         currentBlock.addOP(OP_TYPE, i, pc, REG_POS(i, 16), REG_POS(i, 12), -1,                                                                                \
                            IMM, PRE_OP,                                                                                                                       \
                            instr_is_conditional(i) ? CONDITION(i) : -1, /*isMainMemory(val) ? EXTFL_DIRECTMEMACCESS :*/ FLAG);                                \
         interpreted_cycles += 2;                                                                                                                              \
         return DYNAREC;                                                                                                                                       \
      }                                                                                                                                                        \
      else                                                                                                                                                     \
      {                                                                                                                                                        \
         return INTERPRET;                                                                                                                                     \
      }                                                                                                                                                        \
   }

#define DEFINE_ARM_OP_STR_HB(OP_TYPE, IMM, FLAG)                                                 \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_P_IMM_OFF, OP_TYPE, PRE_OP_IMM, IMM, FLAG)                  \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_M_IMM_OFF, OP_TYPE, PRE_OP_IMM, -IMM, FLAG)                 \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_P_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG)                   \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_M_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG)                   \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_P, IMM, FLAG)   \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_M, -IMM, FLAG)  \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG)        \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_PRE_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)       \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_P, IMM, FLAG)  \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_M, -IMM, FLAG) \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG)        \
   DEFINE_ARM_OP_STR(ARM_##OP_TYPE##_POS_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)

#define DEFINE_ARM_OP_LDR_HB(OP_TYPE, IMM, FLAG)                                                 \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_P_IMM_OFF, OP_TYPE, PRE_OP_IMM, IMM, FLAG)                  \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_M_IMM_OFF, OP_TYPE, PRE_OP_IMM, -IMM, FLAG)                 \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_P_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG)                   \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_M_REG_OFF, OP_TYPE, PRE_OP_NONE, 0, FLAG)                   \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_P, IMM, FLAG)   \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_PRE_M, -IMM, FLAG)  \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG)        \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_PRE_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)       \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_P_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_P, IMM, FLAG)  \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_M_IMM_OFF, OP_TYPE, PRE_OP_IMM_POST_M, -IMM, FLAG) \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_P_REG_OFF, OP_TYPE, PRE_OP_NONE, IMM, FLAG)        \
   DEFINE_ARM_OP_LDR(ARM_##OP_TYPE##_POS_INDE_M_REG_OFF, OP_TYPE, PRE_OP_NONE, -IMM, FLAG)

                                DEFINE_ARM_OP_STR_HB(OP_STRH, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)
                                    DEFINE_ARM_OP_LDR_HB(OP_LDRH, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)
                                        DEFINE_ARM_OP_LDR_HB(OP_LDRSB, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)
                                            DEFINE_ARM_OP_LDR_HB(OP_LDRSH, (((i >> 4) & 0xF0) + (i & 0xF)), EXTFL_NONE)

#define SIGNEXTEND_24(i) (((s32)i << 8) >> 8)

                                                static INSTR_R ARM_OP_B(uint32_t pc, const u32 i)
{

   return INTERPRET;

   if (CONDITION(i) == 0xF || instr_is_conditional(i) || NDS_ARM9.CPSR.bits.T == 1)
   {
   }

   currentBlock.JumpOP = true;

   u32 off = SIGNEXTEND_24(i);

   if (currentBlock.branch_addr == currentBlock.start_addr)
      printf("WARNING: B to self\n");

   currentBlock.addOP(OP_BC, i, pc, -1, -1, -1, (off << 2), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);

   return DYNAREC;
}

static INSTR_R ARM_OP_BL(uint32_t pc, const u32 i)
{

   return INTERPRET;
   if (CONDITION(i) == 0xF || instr_is_conditional(i) || NDS_ARM9.CPSR.bits.T == 1)
   {
   }
   currentBlock.JumpOP = true;

   u32 off = SIGNEXTEND_24(i);

   if (currentBlock.branch_addr == currentBlock.start_addr)
      printf("WARNING: B to self\n");

   currentBlock.addOP(OP_BLC, i, pc, -1, -1, -1, (off << 2), PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);

   return DYNAREC;
}

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

#define _ARMPROC (block_procnum ? NDS_ARM7 : NDS_ARM9)

static INSTR_R ARM_OP_SWP(uint32_t pc, const u32 i) { return INTERPRET; };
static INSTR_R ARM_OP_SWPB(uint32_t pc, const u32 i) { return INTERPRET; };

bool isHaltHackInstruction(u32 i)
{
   const u32 cp15_reg = (REG_POS(i,16)<<16) | (REG_POS(i,0)<<8) | ((i>>5)&0x7);
	return (cp15_reg == 0x070004 || cp15_reg == 0x070802);
}


static INSTR_R ARM_OP_MCR(uint32_t pc, const u32 i)
{
   if (isHaltHackInstruction(i))
   {
      currentBlock.addOP(OP_HALT_HACK, i, pc, REG_POS(i, 12), -1, -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      return DYNAREC;
   }

   currentBlock.MCROP = true;
   return INTERPRET;
}
static INSTR_R ARM_OP_MRC(uint32_t pc, const u32 i)
{
   if (isHaltHackInstruction(i))
   {
      currentBlock.addOP(OP_HALT_HACK, i, pc, REG_POS(i, 12), -1, -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      return DYNAREC;
   }

   currentBlock.MCROP = true;
   return INTERPRET;
}

static INSTR_R ARM_OP_SWI(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SWI, i, pc, -1, ((i >> 16) & 0x1F), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

bool abc = false;

static INSTR_R ARM_OP_BX(uint32_t pc, const u32 i)
{
   // u32 tmp = _ARMPROC.R[REG_POS(i, 0)];
   // currentBlock.branch_addr = tmp & (0xFFFFFFFC|(BIT0(tmp)<<1));

   // if (currentBlock.branch_addr == currentBlock.start_addr) printf("WARNING: BX to self\n");

   // ArmOpCompiled f = (ArmOpCompiled)JIT_COMPILED_FUNC(currentBlock.branch_addr, ARM9);

   // if (f && codeCacheLinked[currentBlock.branch_addr] == 0 && codeCacheLinked[currentBlock.start_addr] == 0)
   /*if (currentBlock.branch_addr == currentBlock.start_addr && !codeCacheLinked[currentBlock.branch_addr] && !BIT0(tmp))
   {
      //printf("BX to its self\n");
      codeCacheLinked[currentBlock.branch_addr] = currentBlock.start_addr;
      currentBlock.addOP(OP_BXC, i, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      //currentBlock.addOP(OP_BXC, i, pc, interpreted_cycles, -1, -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
      return DYNAREC_BRANCH;
   }*/

   /*currentBlock.addOP(OP_BXC, i, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC_BRANCH;*/
   return INTERPRET;
   currentBlock.JumpOP = true;
   currentBlock.addOP(OP_BXC, i, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

static INSTR_R ARM_OP_BLX_REG(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.JumpOP = true;
   currentBlock.addOP(OP_BXRC, i, pc, -1, REG_POS(i, 0), -1, -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   LDRD / STRD
//-----------------------------------------------------------------------------

static INSTR_R ARM_OP_LDRD_STRD_POST_INDEX(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R ARM_OP_STMIA(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_STMIA, i, pc, -1, i, REG_POS(i, 16), -1, PRE_OP_NONE, instr_is_conditional(i) ? CONDITION(i) : -1);
   return DYNAREC;
}

#define ARM_OP_LDRD_STRD_OFFSET_PRE_INDEX 0
#define ARM_OP_MSR_CPSR 0
// #define ARM_OP_BX 0
// #define ARM_OP_BLX_REG 0
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
// #define ARM_OP_STMIA 0
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
   currentBlock.addOP(OP_MOV, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
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
   currentBlock.addOP(OP_LSR_0, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

static INSTR_R THUMB_OP_LSR(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_MOV_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MOV, i, pc, _REG_NUM(i, 8), -1, -1, i & 0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, i, pc, _REG_NUM(i, 8), _REG_NUM(i, 8), -1, i & 0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_IMM3(uint32_t pc, const u32 i)
{
   u32 imm = (i >> 6) & 0x07;
   if (imm == 0)
      currentBlock.addOP(OP_MOV, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   else
      currentBlock.addOP(OP_ADD, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, imm, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6));
   return DYNAREC;
}

static INSTR_R THUMB_OP_SUB_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SUB, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6));
   return DYNAREC;
}

static INSTR_R THUMB_OP_CMP_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_CMP, i, pc, -1, _REG_NUM(i, 8), -1, i & 0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_SUB_IMM8(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_SUB, i, pc, _REG_NUM(i, 8), _REG_NUM(i, 8), -1, i & 0xff, PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_SUB_IMM3(uint32_t pc, const u32 i)
{
   u32 imm = (i >> 6) & 0x07;
   currentBlock.addOP(OP_SUB, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, imm, PRE_OP_IMM);
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   AND
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_AND(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_AND, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
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
   currentBlock.addOP(OP_NEG, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   EOR
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_EOR(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_EOR, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   MVN
//-----------------------------------------------------------------------------

static INSTR_R THUMB_OP_MVN(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MVN, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

static INSTR_R THUMB_OP_ORR(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ORR, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

//-----------------------------------------------------------------------------
//   TST
//-----------------------------------------------------------------------------
static INSTR_R THUMB_OP_TST(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_TST, i, pc, -1, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

static INSTR_R THUMB_OP_CMP(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_CMP, i, pc, -1, _REG_NUM(i, 0), _REG_NUM(i, 3));
   return DYNAREC;
}

static INSTR_R THUMB_OP_ROR_REG(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_MOV_SPE(uint32_t pc, const u32 i)
{
   u32 Rd = _REG_NUM(i, 0) | ((i >> 4) & 8);

   if (Rd == 15)
        return INTERPRET;

   currentBlock.addOP(OP_MOV, i, pc, Rd, REG_POS(i, 3));
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_SPE(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_MUL_REG(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_MUL, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 0), _REG_NUM(i, 3));
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
#define SIGNEEXT_IMM11(i) (((i) & 0x7FF) | (BIT10(i) * 0xFFFFF800))
   currentBlock.addOP(OP_BXC, i, pc, -1, -1, -1, (SIGNEEXT_IMM11(i) << 1), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADJUST_P_SP(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, i, pc, 13, 13, -1, ((i & 0x7F) << 2), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADJUST_M_SP(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_ADD, i, pc, 13, 13, -1, -((i & 0x7F) << 2), PRE_OP_IMM, EXTFL_NOFLAGS);
   return DYNAREC;
}

static INSTR_R THUMB_OP_ADD_2PC(uint32_t pc, const u32 i)
{
   return INTERPRET;
}

static INSTR_R THUMB_OP_ADD_2SP(uint32_t pc, const u32 i)
{
   return INTERPRET;
   currentBlock.addOP(OP_ADD, i, pc, _REG_NUM(i, 8), 13, -1, ((i & 0xFF) << 2), PRE_OP_IMM, EXTFL_NOFLAGS);
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
   currentBlock.addOP(OP_SWI, i, pc, -1, i & 0x1F);
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
   currentBlock.addOP(OP_STRH, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), _REG_NUM(i, 6), 0, PRE_OP_REG, -2);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDRH_REG_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + _ARMPROC.R[_REG_NUM(i, 6)];

   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_LDRH, i, pc, _REG_NUM(i,0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG, -1, EXTFL_DIRECTMEMACCESS);
   else*/
   currentBlock.addOP(OP_LDRH, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG);

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
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i >> 5) & 0x3E);

   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_STRH, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>5)&0x3E), PRE_OP_IMM, -2, EXTFL_DIRECTMEMACCESS);
   else*/
   currentBlock.addOP(OP_STRH, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i >> 5) & 0x3E), PRE_OP_IMM, -2);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDRH_IMM_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i >> 5) & 0x3E);

   currentBlock.addOP(OP_LDRH, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, ((i >> 5) & 0x3E), PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_STR_IMM_OFF(uint32_t pc, const u32 i)
{
   u32 adr = _ARMPROC.R[_REG_NUM(i, 3)] + ((i >> 4) & 0x7C);

   /*if (isMainMemory(adr))
      currentBlock.addOP(OP_STR, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i>>4)&0x7C), PRE_OP_IMM, -1, EXTFL_DIRECTMEMACCESS);
   else*/
   currentBlock.addOP(OP_STR, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), -1, ((i >> 4) & 0x7C), PRE_OP_IMM);
   return DYNAREC;
}

static INSTR_R THUMB_OP_STR_REG_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_STR, i, pc, _REG_NUM(i, 3), _REG_NUM(i, 0), _REG_NUM(i, 6), -1, PRE_OP_REG);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDR_REG_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_LDR, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), _REG_NUM(i, 6), -1, PRE_OP_REG);
   return DYNAREC;
}

static INSTR_R THUMB_OP_LDR_IMM_OFF(uint32_t pc, const u32 i)
{
   currentBlock.addOP(OP_LDR, i, pc, _REG_NUM(i, 0), _REG_NUM(i, 3), -1, ((i >> 4) & 0x7C), PRE_OP_IMM);
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

#define THUMB_OP_INTERPRET 0

#define THUMB_OP_ASR THUMB_OP_INTERPRET

#define THUMB_OP_UND_THUMB THUMB_OP_INTERPRET

#define THUMB_OP_ASR_0 THUMB_OP_INTERPRET

#define THUMB_OP_LSL_REG THUMB_OP_INTERPRET
#define THUMB_OP_LSR_REG THUMB_OP_INTERPRET
#define THUMB_OP_ASR_REG THUMB_OP_INTERPRET
#define THUMB_OP_ADC_REG THUMB_OP_INTERPRET
#define THUMB_OP_SBC_REG THUMB_OP_INTERPRET
#define THUMB_OP_ROR_REG THUMB_OP_INTERPRET

#define THUMB_OP_LDR_SPREL THUMB_OP_INTERPRET
#define THUMB_OP_STR_SPREL THUMB_OP_INTERPRET
#define THUMB_OP_LDR_PCREL THUMB_OP_INTERPRET

#define THUMB_OP_LDRSB_REG_OFF THUMB_OP_INTERPRET
#define THUMB_OP_LDRSH_REG_OFF THUMB_OP_INTERPRET

// UNDEFINED OPS
#define THUMB_OP_PUSH_LR THUMB_OP_INTERPRET
#define THUMB_OP_BKPT_THUMB THUMB_OP_INTERPRET

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

template <int PROCNUM, int thumb>
static u32 FASTCALL OP_DECODE()
{
   u32 cycles;
   u32 adr = ARMPROC.instruct_adr;
   if (thumb)
   {
      ARMPROC.next_instruction = adr + 2;
      ARMPROC.R[15] = adr + 4;
      u32 opcode = _MMU_read16<PROCNUM, MMU_AT_CODE>(adr);
      cycles = thumb_instructions_set[PROCNUM][opcode >> 6](opcode);
   }
   else
   {
      ARMPROC.next_instruction = adr + 4;
      ARMPROC.R[15] = adr + 8;
      u32 opcode = _MMU_read32<PROCNUM, MMU_AT_CODE>(adr);
      if (CONDITION(opcode) == 0xE || TEST_COND(CONDITION(opcode), CODE(opcode), ARMPROC.CPSR))
         cycles = arm_instructions_set[PROCNUM][INSTRUCTION_INDEX(opcode)](opcode);
      else
         cycles = 1;
   }
   ARMPROC.instruct_adr = ARMPROC.next_instruction;
   ARMPROC.idle_loop = false;
   return cycles;
}

static const ArmOpCompiled op_decode[2][2] = {OP_DECODE<0, 0>, OP_DECODE<0, 1>, OP_DECODE<1, 0>, OP_DECODE<1, 1>};

bool instr_does_prefetch(u32 opcode)
{
   u32 x = instr_attributes(opcode);
   if (thumb)
      return thumb_instruction_compilers[opcode >> 6] && (x & BRANCH_ALWAYS);
   else
      return instr_is_branch(opcode) && arm_instruction_compilers[INSTRUCTION_INDEX(opcode)] && ((x & BRANCH_ALWAYS) || (x & BRANCH_LDM));
}

//-----------------------------------------------------------------------------
//   Compiler
//-----------------------------------------------------------------------------

bool compiledHLE(uint32_t pc, bool thumb)
{
   if (thumb)
      return false;

   const std::vector<Function> *functions = &FUNCTIONS_ARM9;

   for (const auto &func : *functions)
   {
      if (func.equals(currentBlock.opcodes))
      {
         printf("[JIT] %s found at 0x%08X, psp equivalent: 0x%X (CPU=%s)\n",
                func.name,
                currentBlock.start_addr,
                emit_getCurrAdr(),
                "ARM9");

         emit_jal(func.hle_function);
         emit_nop();

         return true;
      }
   }

   return false;
}

void print_regs()
{
   for (int i = 0; i < 16; i++)
   {
      printf("R%d: %08X\n", i, NDS_ARM9.R[i]);
   }
   printf("CPSR: %08X\n", NDS_ARM9.CPSR.val);
}


int executed_cycles = 0;
int continue_cpu_exec(u32 cycles)
{
   extern s32 s32next;
   extern s32 arm9;

   executed_cycles += cycles;

    if ((arm9 + executed_cycles) > s32next || NDS_ReschedulePtr == 1){
      const int tmp = executed_cycles;
      executed_cycles = 0;
      return tmp;
    }
    
	if (!(NDS_ARM9.freeze & CPU_FREEZE_IRQ_IE_IF) && !nds.freezeBus){
        ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(NDS_ARM9.instruct_adr, ARM9);

		if (code_block)
         return code_block();

      const int tmp = executed_cycles;
      executed_cycles = 0;
      
      if (GetFreeSpace() < 4 * 1024)
         return tmp;

      return tmp + arm_jit_compile<ARM9>();
    }

   const int tmp = executed_cycles;
   executed_cycles = 0;
   return tmp;
}

u32 pre_hle_block_emit()
{
   void *code_ptr = emit_GetPtr();
   emit_mpush(1, reg_gpr + psp_ra);

   return (u32)code_ptr;
}

void post_hle_block_emit(u32 block_start_addr, u32 base_adr, u32 interpreted_cycles)
{
   // Typically we need to return to dispatcher:
   emit_jal(continue_cpu_exec);
   emit_move(psp_a0, psp_v0); // Arbitrary low cycle count
   emit_mpop(1, reg_gpr + psp_ra);
   emit_jra();
   emit_movi(psp_v1, 0); // Not idle

   make_address_range_executable(block_start_addr, (u32)emit_GetPtr());
   JIT_COMPILED_FUNC(base_adr, ARM9) = (uintptr_t)block_start_addr;
}



bool first_time = true;
template <int PROCNUM>
void compile_basicblock(bool interpret_only = false)
{
   uint32_t opcode = 0;

   void *code_ptr = emit_GetPtr();

   const bool isIdle = interpret_only ? false : currentBlock.isIdleLoop(thumb);

   emit_mpush(1, reg_gpr + psp_ra);

   // StartCodeDump();

   // const bool hle_func = compiledHLE(base_adr, thumb);

   if (!interpret_only){
      if (thumb)
      {
         currentBlock.emitThumbBlock<PROCNUM>();
      }
      else // if (!hle_func)
      {
         currentBlock.emitArmBlock<PROCNUM>();
      }

      if ((currentBlock.manualPrefetch || currentBlock.JumpOP))
      {
         emit_lw(psp_at, RCPU, _next_instr);
         emit_sw(psp_at, RCPU, _instr_adr);

      }
      
      emit_jal(continue_cpu_exec);
      emit_movi(psp_a0, interpreted_cycles);
   }else {
      ArmOpCompiled f = op_decode[PROCNUM][thumb];
      emit_jal(f);
      emit_nop();
   }

   emit_mpop(1, reg_gpr + psp_ra);

   emit_jra();
   emit_movi(psp_v1, isIdle ? 1 : 0);

   make_address_range_executable((u32)code_ptr, (u32)emit_GetPtr());
   JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)code_ptr;

   // Align the code to 4 bytes
   while (emit_getCurrAdr() & 0x3)
      emit_nop();
}

#define _SHA1_DIGEST_LENGTH 5

inline bool is_ldr(uint32_t opcode)
{
   return ((opcode & 0x0E500000) == 0x04100000);
}

inline bool is_lhu(uint32_t opcode)
{
   return ((opcode & 0x0E700000) == 0x08500000);
}

inline bool is_lbu(uint32_t opcode)
{
   return ((opcode & 0x0E700000) == 0x08700000);
}

inline bool is_str(uint32_t opcode)
{
   return ((opcode & 0x0E500000) == 0x04000000);
}

inline bool is_sh(uint32_t opcode)
{
   return ((opcode & 0x0E700000) == 0x08400000);
}

inline bool is_sb(uint32_t opcode)
{
   return ((opcode & 0x0E700000) == 0x08600000);
}

// Check if the opcode is a B (Branch) instruction
inline bool is_b(uint32_t opcode)
{
   // Match the pattern: cond 1010 (B) with link bit 0
   return ((opcode & 0x0F000000) == 0x0A000000);
}

// Check if the opcode is a BL (Branch with Link) instruction
inline bool is_bl(uint32_t opcode)
{
   // Match the pattern: cond 1011 (BL) with link bit 1
   return ((opcode & 0x0F000000) == 0x0B000000);
}

// Check if the opcode is a BX (Branch Exchange) instruction
inline bool is_bx(uint32_t opcode)
{
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

inline bool is_mcr_mrc(uint32_t opcode)
{
   return (opcode & 0x0F000010) == 0x0E000000;
}

template <int PROCNUM>
void build_ArmBasicblock(uint16_t max_opcodes = 128, bool include_branches = false)
{

   uint32_t opnum = 0;
   const u32 isize = 4;
   const uint32_t imask = 0xFFFFFFFC;

   full_block = include_branches;

   uint32_t digest[_SHA1_DIGEST_LENGTH];

   SceKernelUtilsSha1Context ctx;
   sceKernelUtilsSha1BlockInit(&ctx);

   bool contains_intr = false;

   for (uint32_t has_ended = 0; has_ended == 0; opnum++, pc += isize)
   {

      uint32_t op = _MMU_read32<PROCNUM, MMU_AT_CODE>(pc & imask);

      DynaCompiler fc = arm_instruction_compilers[INSTRUCTION_INDEX(op)];
      INSTR_R res = fc == 0 ? INTERPRET : fc(pc, op);

      has_ended = (!include_branches && instr_is_branch(op)) || (opnum >= max_opcodes) || (!include_branches && isHaltHackInstruction(op));

      currentBlock.WriteOP = currentBlock.WriteOP || isARMWritingInstruction(op);
      currentBlock.MCROP = currentBlock.MCROP || is_mcr_mrc(op);


      if (res == INTERPRET)
      {
         currentBlock.addOP(OP_ITP, op, pc, -1, op, -1, -1, PRE_OP_NONE, instr_is_conditional(op) ? CONDITION(op) : -1);
         if (!has_ended)
            contains_intr = true;
      }

      sceKernelUtilsSha1BlockUpdate(&ctx, (u8 *)&op, 4);

      if (has_ended && (!instr_does_prefetch(op) || res == INTERPRET)) // prefetch next instruction
         currentBlock.manualPrefetch = true;

      if (!include_branches)
         interpreted_cycles += op_decode[PROCNUM][false](); // + instr_cycles(op);
   }

   sceKernelUtilsSha1BlockResult(&ctx, (u8 *)digest);

   sprintf(currentBlock.block_hash, ">:1:%02X:%08X:%08X:%08X:%08X:%08X", opnum, digest[0], digest[1], digest[2], digest[3], digest[4]);

// #define save_hash
#ifdef save_hash
   extern void WriteHash(char *msg);
   if (!contains_intr)
      WriteHash(currentBlock.block_hash);
#endif
   // printf("Block hash: %s\n", currentBlock.block_hash);
}

template <int PROCNUM>
void build_ThumbBasicblock()
{

   const u32 isize = 2;
   const uint32_t imask = 0xFFFFFFFE;

   for (uint32_t i = 0, has_ended = 0; has_ended == 0; i++, pc += isize)
   {

      uint32_t op = _MMU_read16<PROCNUM, MMU_AT_CODE>(pc & imask);

      DynaCompiler fc = thumb_instruction_compilers[op >> 6];
      INSTR_R res = fc == 0 ? INTERPRET : fc(pc, op);

      if (res == INTERPRET)
         currentBlock.addOP(OP_ITP, op, pc, -1, op, -1, -1, PRE_OP_NONE, false);

      has_ended = instr_is_branch(op) || (i >= 128);

      if (has_ended && (!instr_does_prefetch(op) || res == INTERPRET)) // prefetch next instruction
         currentBlock.manualPrefetch = true;

      interpreted_cycles += op_decode[PROCNUM][true]() + instr_cycles(op);
   }
}

void checkAndDeleteLinkedBLock(u32 addr)
{

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

void test_jit_func()
{
   const int PROCNUM = 1;

   return;

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
   currentBlock.addOP(OP_ADD, 0, pc, 0, 1, 1, 0, PRE_OP_LSL_IMM);
   currentBlock.addOP(OP_ADD, 0, pc, 2, 2, 0, 1, PRE_OP_LSL_IMM);
   compile_basicblock<PROCNUM>();

   ArmOpCompiled f = (ArmOpCompiled)JIT_COMPILED_FUNC(base_adr, 1);

   asm volatile(
       "addiu $sp, $sp, -28\n"
       "sw $s0, 24($sp)\n"
       "sw $s1, 20($sp)\n"
       "sw $s2, 16($sp)\n"
       "sw $s3, 12($sp)\n"
       "sw $s4, 8($sp)\n"
       "sw $gp, 4($sp)\n"
       "sw $fp, 0($sp)\n"
       "move $k0, %0\n\t" // Move the address of ARMPROC into $k0
       :
       : "r"(&ARMPROC));
   f();

   asm volatile(
       "lw $s0, 24($sp)\n"
       "lw $s1, 20($sp)\n"
       "lw $s2, 16($sp)\n"
       "lw $s3, 12($sp)\n"
       "lw $s4, 8($sp)\n"
       "lw $gp, 4($sp)\n"
       "lw $fp, 0($sp)\n"
       "addiu $sp, $sp, 28\n");

   printf("0x%x\n", f);
   printf("R0: %d %d\n", ARMPROC.R[0], res);

   currentBlock.clearBlock();

   // restore R0 R1 R2
   ARMPROC.R[0] = R0;
   ARMPROC.R[1] = R1;
   ARMPROC.R[2] = R2;
}

int thid_dynarec = -1;

bool emit_nitrosdk_func(uint32_t guest_pc, bool thumb)
{
   if (!nds.isSdkValid() || thumb)
      return false;

   const uint32_t old_pc = pc;

   if (nds.is_twl_sdk() && ((guest_pc & 0xFFFF000) == 0x1FF8000))
   {
      int idx = 0;
      constexpr int cycles[2] = {20, 7};

      for (const auto &func : MICROCODE_FUNCTIONS)
      {

         pc = old_pc;
         currentBlock.clearBlock();
         build_ArmBasicblock<ARM9>(func.opcode_count - 1, true);

         if (func.equals(currentBlock.opcodes))
         {
            printf("[JIT] NitroSDK Microcode %s found at 0x%08X (CPU=%s)\n",
                   func.name,
                   old_pc,
                   "ARM9");

            u32 addr = pre_hle_block_emit();
            emit_jal(func.hle_function);
            emit_nop();
            post_hle_block_emit(addr, base_adr, cycles[idx]);

            interpreted_cycles += cycles[idx];

            return true;
         }

         idx++;
      }
   }

   const std::vector<Function> *functions = &FUNCTIONS_ARM9;

   
   interpreted_cycles = 1;
   for (const auto &func : *functions)
   {      
      pc = old_pc;
      currentBlock.clearBlock();
      build_ArmBasicblock<ARM9>(func.opcode_count - 1, true);
      if (func.equals(currentBlock.opcodes))
      {
         printf("[JIT] %s found at 0x%08X, psp equivalent: 0x%X (CPU=%s)\n",
                func.name,
                currentBlock.start_addr,
                emit_getCurrAdr(),
                "ARM9");
         u32 addr = pre_hle_block_emit();
         emit_jal(func.hle_function);
         emit_nop();
         post_hle_block_emit(addr, base_adr, func.cycles);
         return true;
      }
   }

   pc = old_pc;
   currentBlock.clearBlock();
   return false;
}

int before_emitted_sdk = 0;

template <int PROCNUM>
u32 arm_jit_compile()
{
   block_procnum = PROCNUM;
   interpreted_cycles = 0;
   full_block = false;

   thumb = ARMPROC.CPSR.bits.T == 1;
   base_adr = ARMPROC.instruct_adr;
   pc = base_adr;

   if (GetFreeSpace() < 4 * 1024)
   {
      // printf("Dynarec code reset\n");
      arm_jit_reset(true, true);
   }

   // printf("JIT: Compiling block at 0x%08X, thumb: %d\n", base_adr, thumb);

   /*ArmOpCompiled f = op_decode[PROCNUM][thumb];
      JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
      return f();*/

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

   if (emit_nitrosdk_func(pc, thumb))
   {
      ArmOpCompiled code_block = (ArmOpCompiled)JIT_COMPILED_FUNC(ARMPROC.instruct_adr, PROCNUM);
      return code_block();
   }

   //return op_decode[PROCNUM][thumb]();

   pc = base_adr;
   currentBlock.start_addr = base_adr;
   currentBlock.clearBlock();

   /*
   if (currentBlock.getNOpcodes() < 2)
   {
      //printf("Block too small\n");
      //ArmOpCompiled f = op_decode[PROCNUM][thumb];
      //JIT_COMPILED_FUNC(base_adr, PROCNUM) = (uintptr_t)f;
      compile_basicblock<PROCNUM>();
      return interpreted_cycles * 1.1;
   }
   */



   if (thumb)
   {
      build_ThumbBasicblock<PROCNUM>();
      //currentBlock.optimize_basicblockThumb();
      // return op_decode[PROCNUM][thumb]();
   }
   else
   {
      build_ArmBasicblock<PROCNUM>();
      //currentBlock.optimize_basicblock();
      // return op_decode[PROCNUM][thumb]();
   }

   compile_basicblock<PROCNUM>(true);
   // Return the number of cycles a bit higher than the interpreted cycles
   return interpreted_cycles;
}

/*
void parse_nitrosdk_entry() {




}
*/

uint32_t os_irq_handler_addr = 0;

extern "C" void hle_os_irqhandler(uint32_t guest_pc)
{

   const uint32_t irqs = MMU.reg_IE[0] & MMU.gen_IF<0>();
   /*if (regs.ime == 0 || irqs == 0) {
       // Same behavior as Rust: post-return to guest and stop handling
       //hle_post_function<ARM9>(asm_, 18, guest_pc);
       return;
   }*/

   // ARMPROC.freeze &= ~CPU_FREEZE_IRQ_IE_IF;

   /*

   // Select lowest-index pending IRQ: trailing_zeros()
   uint32_t irq_to_handle;
#if defined(__cpp_lib_bitops) && __cpp_lib_bitops >= 201907L
   irq_to_handle = static_cast<uint32_t>(std::countr_zero(irqs));
#else
   irq_to_handle = static_cast<uint32_t>(__builtin_ctz(irqs));
#endif

   // Clear that IRQ flag
   regs.irf &= ~(1u << irq_to_handle);

   // Push LR onto stack
   regs.sp -= 4;
   _MMU_ARM9_write32(regs.sp, regs.lr);

   // LR becomes OS thread-switch trampoline
   regs.lr = asm_->emu.os_irq_handler_thread_switch_addr;

   // Load IRQ handler from table
   const uint32_t irq_func = _MMU_ARM9_read32(os_irq_handler_addr + (irq_to_handle << 2));

   // Set up argument registers
   regs.gp_regs[0]  = irq_func;
   regs.gp_regs[1]  = irq_table_addr;
   regs.gp_regs[2]  = (1u << irq_to_handle);
   regs.gp_regs[3]  = 0x80000000u;
   regs.gp_regs[12] = 0x04000210u; // IE register (0x4000210)

   // Jump into JIT-compiled handler
   using JitEntry = void (*)(uint32_t);
   const uintptr_t entry_addr = asm_->emu.jit.get_jit_start_addr(irq_func);
   const auto jit_entry = reinterpret_cast<JitEntry>(entry_addr);
   jit_entry(irq_func);*/
}

void check_nitro_sdk()
{
   pc = NDS_ARM9.instruct_adr;

   currentBlock.clearBlock();

   currentBlock.start_addr = pc;
   build_ArmBasicblock<1>(256, true);

   pc = NDS_ARM9.instruct_adr;

   if (currentBlock.getNOpcodes() < 3)
   {
      printf("Not enough instructions in the block\n");
      currentBlock.clearBlock();
      return;
   }

   auto &inst0 = currentBlock.opcodes[0];
   switch (inst0._op)
   {
   case OP_MOV:
      if (inst0.rd != 12 || inst0.imm != 0x4000000) // Check correctness
      {
         printf("First instruction is not MOV R12, #0x04000000\n");
         currentBlock.clearBlock();
         return;
      }
      break;

   default:
      printf("DEFAULT: First instruction is not MOV R12, #0x04000000\n");
      currentBlock.clearBlock();
      return;
   }

   auto &inst1 = currentBlock.opcodes[1];
   switch (inst1._op)
   {
   case OP_STR:
   {
      const bool isPost = inst1.preOpType & PRE_OP_POST_P;
      if (isPost ||
          /*transfer.write_back() ||
          !transfer.add() ||*/
          inst1.rd != 12 ||
          inst1.rs1 != 12 ||
          inst1.imm != 0x208)
      {
         printf("Second instruction is not STRH R12, [R12, #0x208]\n");
         currentBlock.clearBlock();
         return;
      }
      break;
   }
   default:
      printf("DEFAULT: Second instruction is not STRH R12, [R12, #0x208]: %x\n", inst1._op);
      currentBlock.clearBlock();
      return;
   }

   uint32_t start_module_params_addr = 0;
   bool oam_imm_load_found = false;

   for (size_t i = 0; i < currentBlock.getNOpcodes(); i++)
   {
      auto &inst = currentBlock.opcodes[i];

      if (inst._op == OP_LDR)
      {
         if (inst.imm == -1)
            continue;

         uint32_t current_pc = inst.op_pc;
         uint32_t imm = inst.imm;
         uint32_t pc_val = current_pc + 8;
         uint32_t imm_addr = inst.preOpType & PRE_OP_IMM_PRE_P ? pc_val + imm : pc_val - imm;
         uint32_t imm_value = _MMU_ARM9_read32(imm_addr);

         if (oam_imm_load_found)
         {
            start_module_params_addr = imm_value;
            break;
         }
         else if (imm_value == 0x07000000)
         { // OAM_OFFSET
            printf("OAM_OFFSET load found at 0x%08X\n", current_pc);
            oam_imm_load_found = true;
         }
      }
      else
         printf("OP: %ld\n", inst._op);
   }

   if (start_module_params_addr == 0)
   {
      printf("StartModuleParams address not found\n");
      currentBlock.clearBlock();
      return;
   }

   uint32_t buf[3] = {0};

   for (int i = 0; i < 3; i++)
   {
      buf[i] = _MMU_ARM9_read32(start_module_params_addr + 24 + (i << 2));
   }

   uint32_t sdk_version_info = buf[0];
   uint32_t sdk_nitro_code_be = buf[1];
   uint32_t sdk_nitro_code_le = buf[2];

   if (sdk_nitro_code_le != __builtin_bswap32(sdk_nitro_code_be))
   {
      printf("Nitro SDK signature mismatch\n");
      currentBlock.clearBlock();
      return;
   }

   nds.sdk_version_major = (sdk_version_info >> 24) & 0xFF;
   nds.sdk_version_minor = (sdk_version_info >> 16) & 0xFF;
   nds.sdk_version_relstep = sdk_version_info & 0xFFFF;
   nds.sdkValid = true;

   printf("Nitro SDK version %d.%d.%d detected\n",
          nds.sdk_version_major,
          nds.sdk_version_minor,
          nds.sdk_version_relstep);

   constexpr uint32_t ADD_IMM_VALUES[2] = {0x3FC0u, 0x3Cu};
   size_t add_match_count = 0;

   for (size_t i = 0; i < currentBlock.getNOpcodes(); ++i)
   {
      auto &inst = currentBlock.opcodes[i];

      switch (inst._op)
      {
      case OP_ADD:
      {

         if (add_match_count < 2 && inst.imm != static_cast<int32_t>(-1))
         {
            if (static_cast<uint32_t>(inst.imm) == ADD_IMM_VALUES[add_match_count])
            {
               ++add_match_count;
            }
         }
         break;
      }

      case OP_LDR:
      {
         if (inst.imm == static_cast<int32_t>(-1))
         {
            break;
         }

         if (add_match_count == 2)
         {
            const uint32_t current_pc = inst.op_pc;
            const uint32_t pc_val = current_pc + 8;
            const uint32_t imm = static_cast<uint32_t>(inst.imm);

            const bool add = (inst.preOpType & PRE_OP_IMM_PRE_P) != 0;
            const uint32_t imm_addr = add ? (pc_val + imm) : (pc_val - imm);

            const uint32_t imm_value = _MMU_ARM9_read32(imm_addr);

            if (imm_value < 0x02000000)
            {
               os_irq_handler_addr = imm_value;

               printf("OS IRQ handler addr: 0x%08X (from LDR literal @ 0x%08X)\n",
                      imm_value, current_pc);
               i = currentBlock.getNOpcodes(); // force loop end
            }
         }
         break;
      }

      default:
         // ignore other ops
         break;
      }
   }

   currentBlock.clearBlock();
}

template u32 arm_jit_compile<0>();
template u32 arm_jit_compile<1>();

void arm_jit_reset(bool enable, bool suppress_msg)
{
   if (!suppress_msg)
      printf("CPU mode: %s\n", enable ? "JIT" : "Interpreter");

   saveBlockSizeJIT = my_config.DynarecBlockSize; // CommonSettings.jit_max_block_size;
   first_time = true;

   if (enable)
   {
      printf("JIT: max block size %d instruction(s)\n", CommonSettings.jit_max_block_size);

#define JITFREE(x) memset(x, 0, sizeof(x));
      JITFREE(JIT.MAIN_MEM);
      JITFREE(JIT.SWIRAM);
      JITFREE(JIT.ARM9_ITCM);
      JITFREE(JIT.ARM9_LCDC);
      JITFREE(JIT.ARM9_BIOS);
#undef JITFREE

      // memset(recompile_counts, 0, sizeof(recompile_counts));
      init_jit_mem();

      resetCodeCache();
   }
}

void arm_jit_close()
{
   resetCodeCache();
}