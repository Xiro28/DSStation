// Differential tester: runs each instruction through the JIT and the interpreter
// from an identical starting state and reports any divergence in registers,
// flags, or a memory window.
//
// It does NOT need a running game: it crafts CPU state and a scratch RAM window,
// then for each opcode in TEST_CASES it compares JIT vs interpreter output.
//
// Triggered from the in-emulator Menu -> "JIT DiffTest" (see ctrlssdl.cpp),
// which calls jit_difftest_run_force(). Output goes to the on-screen debug
// console (DTPRINT). To add coverage, append entries to TEST_CASES below
// (ARM opcodes, cond=AL=0xE). Each case is compared register/flag/memory-wise
// between the interpreter and the JIT; mismatches print [FAIL] lines.
//
// Limitations: R15/PC is not compared (JIT and interpreter advance PC by
// different conventions); the test op is wrapped with a trailing "B ." so the
// JIT block is exactly one instruction.

#include "types.h"
#include <cstdio>
#include <cstring>
#include <cstdarg>
#include <pspdebug.h>

// Report to BOTH the on-screen debug console and stdout (printf -> PSP console /
// redirected log), so failures can be captured off-device.
static void DTPRINT(const char *fmt, ...)
{
   char buf[256];
   va_list ap;
   va_start(ap, fmt);
   vsnprintf(buf, sizeof(buf), fmt, ap);
   va_end(ap);
   pspDebugScreenPrintf("%s", buf);
   printf("%s", buf);
}

#include "armcpu.h"
#include "MMU.h"
#include "blockdecoder.h"
#include "arm_jit.h"
#include "instructions.h"

// --- hooks into the JIT (defined in arm_jit.cpp / blockdecoder.cpp) ---
extern block currentBlock;
extern u32 base_adr;
extern "C" uint32_t run_block_chain(armcpu_t *armproc, uintptr_t first_block);
template <int PROCNUM> u32 arm_jit_compile();
void arm_jit_reset(bool enable, bool suppress_msg);

// Interpreter op tables.
extern const OpFunc arm_instructions_set[2][4096];
extern const OpFunc thumb_instructions_set[2][1024];

// Same address blockdecoder.cpp uses; setting it to 1 makes the chain exit
// after the first compiled block instead of chasing the trailing "B ." forever.
#define NDS_ReschedulePtr (*(bool *)(0x0010080))

namespace {

constexpr u32 SCRATCH_BASE = 0x02100000;   // inside main RAM (4MB region @ 0x02000000)
constexpr u32 SCRATCH_WORDS = 64;          // 256-byte window we diff

struct CpuSnapshot {
   u32 R[16];
   u32 cpsr_flags;   // NZCV in bits 31..28, plus we keep full val masked
   u32 mem[SCRATCH_WORDS];
};

// Simple deterministic PRNG so runs are reproducible.
u32 g_rng = 0x12345678u;
inline u32 xrand() { g_rng ^= g_rng << 13; g_rng ^= g_rng >> 17; g_rng ^= g_rng << 5; return g_rng; }

void seed_state(armcpu_t &cpu, u32 instr_adr, u32 flag_seed)
{
   // Random register contents (the same sequence is reused for the interp and
   // jit runs of a given case because the caller reseeds g_rng identically).
   for (int i = 0; i < 16; i++)
      cpu.R[i] = xrand();
   // Base registers for memory ops must point into the scratch window.
   cpu.R[0]  = SCRATCH_BASE + 0x40;
   cpu.R[1]  = SCRATCH_BASE + 0x40;
   cpu.R[13] = SCRATCH_BASE + 0x80;   // SP mid-window so push/pop both fit
   cpu.instruct_adr     = instr_adr;
   cpu.next_instruction = instr_adr + 4;
   cpu.R[15]            = instr_adr + 8;
   // Randomize NZCV (carry-in matters for ADC/SBC/RSC etc.).
   cpu.CPSR.val = (cpu.CPSR.val & ~0xF0000000u) | (flag_seed & 0xF0000000u);
}

void seed_mem()
{
   for (u32 i = 0; i < SCRATCH_WORDS; i++)
      _MMU_ARM9_write32(SCRATCH_BASE + i * 4, 0xA5A50000u + i);
}

void take_snapshot(const armcpu_t &cpu, CpuSnapshot &s)
{
   memcpy(s.R, cpu.R, sizeof(s.R));
   s.cpsr_flags = cpu.CPSR.val & 0xF0000000u;
   for (u32 i = 0; i < SCRATCH_WORDS; i++)
      s.mem[i] = _MMU_ARM9_read32(SCRATCH_BASE + i * 4);
}

// Run one instruction through the pure interpreter.
void run_interpreter(armcpu_t &cpu, u32 op, bool thumb)
{
   cpu.instruction = op;
   if (thumb)
      thumb_instructions_set[0][op >> 6](op);
   else
      arm_instructions_set[0][INSTRUCTION_INDEX(op)](op);
}

// Compile a single-instruction block at base and run it via the chain.
// Returns true if the JIT actually COMPILED the op (false = it fell back to the
// interpreter, in which case JIT and interpreter trivially agree).
bool run_jit(armcpu_t &cpu, u32 op, bool thumb, u32 instr_adr)
{
   // Place the opcode in scratch *code* memory the JIT will read, followed by a
   // branch so the block is exactly one real instruction (block build ends on a
   // branch). 0xEAFFFFFE = "B ." (branch to self), an unconditional branch.
   _MMU_ARM9_write32(instr_adr,     op);
   _MMU_ARM9_write32(instr_adr + 4, 0xEAFFFFFE);

   cpu.instruct_adr     = instr_adr;
   cpu.next_instruction = instr_adr + 4;
   cpu.R[15]            = instr_adr + 8;

   JIT_COMPILED_FUNC(instr_adr, 0) = 0; // force fresh compile of this opcode
   arm_jit_compile<0>();
   uintptr_t blk = JIT_COMPILED_FUNC(instr_adr, 0);
   if (!blk) return false;

   const bool saved_resched = NDS_ReschedulePtr;
   NDS_ReschedulePtr = 1;               // force chain to exit after this one block
   run_block_chain(&cpu, blk);
   NDS_ReschedulePtr = saved_resched;
   return true;
}

// Did the JIT emit native code for this op (vs interpret-fallback)? We detect
// it by checking whether the compiled block contains an OP_ITP marker: rather
// than parse, we re-run the front-end decoder. Simpler: probe currentBlock after
// compile. We approximate by: an op is "JIT-native" if any ALU/LDR/STR/LDM/STM
// op type was produced. For reporting we just track per-family counts instead.

// --- per-family result tracking ---
struct FamStat {
   char name[24];
   u32 tested, failed, native;
};
constexpr int MAX_FAMS = 512;
FamStat g_fams[MAX_FAMS];
int     g_nfams = 0;
int     g_cur_fam = -1;

int begin_family(const char *name)
{
   if (g_nfams >= MAX_FAMS) { g_cur_fam = MAX_FAMS - 1; return g_cur_fam; }
   int f = g_nfams++;
   strncpy(g_fams[f].name, name, sizeof(g_fams[f].name) - 1);
   g_fams[f].name[sizeof(g_fams[f].name) - 1] = 0;
   g_fams[f].tested = g_fams[f].failed = g_fams[f].native = 0;
   g_cur_fam = f;
   return f;
}

// Distinct failing opcodes (so the same buggy form across seeds prints once).
struct FailRec { u32 op; const char *fam; };
constexpr int MAX_FAILS = 24;
FailRec g_fail_list[MAX_FAILS];
int     g_nfail_list = 0;

armcpu_t *g_cpu = nullptr;
u32       g_adr = 0;

constexpr int SEEDS_PER_OP = 8;            // random register sets tried per opcode

// Run one opcode across several random states, both ways, and diff. The first
// seed that diverges is reported in full; the op is recorded once.
bool check_op(u32 op, bool thumb, const char *name)
{
   armcpu_t &cpu = *g_cpu;
   FamStat &fam = g_fams[g_cur_fam];
   fam.tested++;

   bool native_seen = false;

   for (int seed = 0; seed < SEEDS_PER_OP; seed++)
   {
      const u32 reg_seed  = 0xC0FFEEu * (seed + 1) + op;
      const u32 flag_seed = (op << 3) ^ (seed * 0x40000000u);

      // Snapshot the INPUT state (both runs use the same seeded state).
      g_rng = reg_seed; seed_mem();
      seed_state(cpu, g_adr, flag_seed);
      CpuSnapshot in; take_snapshot(cpu, in);

      run_interpreter(cpu, op, thumb);
      CpuSnapshot itp; take_snapshot(cpu, itp);

      g_rng = reg_seed; seed_mem();
      seed_state(cpu, g_adr, flag_seed);
      bool native = run_jit(cpu, op, thumb, g_adr);
      CpuSnapshot jit; take_snapshot(cpu, jit);
      native_seen = native_seen || native;

      bool ok = true;
      for (int r = 0; r < 15; r++)          // skip R15: PC handling differs by design
         if (itp.R[r] != jit.R[r]) ok = false;
      if (itp.cpsr_flags != jit.cpsr_flags) ok = false;
      for (u32 m = 0; m < SCRATCH_WORDS; m++)
         if (itp.mem[m] != jit.mem[m]) ok = false;

      if (!ok) {
         fam.failed++;
         if (g_nfail_list < MAX_FAILS)
            g_fail_list[g_nfail_list++] = { op, name };
         // Detailed dump for the first few distinct failures: show the inputs
         // each operand register actually held, then expected (interp) vs jit.
         if (g_nfail_list <= 6) {
            DTPRINT("[FAIL] %s op=%08X native=%d seed=%d\n", name, op, native, seed);
            // inputs: only the registers this opcode reads, plus flags-in.
            const u32 rn = (op >> 16) & 0xF, rm = op & 0xF,
                      rs = (op >> 8) & 0xF, rd = (op >> 12) & 0xF;
            DTPRINT("   in: Rn(%u)=%08X Rm(%u)=%08X Rs(%u)=%08X Rd(%u)=%08X flg=%08X\n",
                    rn, in.R[rn], rm, in.R[rm], rs, in.R[rs], rd, in.R[rd], in.cpsr_flags);
            // differing result registers: expected vs jit.
            for (int r = 0; r < 15; r++)
               if (itp.R[r] != jit.R[r])
                  DTPRINT("   R%-2d expect=%08X jit=%08X\n", r, itp.R[r], jit.R[r]);
            if (itp.cpsr_flags != jit.cpsr_flags)
               DTPRINT("   flg expect=%08X jit=%08X\n", itp.cpsr_flags, jit.cpsr_flags);
            for (u32 m = 0; m < SCRATCH_WORDS; m++)
               if (itp.mem[m] != jit.mem[m])
                  DTPRINT("   m+%02X(in=%08X) expect=%08X jit=%08X\n",
                          m*4, in.mem[m], itp.mem[m], jit.mem[m]);
         }
         if (native_seen) fam.native++;
         return false;
      }
   }
   if (native_seen) fam.native++;
   return true;
}

// Build an ARM data-processing opcode (immediate or register form).
inline u32 dp(u32 cond, u32 opc, u32 s, u32 rn, u32 rd, u32 operand2, bool imm)
{
   return (cond << 28) | (imm ? (1u << 25) : 0) | (opc << 21) | (s << 20) |
          (rn << 16) | (rd << 12) | (operand2 & 0xFFF);
}

// Sweep all data-processing opcodes. Each (opcode x operand-form) is its own
// reported family, so the summary says exactly e.g. "ADD imm" passes but
// "ADD ror" / "ADD rrx" fails. Forms:
//   imm   : rotated 8-bit immediate
//   lsl   : Rm, LSL #n   (n in {0,1,31})
//   lsr   : Rm, LSR #n
//   asr   : Rm, ASR #n
//   ror   : Rm, ROR #n   (n in {1,31}; n=0 is RRX, tested separately)
//   rrx   : Rm, ROR #0  == RRX (rotate right through carry)
//   lslr  : Rm, LSL Rs   (register-specified shift amount)
//   lsrr/asrr/rorr similarly
void sweep_dataproc()
{
   static const char *opc_names[16] = {
      "AND","EOR","SUB","RSB","ADD","ADC","SBC","RSC",
      "TST","TEQ","CMP","CMN","ORR","MOV","BIC","MVN" };
   const u32 rn = 3, rd = 2, rm = 4, rs = 6;

   for (u32 opc = 0; opc < 16; opc++)
   for (u32 s = 0; s <= 1; s++)
   {
      const char *suf = s ? "S" : "";
      char fam[24];

      // immediate
      snprintf(fam, sizeof(fam), "%s%s imm", opc_names[opc], suf);
      begin_family(fam);
      for (u32 imm8 : {0u, 1u, 0xFFu, 0x80u})
      for (u32 rot  : {0u, 4u, 8u})            // rotate field too
         check_op(dp(0xE, opc, s, rn, rd, (rot << 8) | imm8, true), false, fam);

      // immediate-shifted register: LSL/LSR/ASR/ROR by #1 and #31
      static const char *shn[4] = { "lsl", "lsr", "asr", "ror" };
      for (u32 sh = 0; sh < 4; sh++) {
         snprintf(fam, sizeof(fam), "%s%s %s", opc_names[opc], suf, shn[sh]);
         begin_family(fam);
         for (u32 amt : {1u, 5u, 31u}) {
            u32 op2 = (amt << 7) | (sh << 5) | rm;
            check_op(dp(0xE, opc, s, rn, rd, op2, false), false, fam);
         }
      }

      // special encodings where shift-amount #0 means something else:
      // LSL #0 = plain Rm ; LSR #0 = LSR #32 ; ASR #0 = ASR #32 ; ROR #0 = RRX
      snprintf(fam, sizeof(fam), "%s%s lsl0", opc_names[opc], suf); begin_family(fam);
      check_op(dp(0xE, opc, s, rn, rd, (0u<<5)|rm, false), false, fam);     // LSL #0
      snprintf(fam, sizeof(fam), "%s%s lsr32", opc_names[opc], suf); begin_family(fam);
      check_op(dp(0xE, opc, s, rn, rd, (1u<<5)|rm, false), false, fam);     // LSR #0(=32)
      snprintf(fam, sizeof(fam), "%s%s asr32", opc_names[opc], suf); begin_family(fam);
      check_op(dp(0xE, opc, s, rn, rd, (2u<<5)|rm, false), false, fam);     // ASR #0(=32)
      snprintf(fam, sizeof(fam), "%s%s rrx", opc_names[opc], suf); begin_family(fam);
      check_op(dp(0xE, opc, s, rn, rd, (3u<<5)|rm, false), false, fam);     // ROR #0 = RRX

      // register-specified shift amount: LSL/LSR/ASR/ROR by Rs
      static const char *shr[4] = { "lslr", "lsrr", "asrr", "rorr" };
      for (u32 sh = 0; sh < 4; sh++) {
         snprintf(fam, sizeof(fam), "%s%s %s", opc_names[opc], suf, shr[sh]);
         begin_family(fam);
         u32 op2 = (rs << 8) | (sh << 5) | (1u << 4) | rm;   // bit4=1 => reg shift
         check_op(dp(0xE, opc, s, rn, rd, op2, false), false, fam);
      }
   }
}

// Sweep LDR/STR (word & byte) immediate and register offset, pre/post, up/down,
// with and without writeback.
void sweep_ldrstr()
{
   begin_family("LDR/STR");
   for (u32 L = 0; L <= 1; L++)             // 0=STR 1=LDR
   for (u32 B = 0; B <= 1; B++)             // byte
   for (u32 P = 0; P <= 1; P++)             // pre/post
   for (u32 U = 0; U <= 1; U++)             // up/down
   for (u32 W = 0; W <= 1; W++)             // writeback (only valid with P, or post)
   for (u32 I = 0; I <= 1; I++)             // 0=imm offset 1=reg offset
   {
      const u32 rn = 0 /*base=scratch+0x40*/, rd = 2;
      u32 off = I ? 4 /*rm=r4*/ : 0x10;     // imm12 = 16 bytes
      u32 op = (0xEu << 28) | (1u << 26) | (I << 25) | (P << 24) | (U << 23) |
               (B << 22) | (W << 21) | (L << 20) | (rn << 16) | (rd << 12) | off;
      check_op(op, false, "ldr/str");
   }
}

// Sweep LDM/STM across P/U/W/L and several register-list patterns.
void sweep_ldmstm()
{
   begin_family("LDM/STM");
   const u32 lists[] = { 0x000C, 0x001C, 0x003C, 0x0006, 0x00FF, 0x8004 /*incl PC*/, 0x4004 /*incl LR*/ };
   for (u32 P = 0; P <= 1; P++)
   for (u32 U = 0; U <= 1; U++)
   for (u32 W = 0; W <= 1; W++)
   for (u32 L = 0; L <= 1; L++)
   for (u32 rlist : lists)
   {
      const u32 rn = 0; // base = scratch+0x40
      u32 op = (0xEu << 28) | (1u << 27) | (P << 24) | (U << 23) |
               (W << 21) | (L << 20) | (rn << 16) | rlist;
      check_op(op, false, "ldm/stm");
   }
}

// Sweep MUL / MLA across register choices.
void sweep_mul()
{
   begin_family("MUL/MLA");
   for (u32 s = 0; s <= 1; s++) {
      // MUL rd, rm, rs : rd=2 rm=3 rs=4
      check_op((0xEu<<28)|(s<<20)|(2u<<16)|(4u<<8)|(9u<<4)|3u, false, "mul");
      // MLA rd, rm, rs, rn : rd=2 rn=5 rs=4 rm=3
      check_op((0xEu<<28)|(1u<<21)|(s<<20)|(2u<<16)|(5u<<12)|(4u<<8)|(9u<<4)|3u, false, "mla");
   }
}

} // namespace

// Force-run: invoked from the ROM-select menu. Tests every instruction family
// the JIT handles, sweeping operand/addressing/condition variations, and diffs
// each against the interpreter.
extern "C" void jit_difftest_run_force()
{
   DTPRINT("=== JIT vs interpreter difftest ===\n");

   // Ensure JIT memory is initialized (the ROM-select menu may run before any
   // ROM has been loaded / MMU_Reset has set the JIT up).
   arm_jit_reset(true, true);

   armcpu_t &cpu = NDS_ARM9;
   armcpu_t saved = cpu;          // restore real CPU afterwards

   g_cpu = &cpu;
   g_adr = SCRATCH_BASE + 0x200;
   g_nfams = 0; g_nfail_list = 0; g_cur_fam = -1;

   sweep_dataproc();
   sweep_ldrstr();
   sweep_ldmstm();
   sweep_mul();

   cpu = saved;

   // --- per-family summary (only families with native JIT codegen are
   //     interesting; interpret-fallback families trivially pass) ---
   u32 tot_t = 0, tot_f = 0;
   DTPRINT("family        tested fail native\n");
   for (int f = 0; f < g_nfams; f++) {
      FamStat &s = g_fams[f];
      tot_t += s.tested; tot_f += s.failed;
      // Print only families that were JIT-native or had failures (skip noise).
      if (s.native || s.failed)
         DTPRINT("%-13s %5u %5u %5u%s\n", s.name, s.tested, s.failed, s.native,
                 s.failed ? "  <-- FAIL" : "");
   }
   DTPRINT("TOTAL tested=%u failed=%u\n", tot_t, tot_f);

   // --- distinct failing opcodes ---
   if (g_nfail_list) {
      DTPRINT("failing opcodes:\n");
      for (int i = 0; i < g_nfail_list; i++)
         DTPRINT("  %-10s %08X\n", g_fail_list[i].fam, g_fail_list[i].op);
      if (tot_f > (u32)g_nfail_list)
         DTPRINT("  ... (%u more)\n", tot_f - g_nfail_list);
   } else {
      DTPRINT("ALL PASS\n");
   }
}
