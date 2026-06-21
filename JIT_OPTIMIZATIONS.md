# DSStation JIT Optimization Tracking

Research source: multi-agent workflow `wf_9138754e-295` (6 research dimensions + adversarial verify).

---

## Implemented — Session 1

| ID | Description |
|---|---|
| `kill-sha1-build` | SHA1 per-instruction hashing gated behind `#if defined(JIT_BUILD_HASH) \|\| defined(save_hash)` — removed from hot path |
| `gate-stats-loop` | ITP stats walk gated behind `#ifdef JIT_PROFILE_ITP` |
| `compact-block-fields` | `reg_usage_end[17]` removed (write-only, never read); `block_hash[1024]` gated behind same macro |
| `emit-by-reference` | Emit loops changed from `for (opcode op : opcodes)` to `for (opcode &op : opcodes)` — avoids per-op copy |
| `inline-dispatch-OR` | `emit_inline_dispatch`: 5 separate `EMIT_CHECK_EXIT` chains (20 insns) collapsed to OR-fold into `$t2` + single `beq/j` exit (~12 insns fewer per linked block) |
| `icache-align` | Block emission aligned to 64-byte ICache line boundary before `emit_GetPtr()` (guarded by `exp_icache_align`) |
| `early-term-suffix-reuse` | Block build stops early when current PC already has a compiled block; epilogue jumps directly into it instead of re-emitting (guarded by `exp_early_term`) |

---

## Implemented — Session 2

| ID | Macro | Description |
|---|---|---|
| `mla-madd` | `JIT_OPT_MULACC` | `OP_MLA`: `mult+mflo+addu` → `mtlo(Rn)+madd+mflo`; saves one instruction and removes the addu data dependency |
| `umlal-maddu` | `JIT_OPT_MULACC` | `OP_UMLA` (UMLAL): was only accumulating the low half (correctness bug) → `mtlo+mthi+maddu+mflo+mfhi` for true 64-bit accumulate; `ARM_OP_UMLAL` unblocked |
| `umull-maddu-context` | `JIT_OPT_MULACC` | `ARM_OP_UMULL` unblocked (was `return INTERPRET`); `OP_UMUL` lowering fixed — RdHi and RdLo were mapped to the same register (bug), now mapped separately |
| `rrx-ext-gp` | `JIT_OPT_RRX_GP` | `PRE_OP_ROR_IMM` (RRX path): skips `lbu` CPSR reload when `flag_loaded` is true; reads carry directly from `psp_gp` |
| `qadd-qsub-minmax` | `JIT_OPT_SATURATE` | `ARM_OP_QADD/QSUB` were `#define`d to 0 (always INTERPRET) → real decoder functions + 11-insn branchless saturation via `nor/and/sra/xor/movn` pattern |
| `smul-smla-xy-madd` | `JIT_OPT_SIGNEDMUL16` | `ARM_OP_SMUL_B_B` etc. were `#define`d to 0 → `decode_smulxy/decode_smlaxy`; lowering uses `seh/sra` to extract 16-bit halves + `mult` / `mtlo+madd+mflo` |
| `condmov-movz-verify` | `JIT_OPT_PREDICATE_MUL` | `OP_MUL/MLA` conditional path now always uses `conditional_branchless` (movz/movn); previously fell back to a branch when `rd_allocated` was false |

---

## No code change needed

| ID | Reason |
|---|---|
| `ldrb-ext-vs-andi` | The C read helpers (`_MMU_read08/16`) already return zero-extended values; LDRB/LDRH need no extra masking instruction. Already optimal. |
| `ir-fields-cleanup` (partial) | `reg_usage_end` was removed. Remaining item: `EXTFL_SAVECOND` is force-OR'd in the opcode constructor even when callers explicitly pass `EXTFL_NONE`, making `extra_flags` untrustworthy for any future peephole pass. Low priority. |

---

## Not Implemented — Remaining Work

### High impact, high complexity

#### `backpatch-block-jump`
At block compile time, write `j <next_block_addr>` directly into the emitted MIPS code via runtime patching (replacing the `emit_inline_dispatch` runtime table walk). When JIT invalidation fires (SMC path: `JIT_MarkCodePage` / `mmu_write_lut`, MMU.h:1038-1108), revert all patch sites that pointed into the freed page back to `j continue_cpu_dispatch`.

- **Savings**: ~13 → 1 emitted insns per taken branch edge (hot inner loops)
- **Files**: `arm_jit.cpp` (compile_basicblock epilogue), `MMU.h` (SMC invalidation)
- **Risk**: Needs a patch-site registry per JIT page; ICache flush of patched lines

#### `regfile-resident-chain`
Keep hot ARM registers live across chained blocks. Currently `emitArmBlock` unconditionally flushes the entire SRA cache to the ARMPROC struct at every block boundary (`regman.flush_all(); regman.reset()`, blockdecoder.cpp:2320-2321) and the next block reloads from scratch.

- **Savings**: 5–10 load/store insns eliminated per block-to-block transition on the hot path
- **Files**: `blockdecoder.cpp` (emitArmBlock, block boundary epilogue/prologue)
- **Risk**: Must only apply when the successor block is statically known and linked; fallback to full flush otherwise

#### `branch-edge-link`
`OP_BC/OP_BLC` currently emit a C call to `jump_to_linked_bc/blc<true>` which updates R15/next_instruction/instruct_adr and returns a cycle count of 3 (blockdecoder.cpp:846-864). If the branch target is already compiled, substitute a direct JIT-to-JIT flow instead of round-tripping through the C dispatcher.

- **Files**: `blockdecoder.cpp` (OP_BC/OP_BLC cases ~1460-1495), `arm_jit.cpp`
- **Related to**: `backpatch-block-jump` — ideally implemented together

---

### Medium impact

#### `idle-readop-spin` ⭐ easiest remaining win
**Bug**: `ReadOP` is declared in blockdecoder.h:382, cleared in `clearBlock` (h:346), and checked in `isIdleLoop` (h:276) — but **has no setter anywhere in the codebase**. The poll-loop guard is completely dead. Memory-polling spin loops (e.g. `ldr rX,[VCOUNT]; cmp; bne`) are never fast-forwarded to the next scheduler event.

- **Fix**: Set `ReadOP = true` in the block builder when an LDR/LDM instruction is decoded
- **Files**: `arm_jit.cpp` (ARM_OP_LDR decoder and related load decoders)
- **Risk**: Low; this is a pure correctness fix for a dead flag

#### `disp-tail-cheap-exit`
Further shrink `emit_inline_dispatch` beyond the OR-fold already done. The `s32next` field load and the `freeze`/`freezeBus` loads are block-constant (do not change during a block's execution) and could be hoisted or cached. Current state after the OR-fold is already improved from ~26 to ~14 insns; headroom remains.

- **Files**: `arm_jit.cpp` (`emit_inline_dispatch`, ~line 2197-2276)

#### `reenable-optimize-pipeline`
`optimize_basicblock()` and `optimize_basicblockThumb()` are commented out at arm_jit.cpp:2855/2861 due to a known regression: 3D graphics vanished during const-prop of GX-FIFO writes. The optimizer incorrectly propagated a constant through an `OP_3D_FIFO` write that has a side-effect.

- **Fix**: Gate const-prop in `optimize_basicblock` on `!MCROP` (or check `OP_3D_FIFO`/`OP_3D_CMD` in the op stream before propagating)
- **Files**: `arm_jit.cpp` (optimizer call sites), `blockdecoder.cpp` (optimize_basicblock implementation)

---

### Specialized / high complexity

#### `vfpu-ldm-stm-bulk`
Use VFPU `lvq/svq` (128-bit load/store) for LDM/STM with ≥4 registers and a word-aligned base address in main RAM. Currently each register in the list costs a full C call to `_MMU_read32`/`_write32`. The HLE copy stubs (MI_CPU_COPY32 arm_jit.cpp:123, MI_COPY64B:136, hle_mi_cpu_clear32:199-226) are the primary targets.

- **Savings**: 4 C calls → 1 `lvq` + 4 `mfv` (or 4 `mtv` + 1 `svq`) for the aligned main-RAM fast path
- **Risk**: VFPU register pressure; must verify alignment; fallback to C for DTCM/IO

#### `vfpu-gxfifo-matrix`
Use VFPU `vtfm4q` for GX FIFO matrix command bursts (MTX_LOAD_4x4, MTX_MULT_4x4, vertex packets) routed through `OP_3D_FIFO` (blockdecoder.cpp:1035-1046) and the HLE GX-FIFO send stubs.

- **Risk**: Very specialized; requires understanding of the GX command buffer format and whether the VFPU result layout matches what `gfx3d_sendCommandToFIFO` expects
