#include "aot_cache.h"
#include "arm_jit.h"
#include "mips_code_emiter.h"
#include "armcpu.h"
#include "NDSSystem.h"
#include "MMU.h"
#include "MMU_timing.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <pspkernel.h>
#include <pspkerneltypes.h>
#include <pspdebug.h>

// ---------------------------------------------------------------
// Globals
// ---------------------------------------------------------------

static char s_aot_path[256];

#define AOT_MAX_BLOCKS  16384
#define AOT_BLOB_CAP    (4 * 1024 * 1024)

static AOTBlockEntry s_entries[AOT_MAX_BLOCKS];
static u8  *s_blob_buf   = NULL;
static u32  s_num_blocks  = 0;
static u32  s_blob_offset = 0;

// ---------------------------------------------------------------
// Separate AOT code buffer
//
// Pre-compiled blocks live in a dedicated heap buffer so that
// JIT cache evictions (resetCodeCache) never destroy them.
// aot_load() and aot_precompile() direct emit_* into this buffer
// via set_code_cache().  JIT_COMPILED_FUNC entries point into this
// buffer and remain valid indefinitely.
// ---------------------------------------------------------------

#define AOT_CODE_BUF_SIZE (4 * 1024 * 1024)

static u8  *s_aot_code_buf  = NULL;
static u32  s_aot_code_used = 0;
static u32  s_saved_last_addr = 0;

extern u32 LastAddr;   // defined in mips_code_emiter.cpp

static bool aot_buf_ensure(void)
{
    if (s_aot_code_buf) return true;
    s_aot_code_buf  = (u8*)malloc(AOT_CODE_BUF_SIZE);
    s_aot_code_used = 0;
    return s_aot_code_buf != NULL;
}

static void aot_buf_begin(void)
{
    s_saved_last_addr = LastAddr;
    LastAddr = s_aot_code_used;
    set_code_cache(s_aot_code_buf);
}

static void aot_buf_end(void)
{
    s_aot_code_used = LastAddr;
    LastAddr = s_saved_last_addr;
    set_code_cache(NULL);
}

// Free bytes remaining in the AOT buffer (only valid inside begin/end).
static u32 aot_buf_free(void)
{
    if (!s_aot_code_buf) return 0;
    return AOT_CODE_BUF_SIZE - LastAddr;
}

// ---------------------------------------------------------------
// SHA1
// ---------------------------------------------------------------

static void sha1_buf(const void *data, u32 len, u8 out[20])
{
    SceKernelUtilsSha1Context ctx;
    sceKernelUtilsSha1BlockInit(&ctx);
    sceKernelUtilsSha1BlockUpdate(&ctx, (u8*)data, len);
    sceKernelUtilsSha1BlockResult(&ctx, out);
}

// ---------------------------------------------------------------
// Peephole optimizer — runs on the captured blob before saving.
//
// Pass 1: consecutive identical LUI Rx,K  → second becomes NOP.
// Pass 2: [ALU] [branch] [NOP]  where ALU dest ∉ branch reads
//         → move ALU into delay slot, original slot becomes NOP.
// ---------------------------------------------------------------

static inline u32 mips_op(u32 w)  { return w >> 26; }
static inline u32 mips_rs(u32 w)  { return (w >> 21) & 31; }
static inline u32 mips_rt(u32 w)  { return (w >> 16) & 31; }
static inline u32 mips_rd(u32 w)  { return (w >> 11) & 31; }
static inline u32 mips_fn(u32 w)  { return w & 63; }
static inline u32 mips_imm(u32 w) { return w & 0xFFFF; }
static inline bool is_nop(u32 w)  { return w == 0; }

static u32 insn_dest(u32 w)
{
    if (is_nop(w)) return 32;
    u32 op = mips_op(w);
    if (op == 0) {
        u32 fn = mips_fn(w);
        if (fn == 0x08) return 32;   // JR  — no dest
        if (fn == 0x09) return 31;   // JALR — writes $ra
        return mips_rd(w);
    }
    if (op == 1 || op == 2)  return 32;  // REGIMM, J
    if (op == 3)              return 31;  // JAL
    if (op >= 4 && op <= 7)  return 32;  // branches
    if (op >= 0x28 && op <= 0x2e) return 32; // stores
    return mips_rt(w);
}

static bool insn_reads(u32 w, u32 r)
{
    if (r == 0) return false;
    u32 op = mips_op(w);
    if (op == 0) {
        u32 fn = mips_fn(w);
        if (fn == 0x08) return mips_rs(w) == r;
        if (fn == 0x09) return mips_rs(w) == r || mips_rd(w) == r;
        return mips_rs(w) == r || mips_rt(w) == r;
    }
    if (op == 1) return mips_rs(w) == r;
    if (op == 2 || op == 3) return false;
    if (op >= 4 && op <= 7) return mips_rs(w) == r || mips_rt(w) == r;
    if (op == 0x0F) return false; // LUI
    bool reads_rs = mips_rs(w) == r;
    bool reads_rt = (op >= 0x28 && op <= 0x2e) && (mips_rt(w) == r);
    return reads_rs || reads_rt;
}

static bool is_branch(u32 w)
{
    u32 op = mips_op(w);
    if (op == 0) { u32 fn = mips_fn(w); return fn == 0x08 || fn == 0x09; }
    return op >= 1 && op <= 7;
}

static void optimize_block(u32 *words, u32 count)
{
    if (count < 2) return;

    // Pass 1: redundant consecutive LUI
    for (u32 i = 1; i < count; i++) {
        if (mips_op(words[i])   == 0x0F &&
            mips_op(words[i-1]) == 0x0F &&
            mips_rt(words[i])   == mips_rt(words[i-1]) &&
            mips_imm(words[i])  == mips_imm(words[i-1]))
        {
            words[i] = 0;
        }
    }

    // Pass 2: delay-slot NOP filling
    for (u32 i = 1; i + 1 < count; i++) {
        if (!is_branch(words[i])) continue;
        if (!is_nop(words[i+1])) continue;
        u32 cand = words[i-1];
        if (is_nop(cand) || is_branch(cand)) continue;
        u32 cd = insn_dest(cand);
        if (cd != 32 && insn_reads(words[i], cd)) continue;
        words[i+1] = cand;
        words[i-1] = 0;
        i++;
    }
}

// ---------------------------------------------------------------
// Relocation — patches J/JAL targets that fall in [old_base, old_base+old_size)
// ---------------------------------------------------------------

static void relocate_block(u32 *words, u32 count,
                            u32 old_base, u32 old_size, u32 new_base)
{
    for (u32 i = 0; i < count; i++) {
        u32 op = mips_op(words[i]);
        if (op != 2 && op != 3) continue;
        u32 raw    = (words[i] & 0x03FFFFFF) << 2;
        u32 full_old = (old_base & 0xF0000000) | raw;
        if (full_old < old_base || full_old >= old_base + old_size) continue;
        u32 full_new = new_base + (full_old - old_base);
        words[i] = (words[i] & 0xFC000000) | ((full_new >> 2) & 0x03FFFFFF);
    }
}

// ---------------------------------------------------------------
// Public API
// ---------------------------------------------------------------

void aot_init(const char *rom_path)
{
    strncpy(s_aot_path, rom_path, sizeof(s_aot_path) - 5);
    s_aot_path[sizeof(s_aot_path) - 5] = '\0';
    char *dot = strrchr(s_aot_path, '.');
    if (dot && dot > strrchr(s_aot_path, '/') && dot > strrchr(s_aot_path, '\\'))
        *dot = '\0';
    strcat(s_aot_path, ".aot");

    s_num_blocks  = 0;
    s_blob_offset = 0;
    if (!s_blob_buf)
        s_blob_buf = (u8*)malloc(AOT_BLOB_CAP);

    printf("AOT: path = %s\n", s_aot_path);
}

void aot_capture_block(const void *code_ptr, const void *code_end,
                       u32 arm_addr, int procnum, u32 cycles)
{
    if (!s_blob_buf) return;
    if (s_num_blocks >= AOT_MAX_BLOCKS) return;

    u32 size = (u32)((const u8*)code_end - (const u8*)code_ptr);
    if (size == 0 || size > 64 * 1024) return;
    if (s_blob_offset + size > AOT_BLOB_CAP) return;

    u8 *dst = s_blob_buf + s_blob_offset;
    memcpy(dst, code_ptr, size);
    optimize_block((u32*)dst, size / 4);

    AOTBlockEntry *e = &s_entries[s_num_blocks++];
    e->arm_addr    = arm_addr;
    e->procnum     = (u8)procnum;
    e->_pad[0] = e->_pad[1] = e->_pad[2] = 0;
    e->cycles      = cycles;
    e->blob_offset = s_blob_offset;
    e->blob_size   = size;
    sha1_buf(dst, size, e->sha1);
    s_blob_offset += size;
}

void aot_close(void)
{
    if (!s_blob_buf || s_num_blocks == 0) return;

    FILE *f = fopen(s_aot_path, "wb");
    if (!f) { printf("AOT: write fail %s\n", s_aot_path); return; }

    AOTFileHeader hdr;
    hdr.magic          = AOT_MAGIC;
    hdr.version        = AOT_VERSION;
    hdr.num_blocks     = s_num_blocks;
    hdr.code_blob_size = s_blob_offset;
    hdr.cache_base     = s_aot_code_buf ? (u32)s_aot_code_buf : 0;
    hdr.cache_size     = AOT_CODE_BUF_SIZE;
    hdr._pad[0] = hdr._pad[1] = 0;

    fwrite(&hdr,       sizeof(hdr),              1,            f);
    fwrite(s_entries,  sizeof(AOTBlockEntry), s_num_blocks,    f);
    fwrite(s_blob_buf, 1,                s_blob_offset,        f);
    fclose(f);

    printf("AOT: saved %lu blocks (%lu bytes) to %s\n",
           (unsigned long)s_num_blocks, (unsigned long)s_blob_offset, s_aot_path);
}

int aot_load(void)
{
    FILE *f = fopen(s_aot_path, "rb");
    if (!f) { printf("AOT: no cache at %s\n", s_aot_path); return -1; }

    AOTFileHeader hdr;
    if (fread(&hdr, sizeof(hdr), 1, f) != 1 ||
        hdr.magic   != AOT_MAGIC  ||
        hdr.version != AOT_VERSION)
    {
        printf("AOT: bad header\n");
        fclose(f); return -1;
    }

    if (hdr.num_blocks > AOT_MAX_BLOCKS || hdr.code_blob_size > AOT_BLOB_CAP) {
        printf("AOT: file too large\n");
        fclose(f); return -1;
    }

    AOTBlockEntry *entries = (AOTBlockEntry*)malloc(sizeof(AOTBlockEntry) * hdr.num_blocks);
    if (!entries) { fclose(f); return -1; }

    if (fread(entries, sizeof(AOTBlockEntry), hdr.num_blocks, f) != hdr.num_blocks) {
        printf("AOT: truncated entries\n");
        free(entries); fclose(f); return -1;
    }

    u8 *blob = (u8*)malloc(hdr.code_blob_size);
    if (!blob) { free(entries); fclose(f); return -1; }

    if (fread(blob, 1, hdr.code_blob_size, f) != hdr.code_blob_size) {
        printf("AOT: truncated blob\n");
        free(blob); free(entries); fclose(f); return -1;
    }
    fclose(f);

    if (!aot_buf_ensure()) {
        printf("AOT: cannot alloc buffer\n");
        free(blob); free(entries); return -1;
    }

    u32 old_base   = hdr.cache_base;
    u32 old_size   = hdr.cache_size;
    u32 new_base   = (u32)s_aot_code_buf;
    bool need_reloc = (new_base != old_base);

    aot_buf_begin();

    int loaded = 0;
    for (u32 i = 0; i < hdr.num_blocks; i++) {
        AOTBlockEntry *e = &entries[i];
        if (e->blob_offset + e->blob_size > hdr.code_blob_size) continue;
        if (e->blob_size == 0) continue;

        u8 digest[20];
        sha1_buf(blob + e->blob_offset, e->blob_size, digest);
        if (memcmp(digest, e->sha1, 20) != 0) {
            printf("AOT: SHA1 fail @%08lX\n", (unsigned long)e->arm_addr);
            continue;
        }

        if (JIT_COMPILED_FUNC(e->arm_addr, e->procnum) != 0) continue;
        if (aot_buf_free() < e->blob_size + 64) {
            printf("AOT: buffer full at block %lu\n", (unsigned long)i);
            break;
        }

        void *dst = emit_GetPtr();
        memcpy(dst, blob + e->blob_offset, e->blob_size);

        if (need_reloc)
            relocate_block((u32*)dst, e->blob_size / 4, old_base, old_size, new_base);

        emit_Skip(e->blob_size);
        while (emit_getCurrAdr() & 0x3) emit_Skip(4);

        make_address_range_executable((u32)dst, (u32)dst + e->blob_size);
        JIT_COMPILED_FUNC(e->arm_addr, e->procnum) = (uintptr_t)dst;
        loaded++;
    }

    aot_buf_end();
    free(blob);
    free(entries);

    printf("AOT: loaded %d/%lu blocks\n", loaded, (unsigned long)hdr.num_blocks);
    return loaded;
}

// ---------------------------------------------------------------
// Pre-compilation
// ---------------------------------------------------------------

bool aot_precompiling = false;

struct ScanRegion { u32 base; u32 size; };
static const ScanRegion ARM9_REGIONS[] = {
    { 0x02000000, 4 * 1024 * 1024 },
    { 0x01000000, 0x8000           },
};

void aot_precompile(void)
{
    if (!aot_buf_ensure()) {
        printf("AOT: cannot alloc precompile buffer\n");
        return;
    }

    pspDebugScreenClear();
    pspDebugScreenSetXY(0, 0);
    pspDebugScreenPrintf("AOT pre-compile...\n");

    armcpu_t saved_cpu;
    memcpy(&saved_cpu, &NDS_ARM9, sizeof(armcpu_t));
    NDS_ARM9.CPSR.bits.T = 0;

    aot_precompiling = true;
    aot_buf_begin();

    u32 total = 0;
    for (u32 r = 0; r < sizeof(ARM9_REGIONS)/sizeof(ARM9_REGIONS[0]); r++)
        total += ARM9_REGIONS[r].size / 4;

    u32 scanned = 0, compiled = 0;
    int last_pct = -1;

    for (u32 r = 0; r < sizeof(ARM9_REGIONS)/sizeof(ARM9_REGIONS[0]); r++) {
        u32 base = ARM9_REGIONS[r].base;
        u32 size = ARM9_REGIONS[r].size;

        for (u32 off = 0; off < size; off += 4, scanned++) {
            u32 addr = base + off;

            if (JIT_COMPILED_FUNC(addr, 0) != 0) continue;

            u32 word = _MMU_read32<0, MMU_AT_CODE>(addr);
            if (word == 0x00000000 || word == 0xFFFFFFFF) continue;

            if (aot_buf_free() < 8 * 1024) {
                printf("AOT: buffer full after %lu blocks\n", (unsigned long)compiled);
                goto done;
            }

            NDS_ARM9.instruct_adr     = addr;
            NDS_ARM9.next_instruction = addr + 4;
            NDS_ARM9.CPSR.bits.T      = 0;

            arm_jit_compile<0>();

            if (JIT_COMPILED_FUNC(addr, 0) != 0) {
                compiled++;
                u32 next = NDS_ARM9.next_instruction;
                if (next > addr + 4 && next < base + size)
                    off = next - base - 4;
            }

            int pct = (int)((u64)scanned * 100 / total);
            if (pct != last_pct) {
                last_pct = pct;
                pspDebugScreenSetXY(0, 1);
                pspDebugScreenPrintf("[");
                for (int j = 0; j < 50; j++)
                    pspDebugScreenPrintf(j < pct/2 ? "#" : " ");
                pspDebugScreenPrintf("] %3d%%  %lu blocks\n", pct, (unsigned long)compiled);
            }
        }
    }

done:
    aot_buf_end();
    aot_precompiling = false;

    memcpy(&NDS_ARM9, &saved_cpu, sizeof(armcpu_t));

    pspDebugScreenSetXY(0, 3);
    pspDebugScreenPrintf("AOT: %lu blocks. Saving...\n", (unsigned long)compiled);
    aot_close();
    pspDebugScreenPrintf("AOT: done.\n");
    sceKernelDelayThread(1500000);
}
