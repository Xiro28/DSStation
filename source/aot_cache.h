#ifndef AOT_CACHE_H
#define AOT_CACHE_H

#include "types.h"

// Binary format of <romname>.aot:
//
//  AOTFileHeader
//  AOTBlockEntry[header.num_blocks]
//  MIPS bytecode blob (header.code_blob_size bytes)
//
// Relocation: every j/jal inside each blob that targets the old code cache
// region is patched on load to the equivalent offset in the new cache base.
// The old cache base is stored in the header so the patcher can distinguish
// cache-internal jumps from calls to fixed runtime helpers.

#define AOT_MAGIC   0x544F4144u  // "DAOT"
#define AOT_VERSION 54u           // bumped: cycles-in-register ($s3) reintroduced behind JIT_CYCLES_IN_REG

struct AOTFileHeader {
    u32 magic;
    u32 version;
    u32 num_blocks;
    u32 code_blob_size;
    u32 cache_base;       // CodeCache pointer value at capture time
    u32 cache_size;       // CODE_SIZE at capture time
    u32 _pad[2];
};

struct AOTBlockEntry {
    u32 arm_addr;
    u8  procnum;          // 0 = ARM9, 1 = ARM7
    u8  _pad[3];
    u32 cycles;
    u32 blob_offset;      // byte offset into code blob
    u32 blob_size;        // byte size of MIPS code
    u8  sha1[20];         // SHA1 of the MIPS blob after optimization, before relocation
};

// Call once with the path of the ROM being played.
void aot_init(const char *rom_path);

// Capture one JIT-compiled block.  code_ptr..code_end is the live MIPS range.
void aot_capture_block(const void *code_ptr, const void *code_end,
                       u32 arm_addr, int procnum, u32 cycles);

// Load .aot, patch relocations, populate JIT table.
// Returns blocks loaded, or -1 on error/missing file.
int  aot_load(void);

// Flush capture buffer to disk.
void aot_close(void);

// Pre-compile all ARM9 code pages found in the loaded ROM and write the
// result to the .aot file.  Shows a progress screen.
// Call after NDS_LoadROM() but before NDS_setup().
void aot_precompile(void);

// True while aot_precompile() is running.
// arm_jit_compile() checks this to skip executing NitroSDK HLE stubs.
extern bool aot_precompiling;

// Re-register AOT blocks into the JIT table after arm_jit_reset clears it.
void aot_reregister(void);

#endif // AOT_CACHE_H
