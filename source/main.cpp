/* main.c - this file is part of DeSmuME
 *
 * Copyright (C) 2006-2015 DeSmuME Team
 * Copyright (C) 2007 Pascal Giard (evilynux)
 * Used under fair use by the DSonPSP team, 2019
 *
 * This file is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * This file is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; see the file COPYING.  If not, write to
 * the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <psppower.h>
#include <pspdebug.h>
#include <pspctrl.h>
#include <pspdisplay.h>
#include <pspsuspend.h>
#include <pspkernel.h>
#include <psprtc.h>

#include "pspdmac.h"

#include "PSP/FrontEnd.h"
#include "PSP/video.h"

#include "NDSSystem.h"
#include "GPU.h"
#include "SPU.h"
#include "sndsdl.h"
#include "sndpsp.h"
#include "ctrlssdl.h"
#include "slot2.h"

#include "render3D.h"
#include "rasterize.h"

#include <unistd.h>
#include "dirent.h"
#include "PSP/vram.h"
#include "PSP/PSPDisplay.h"

//#define PROFILE

#ifdef PROFILE
#include "pspprof.h"
#endif

#include "aot_cache.h"
#include "armcpu.h"

PSP_MODULE_INFO("DesmuME PSP", 0, 3, 0);

// ---- JIT crash handler ----
extern volatile u32 jit_last_guest_pc;
extern armcpu_t NDS_ARM9;
extern armcpu_t NDS_ARM7;

static void jit_exception_handler(PspDebugRegBlock *regs)
{
    pspDebugScreenInit();
    pspDebugScreenSetBackColor(0x00000000);
    pspDebugScreenSetTextColor(0x00FF0000);
    pspDebugScreenClear();

    pspDebugScreenPrintf("*** JIT CRASH ***\n\n");
    pspDebugScreenPrintf("Last guest PC : 0x%08X\n", jit_last_guest_pc);
    pspDebugScreenPrintf("MIPS EPC      : 0x%08X\n", regs->epc);
    pspDebugScreenPrintf("Cause         : 0x%08X\n", regs->cause);
    pspDebugScreenPrintf("BadVAddr      : 0x%08X\n", regs->badvaddr);
    pspDebugScreenPrintf("Status        : 0x%08X\n\n", regs->status);

    pspDebugScreenPrintf("-- ARM9 regs --\n");
    for (int i = 0; i < 16; i++) {
        pspDebugScreenPrintf("R%02d=0x%08X  ", i, NDS_ARM9.R[i]);
        if ((i & 3) == 3) pspDebugScreenPrintf("\n");
    }
    pspDebugScreenPrintf("CPSR=0x%08X  thumb=%d\n\n", NDS_ARM9.CPSR.val, NDS_ARM9.CPSR.bits.T);

    pspDebugScreenPrintf("-- MIPS regs at crash --\n");
    pspDebugScreenPrintf("at=0x%08X v0=0x%08X v1=0x%08X\n", regs->r[1], regs->r[2], regs->r[3]);
    pspDebugScreenPrintf("a0=0x%08X a1=0x%08X a2=0x%08X a3=0x%08X\n",
                          regs->r[4], regs->r[5], regs->r[6], regs->r[7]);
    pspDebugScreenPrintf("t0=0x%08X t1=0x%08X t2=0x%08X t3=0x%08X\n",
                          regs->r[8], regs->r[9], regs->r[10], regs->r[11]);
    pspDebugScreenPrintf("k0=0x%08X sp=0x%08X ra=0x%08X\n\n",
                          regs->r[26], regs->r[29], regs->r[31]);

    pspDebugScreenPrintf("Press X to exit.\n");

    SceCtrlData pad;
    while (1) {
        sceCtrlReadBufferPositive(&pad, 1);
        if (pad.Buttons & PSP_CTRL_CROSS) break;
        sceKernelDelayThread(100000);
    }
    sceKernelExitGame();
}
// ---- end crash handler ----

PSP_MAIN_THREAD_ATTR(PSP_THREAD_ATTR_USER | PSP_THREAD_ATTR_VFPU);
PSP_HEAP_SIZE_KB(-2048);

char rom_filename[256];

volatile bool execute = false;

SoundInterface_struct *SNDCoreList[] = {
	&SNDDummy,
	&SNDPSP,
	NULL};

GPU3DInterface *core3DList[] = {
	&gpu3DNull,
	&gpu3DRasterize,
	//  &gpu3DGU,
	NULL};

const char *save_type_names[] = {
	"Autodetect",
	"EEPROM 4kbit",
	"EEPROM 64kbit",
	"EEPROM 512kbit",
	"FRAM 256kbit",
	"FLASH 2mbit",
	"FLASH 4mbit",
	NULL};

configured_features my_config;

extern int userEnableProfiler();

// TAKEN FROM https://github.com/albe/openTri/blob/main/src/streams/streams.c#L22
void *memcpy_vfpu(void *dst, void *src, unsigned int size)
{
	u8 *src8 = (u8 *)src;
	u8 *dst8 = (u8 *)dst;

	// < 8 isn't worth trying any optimisations...
	if (size < 8)
	{
		while (size--)
		{
			*dst8++ = *src8++;
		}
		return (dst);
	}

	// < 64 means we don't gain anything from using vfpu...
	if (size < 64)
	{
		// Align dst on 4 bytes or just resume if already done
		while (((((u32)dst8) & 0x3) != 0) && size)
		{
			*dst8++ = *src8++;
			size--;
		}
		if (size < 4)
		{
			while (size--)
			{
				*dst8++ = *src8++;
			}
			return (dst);
		}

		// We are dst aligned now and >= 4 bytes to copy
		u32 *src32 = (u32 *)src8;
		u32 *dst32 = (u32 *)dst8;
		switch (((u32)src8) & 0x3)
		{
		case 0:
			while (size & 0xC)
			{
				*dst32++ = *src32++;
				size -= 4;
			}
			if (size == 0)
				return (dst); // fast out
			while (size >= 16)
			{
				*dst32++ = *src32++;
				*dst32++ = *src32++;
				*dst32++ = *src32++;
				*dst32++ = *src32++;
				size -= 16;
			}
			if (size == 0)
				return (dst); // fast out
			src8 = (u8 *)src32;
			dst8 = (u8 *)dst32;
			break;
		default:
		{
			register u32 a, b, c, d;
			while (size >= 4)
			{
				a = *src8++;
				b = *src8++;
				c = *src8++;
				d = *src8++;
				*dst32++ = (d << 24) | (c << 16) | (b << 8) | a;
				size -= 4;
			}
			if (size == 0)
				return (dst); // fast out
			dst8 = (u8 *)dst32;
		}
		break;
		}
		while (size--)
		{
			*dst8++ = *src8++;
		}

		return (dst);
	}

	// Align dst on 16 bytes to gain from vfpu aligned stores
	while ((((u32)dst8) & 0xF) != 0 && size)
	{
		*dst8++ = *src8++;
		size--;
	}

	// We use uncached dst to use VFPU writeback and free cpu cache for src only
	u8 *udst8 = (u8 *)((u32)dst8 | 0x40000000);
	// We need the 64 byte aligned address to make sure the dcache is invalidated correctly
	u8 *dst64a = (u8 *)((u32)dst8 & ~0x3F);
	// Invalidate the first line that matches up to the dst start
	if (size >= 64)
		asm(".set	push\n"		 // save assembler option
			".set	noreorder\n" // suppress reordering
			"cache 0x1B, 0(%0)\n"
			"addiu	%0, %0, 64\n"
			"sync\n"
			".set	pop\n"
			: "+r"(dst64a));
	switch (((u32)src8 & 0xF))
	{
	// src aligned on 16 bytes too? nice!
	case 0:
		while (size >= 64)
		{
			asm(".set	push\n"			// save assembler option
				".set	noreorder\n"	// suppress reordering
				"cache	0x1B,  0(%2)\n" // Dcache writeback invalidate
				"lv.q	c000,  0(%1)\n"
				"lv.q	c010, 16(%1)\n"
				"lv.q	c020, 32(%1)\n"
				"lv.q	c030, 48(%1)\n"
				"sync\n" // Wait for allegrex writeback
				"sv.q	c000,  0(%0), wb\n"
				"sv.q	c010, 16(%0), wb\n"
				"sv.q	c020, 32(%0), wb\n"
				"sv.q	c030, 48(%0), wb\n"
				// Lots of variable updates... but get hidden in sv.q latency anyway
				"addiu  %3, %3, -64\n"
				"addiu	%2, %2, 64\n"
				"addiu	%1, %1, 64\n"
				"addiu	%0, %0, 64\n"
				".set	pop\n" // restore assembler option
				: "+r"(udst8), "+r"(src8), "+r"(dst64a), "+r"(size)
				:
				: "memory");
		}
		if (size > 16)
		{
			// Invalidate the last cache line where the max remaining 63 bytes are
			asm(".set	push\n"		 // save assembler option
				".set	noreorder\n" // suppress reordering
				"cache	0x1B, 0(%0)\n"
				"sync\n"
				".set	pop\n" // restore assembler option
				::"r"(dst64a));
			while (size >= 16)
			{
				asm(".set	push\n"		 // save assembler option
					".set	noreorder\n" // suppress reordering
					"lv.q	c000, 0(%1)\n"
					"sv.q	c000, 0(%0), wb\n"
					// Lots of variable updates... but get hidden in sv.q latency anyway
					"addiu	%2, %2, -16\n"
					"addiu	%1, %1, 16\n"
					"addiu	%0, %0, 16\n"
					".set	pop\n" // restore assembler option
					: "+r"(udst8), "+r"(src8), "+r"(size)
					:
					: "memory");
			}
		}
		asm(".set	push\n"		 // save assembler option
			".set	noreorder\n" // suppress reordering
			"vflush\n"			 // Flush VFPU writeback cache
			".set	pop\n"		 // restore assembler option
		);
		dst8 = (u8 *)((u32)udst8 & ~0x40000000);
		break;
	// src is only qword unaligned but word aligned? We can at least use ulv.q
	case 4:
	case 8:
	case 12:
		while (size >= 64)
		{
			asm(".set	push\n"			// save assembler option
				".set	noreorder\n"	// suppress reordering
				"cache	0x1B,  0(%2)\n" // Dcache writeback invalidate
				"ulv.q	c000,  0(%1)\n"
				"ulv.q	c010, 16(%1)\n"
				"ulv.q	c020, 32(%1)\n"
				"ulv.q	c030, 48(%1)\n"
				"sync\n" // Wait for allegrex writeback
				"sv.q	c000,  0(%0), wb\n"
				"sv.q	c010, 16(%0), wb\n"
				"sv.q	c020, 32(%0), wb\n"
				"sv.q	c030, 48(%0), wb\n"
				// Lots of variable updates... but get hidden in sv.q latency anyway
				"addiu  %3, %3, -64\n"
				"addiu	%2, %2, 64\n"
				"addiu	%1, %1, 64\n"
				"addiu	%0, %0, 64\n"
				".set	pop\n" // restore assembler option
				: "+r"(udst8), "+r"(src8), "+r"(dst64a), "+r"(size)
				:
				: "memory");
		}
		if (size > 16)
			// Invalidate the last cache line where the max remaining 63 bytes are
			asm(".set	push\n"		 // save assembler option
				".set	noreorder\n" // suppress reordering
				"cache	0x1B, 0(%0)\n"
				"sync\n"
				".set	pop\n" // restore assembler option
				::"r"(dst64a));
		while (size >= 16)
		{
			asm(".set	push\n"		 // save assembler option
				".set	noreorder\n" // suppress reordering
				"ulv.q	c000, 0(%1)\n"
				"sv.q	c000, 0(%0), wb\n"
				// Lots of variable updates... but get hidden in sv.q latency anyway
				"addiu	%2, %2, -16\n"
				"addiu	%1, %1, 16\n"
				"addiu	%0, %0, 16\n"
				".set	pop\n" // restore assembler option
				: "+r"(udst8), "+r"(src8), "+r"(size)
				:
				: "memory");
		}
		asm(".set	push\n"		 // save assembler option
			".set	noreorder\n" // suppress reordering
			"vflush\n"			 // Flush VFPU writeback cache
			".set	pop\n"		 // restore assembler option
		);
		dst8 = (u8 *)((u32)udst8 & ~0x40000000);
		break;
	// src not aligned? too bad... have to use unaligned reads
	default:
		while (size >= 64)
		{
			asm(".set	push\n"		 // save assembler option
				".set	noreorder\n" // suppress reordering
				"cache 0x1B,  0(%2)\n"

				"lwr	 $8,  0(%1)\n" //
				"lwl	 $8,  3(%1)\n" // $8  = *(s + 0)
				"lwr	 $9,  4(%1)\n" //
				"lwl	 $9,  7(%1)\n" // $9  = *(s + 4)
				"lwr	$10,  8(%1)\n" //
				"lwl	$10, 11(%1)\n" // $10 = *(s + 8)
				"lwr	$11, 12(%1)\n" //
				"lwl	$11, 15(%1)\n" // $11 = *(s + 12)
				"mtv	 $8, s000\n"
				"mtv	 $9, s001\n"
				"mtv	$10, s002\n"
				"mtv	$11, s003\n"

				"lwr	 $8, 16(%1)\n"
				"lwl	 $8, 19(%1)\n"
				"lwr	 $9, 20(%1)\n"
				"lwl	 $9, 23(%1)\n"
				"lwr	$10, 24(%1)\n"
				"lwl	$10, 27(%1)\n"
				"lwr	$11, 28(%1)\n"
				"lwl	$11, 31(%1)\n"
				"mtv	 $8, s010\n"
				"mtv	 $9, s011\n"
				"mtv	$10, s012\n"
				"mtv	$11, s013\n"

				"lwr	 $8, 32(%1)\n"
				"lwl	 $8, 35(%1)\n"
				"lwr	 $9, 36(%1)\n"
				"lwl	 $9, 39(%1)\n"
				"lwr	$10, 40(%1)\n"
				"lwl	$10, 43(%1)\n"
				"lwr	$11, 44(%1)\n"
				"lwl	$11, 47(%1)\n"
				"mtv	 $8, s020\n"
				"mtv	 $9, s021\n"
				"mtv	$10, s022\n"
				"mtv	$11, s023\n"

				"lwr	 $8, 48(%1)\n"
				"lwl	 $8, 51(%1)\n"
				"lwr	 $9, 52(%1)\n"
				"lwl	 $9, 55(%1)\n"
				"lwr	$10, 56(%1)\n"
				"lwl	$10, 59(%1)\n"
				"lwr	$11, 60(%1)\n"
				"lwl	$11, 63(%1)\n"
				"mtv	 $8, s030\n"
				"mtv	 $9, s031\n"
				"mtv	$10, s032\n"
				"mtv	$11, s033\n"

				"sync\n"
				"sv.q 	c000,  0(%0), wb\n"
				"sv.q 	c010, 16(%0), wb\n"
				"sv.q 	c020, 32(%0), wb\n"
				"sv.q 	c030, 48(%0), wb\n"
				// Lots of variable updates... but get hidden in sv.q latency anyway
				"addiu	%3, %3, -64\n"
				"addiu	%2, %2, 64\n"
				"addiu	%1, %1, 64\n"
				"addiu	%0, %0, 64\n"
				".set	pop\n" // restore assembler option
				: "+r"(udst8), "+r"(src8), "+r"(dst64a), "+r"(size)
				:
				: "$8", "$9", "$10", "$11", "memory");
		}
		if (size > 16)
			// Invalidate the last cache line where the max remaining 63 bytes are
			asm(".set	push\n"		 // save assembler option
				".set	noreorder\n" // suppress reordering
				"cache	0x1B, 0(%0)\n"
				"sync\n"
				".set	pop\n" // restore assembler option
				::"r"(dst64a));
		while (size >= 16)
		{
			asm(".set	push\n"		   // save assembler option
				".set	noreorder\n"   // suppress reordering
				"lwr	 $8,  0(%1)\n" //
				"lwl	 $8,  3(%1)\n" // $8  = *(s + 0)
				"lwr	 $9,  4(%1)\n" //
				"lwl	 $9,  7(%1)\n" // $9  = *(s + 4)
				"lwr	$10,  8(%1)\n" //
				"lwl	$10, 11(%1)\n" // $10 = *(s + 8)
				"lwr	$11, 12(%1)\n" //
				"lwl	$11, 15(%1)\n" // $11 = *(s + 12)
				"mtv	 $8, s000\n"
				"mtv	 $9, s001\n"
				"mtv	$10, s002\n"
				"mtv	$11, s003\n"

				"sv.q	c000, 0(%0), wb\n"
				// Lots of variable updates... but get hidden in sv.q latency anyway
				"addiu	%2, %2, -16\n"
				"addiu	%1, %1, 16\n"
				"addiu	%0, %0, 16\n"
				".set	pop\n" // restore assembler option
				: "+r"(udst8), "+r"(src8), "+r"(size)
				:
				: "$8", "$9", "$10", "$11", "memory");
		}
		asm(".set	push\n"		 // save assembler option
			".set	noreorder\n" // suppress reordering
			"vflush\n"			 // Flush VFPU writeback cache
			".set	pop\n"		 // restore assembler option
		);
		dst8 = (u8 *)((u32)udst8 & ~0x40000000);
		break;
	}

	// Copy the remains byte per byte...
	while (size--)
	{
		*dst8++ = *src8++;
	}

	return (dst);
}

void PrintfXY(const char *text, int x, int y)
{
	pspDebugScreenSetXY(x, y);
	pspDebugScreenPrintf(text);
}

void WriteLog(char *msg)
{
	FILE *fd;
	fd = fopen("debug_log.txt", "a");
	fprintf(fd, "%s\n", msg);
	fclose(fd);
}

void WriteHash(char *msg)
{
	FILE *fd;
	fd = fopen("hashes.txt", "a");
	fprintf(fd, "%s\n", msg);
	fclose(fd);
}

bool audio_inited = false;

#define PSP_AUDIO_SAMPLE_MAX 735 * 4

void EMU_Conf()
{

	// ReAddress display to 32bit vram
	pspDebugScreenInitEx((void *)(0x44000000), PSP_DISPLAY_PIXEL_FORMAT_5551, 1);

	// Settings are now chosen in the split-screen ROM menu (DSEmuGui) and already
	// finalized into my_config there; no separate DoConfig pass is needed.
	FinalizeMainSettings(&my_config);

	NDS_3D_ChangeCore(my_config.Render3D);
	backup_setManualBackupType(my_config.savetype);

	pspDebugScreenClear();

	if (my_config.enable_sound && !audio_inited)
	{
		SPU_ChangeSoundCore(SNDCORE_PSP, PSP_AUDIO_SAMPLE_MAX);
		SPU_SetSynchMode(0, 0 /*CommonSettings.SPU_sync_method*/);
		audio_inited = true;
	}
	else if (audio_inited && !my_config.enable_sound)
	{
		SPU_ChangeSoundCore(SNDCORE_DUMMY, 0);
		audio_inited = false;
	}

	PrintfXY("ROM: ", 0, 1);
	PrintfXY(gameInfo.ROMname, 5, 1);

	char number;
	sprintf(&number, "%1d", my_config.frameskip);
	PrintfXY("Frameskip: ", 55, 1);
	PrintfXY(&number, 65, 1);
}

void ChangeRom(bool reset)
{
	if (reset)
	{
		NDS_Reset();
	}
	pspDebugScreenClear();

	
	DSEmuGui("", rom_filename);
	EMU_Conf();

	if (NDS_LoadROM(rom_filename) < 0)
	{
		WriteLog("ERROR ROM:");
		WriteLog(rom_filename);
		exit(-1);
	}

	//userEnableProfiler();
	execute = true;
}

void ResetRom()
{

	NDS_Reset();
	pspDebugScreenClear();

	if (NDS_LoadROM(rom_filename) < 0)
	{
		WriteLog("ERROR ROM:");
		WriteLog(rom_filename);
		exit(-1);
	}

	execute = true;
}

void deinit(){
	#ifdef PROFILE
	gprof_stop("desmume.out", 1);
	#endif
	NDS_DeInit();
	sceKernelExitGame();
}

int main(int argc, char **argv)
{
	/* the firmware settings */
	struct NDS_fw_config_data fw_config;

	scePowerSetClockFrequency(333, 333, 166);

	pspDebugScreenInitEx((void *)(0x44000000), PSP_DISPLAY_PIXEL_FORMAT_5551, 1);
	//pspDebugInstallErrorHandler(jit_exception_handler);

	// disable fpu exceptions
	asm volatile(
		"cfc1    $2, $31\n"
		"lui     $8, 0x80\n"
		"and     $8, $2, $8\n" // Mask off all bits except for 23 of FCR
		"ctc1    $8, $31\n");

	Init_PSP_DISPLAY_FRAMEBUFF();

	extern void initMeEngine();
	initMeEngine();

	NDS_Init();

	/* default the firmware settings, they may get changed later */
	NDS_FillDefaultFirmwareConfigData(&fw_config);

	slot2_Init();

	slot2_Change(NDS_SLOT2_NONE);

	/* Create the dummy firmware */
	NDS_CreateDummyFirmware(&fw_config);

	#ifdef PROFILE
	execute = true;
	NDS_LoadROM("test.nds");
	my_config.Render3D = true;
	my_config.showfps = true;
#else
	ChangeRom(false);
#endif

	extern void test_jit_func();
	test_jit_func();

	EMU_SCREEN(true, true);
	#ifdef PROFILE
	gprof_start();
	#endif

	NDS_setup();
	
	return 0;
}

/*

no loop qui, struttura tutto in questo modo:

main chiama funzione bloccante: emulate system

emulate system sarà:
do
{
	run_cpu_until_(cycles or idle_loop)
	
	run_dma / run_timers

	run_irq

	draw_display

	calculate_frameskip / framerate
}while(exit);

in assembly

il run_cpu sarà:

cycle_cpu = get_next_event()

allocate_guest_regs

label_run:
	v1 = extract_block()

	if v0 == 0: blocco non trovato
		// decodifico il blocco
		jmp block_decode()

	// eseguo il blocco
	jmp v0

	// controllo che sono con i cicli corretti
	subu cycle_reg, cycle_reg, cycles

	// se idle loop skippiamo il blocco
	movz cycle_reg, zero, idle_reg

	// se ci sono ancora cicli da consumare, continua con l'esecuzione
	bgz cycle_reg, label_run

// passiamo al resto del'hardware
deallocate_guest_reg






*/