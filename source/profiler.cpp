#include <pspkernel.h>
#include <cstdint>
#include <cstdio>

#include "me_engine.h"

#define PROFILER_REG_BASE 0x1C400000
#define PROFILER_REG_COUNT 21

void usrDebugProfilerEnable(void)
{
	_sw(1, PROFILER_REG_BASE);
}

void usrDebugProfilerDisable(void)
{
	_sw(0, PROFILER_REG_BASE);
	asm("sync");
}

void usrDebugProfilerClear(void)
{
	u32 addr;
	int i;

	addr = PROFILER_REG_BASE;
	
	for(i = 1; i < PROFILER_REG_COUNT; i++)
	{
		addr += 4;
		_sw(0, addr);
	}
}

extern "C"
{

	typedef struct _PspDebugProfilerRegs2
	{
		volatile u32 enable;
		volatile u32 systemck;
		volatile u32 cpuck;
		volatile u32 totalstall; 
		volatile u32 internal;
		volatile u32 memory;
		volatile u32 copz;
		volatile u32 vfpu;
		volatile u32 sleep;
		volatile u32 bus_access;
		volatile u32 uncached_load;
		volatile u32 uncached_store;
		volatile u32 cached_load;
		volatile u32 cached_store;
		volatile u32 i_miss;
		volatile u32 d_miss;
		volatile u32 d_writeback;
		volatile u32 cop0_inst;
		volatile u32 fpu_inst;
		volatile u32 vfpu_inst;
		volatile u32 local_bus;
		volatile u32 waste[5];
	} PspDebugProfilerRegs2;

	void usrDebugProfilerGetRegs(PspDebugProfilerRegs2 *regs);
}

int enableProfiler()
{
    usrDebugProfilerDisable();
	usrDebugProfilerClear();
	usrDebugProfilerEnable();
    return 0;
}

int printProfiler()
{
    PspDebugProfilerRegs2 regs;
    usrDebugProfilerGetRegs(&regs);
    
    //printf("System clock: %08x\n", regs.systemck);
    printf("CPU clock: %08x\n", regs.cpuck);
    printf("Internal: %08x\n", regs.internal);
    printf("Memory: %08x\n", regs.memory);
    printf("COPZ: %08x\n", regs.copz);
    printf("VFPU: %08x\n", regs.vfpu);
    printf("Sleep: %08x\n", regs.sleep);
    printf("Bus Access: %08x\n", regs.bus_access);
    printf("Uncached Load: %08x\n", regs.uncached_load);
    printf("Uncached Store: %08x\n", regs.uncached_store);
    printf("Cached Load: %08x\n", regs.cached_load);
    printf("Cached Store: %08x\n", regs.cached_store);
    printf("I Miss: %08x\n", regs.i_miss);
    printf("D Miss: %08x\n", regs.d_miss);
    printf("D Writeback: %08x\n", regs.d_writeback);
    printf("COP0 Inst: %08x\n", regs.cop0_inst);
    printf("FPU Inst: %08x\n", regs.fpu_inst);
    printf("VFPU Inst: %08x\n", regs.vfpu_inst);

    printf(" -- -- -- --\n");
    return 0;
}

int userEnableProfiler(){
        return kcall(&enableProfiler);
}

int userPrintProfiler(){
        return kcall(&printProfiler);
}