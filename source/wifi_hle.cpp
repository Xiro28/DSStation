#include "wifi_hle.h"

#include "MD_FIFO.h"
#include "MMU.h"
#include "wifi.h"
#include "NDSSystem.h"

u32 IPCCmdAddr;
u32 SharedMem[2];

u16 Channel;


void WiFIReset()
{
    IPCCmdAddr = 0;

    SharedMem[0] = 0;
    SharedMem[1] = 0;

    Channel = 0;

    u16 chanmask = 0x2082;
    _MMU_ARM7_write16(0x027FFCFA, chanmask);
}

void WifiIPCReply(u16 cmd, u16 status, int numextra=0, u16* extra=nullptr)
{
    u32 replybuf = _MMU_ARM7_read32(SharedMem[0]+0x8);
    _MMU_ARM7_write16(replybuf+0x00, cmd);
    _MMU_ARM7_write16(replybuf+0x02, status);

    if (cmd == 0xA)
    {
       if (numextra == 1)
        {
            _MMU_ARM7_write16(replybuf+0x8, 4);
            _MMU_ARM7_write16(replybuf+0x10, extra[0]);
            _MMU_ARM7_write16(replybuf+0x12, 0);
        }
    }else{
        for (int i = 0; i < numextra; i++)
        {
            _MMU_ARM7_write16(replybuf+0x8+(i*2), extra[i]);
        }
    }

    extern void SendIPCReply(u32 service, u32 data, u32 flag = 0);
    SendIPCReply(0xA, replybuf, 0);

}

void WifiOnIPCRequest(u32 addr)
{
    IPCCmdAddr = addr;

    u16 cmd = _MMU_ARM7_read16(addr);
    cmd &= ~0x8000;

    if (cmd < 0x2E)
    {
        _MMU_ARM7_write32(SharedMem[1]+0x4, 1);
        _MMU_ARM7_write16(SharedMem[1]+0x2, cmd);

        //printf("WIFI HLE: IPC request %04X at %08X\n", cmd, addr);

        switch (cmd)
        {
        case 0x0: // init
            {
                SharedMem[0] = _MMU_ARM7_read32(addr+0x4);
                SharedMem[1] = _MMU_ARM7_read32(addr+0x8);
                u32 respbuf = _MMU_ARM7_read32(addr+0xC);

                _MMU_ARM7_write32(SharedMem[0], SharedMem[1]);
                _MMU_ARM7_write32(SharedMem[0]+0x8, respbuf);


                _MMU_ARM7_write16(SharedMem[1], 2);
                _MMU_ARM7_write16(SharedMem[1] + 0x4, 0);
                WifiIPCReply(0x0, 0);
            }
            break;

        case 0x2: // deinit
            {
                u16 status = _MMU_ARM7_read16(SharedMem[1]);
               
                _MMU_ARM7_write16(SharedMem[1], 0);
                _MMU_ARM7_write16(SharedMem[1] + 0x4, 0);
                WifiIPCReply(0x2, 0);
            }
            break;
        

        case 0xA: // start host scan
            {
                u16 status = _MMU_ARM7_read16(SharedMem[1]);
                if (status != 2 && status != 3 && status != 5)
                {
                    u16 ext = 4;
                    WifiIPCReply(0xA, 3, 1, &ext);
                    break;
                }

                Channel = _MMU_ARM7_read16(addr+0x2);

                _MMU_ARM7_write16(SharedMem[1], 5);
                _MMU_ARM7_write16(SharedMem[1] + 0x4, 0);

                s64 cycles = 33513982LL * 1024LL;
                s64 delay = (cycles + 999999LL) / 1000000LL;
                NDS_RescheduleWiFi(delay);
            }
            return;

        case 0xB: // stop host scan
        {

            u16 status = _MMU_ARM7_read16(SharedMem[1]);
            if (status != 5)
            {
                WifiIPCReply(0xB, 3);
                break;
            }
            
            _MMU_ARM7_write16(SharedMem[1], 2);
            _MMU_ARM7_write16(SharedMem[1] + 0x4, 0);
            
            WifiIPCReply(0xB, 0);
        }
        break;

        case 0xC: // connect to host
        return;

        case 0xE: // start local MP
            break;

        default:
            printf("WIFI HLE: unknown command %04X\n", cmd);
            break;
        }

        _MMU_ARM7_write32(SharedMem[1]+0x4, 0);
    }

    _MMU_ARM7_write16(addr, cmd|0x8000);
}

void wifi_scan_callback() {

    int numextra = 1;
    u16 extra[8+128];
    extra[0] = Channel;

    u16 status = _MMU_ARM7_read16(SharedMem[1]);
    if (status == 0x5) // host scan in progress
    {
        WifiIPCReply(0xA, 0, 1, extra);

        _MMU_ARM7_write32(SharedMem[1]+0x4, 0);
        _MMU_ARM7_write16(IPCCmdAddr, 0x800A);
    }
}