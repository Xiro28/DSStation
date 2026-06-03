
//LOGIC TAKEN FROM MELONDS : https://github.com/melonDS-emu/melonDS/

#include "MMU.h"
#include "FIFO.h"
#include "arm7_hle.h"
#include "NDSSystem.h"
#include "wifi_hle.h"

u16 IPCSync9, IPCSync7;
u16 IPCFIFOCnt9, IPCFIFOCnt7;

namespace Sound_Nitro{
    extern void OnIPCRequest(u32 data);
    extern void Reset();
    extern void Process(u32 param);
}

u32 SM_Command;
u32 SM_DataPos;
u32 SM_Buffer;

u16 PM_Data[16];

int TS_Status;
u16 TS_Data[16];
u16 TS_NumSamples;
u16 TS_SamplePos[4];

u16 FW_Data[16];

u16 Mic_Data[16];

int Sound_Engine;

void SendIPCSync(u8 val)
{
    IPCSync9 = (IPCSync9 & 0xFFF0) | (val & 0xF);

    printf("[HLE] SendIPCSync: val=%d IPCSync9=0x%04X IRQ_EN=%d\n",
        val, IPCSync9, (IPCSync9 >> 14) & 1);
if ((IPCSync9 & IPCSYNC_IRQ_SEND) && (IPCSync7 & IPCSYNC_IRQ_RECV)){
        printf("[HLE] Firing IRQ_BIT_IPCSYNC on ARM9\n");
        NDS_makeIrq(ARMCPU_ARM9, IRQ_BIT_IPCSYNC); // IRQ bit 16
    }
    
}

void SendIPCReply(u32 service, u32 data, u32 flag)
{
    u32 val = (service & 0x1F) | (data << 6) | ((flag & 0x1) << 5);

    if (ipc_fifo[ARMCPU_ARM7].size > 15 ){
        printf("[HLE] WARNING: IPCFIFO7 full, dropping reply svc=%d data=0x%08X flag=%d\n",
            service, data, flag);
        IPCFIFOCnt7 |= 0x4000;
        IPCFIFOCnt7 |= IPCFIFOCNT_SENDFULL;
        IPCFIFOCnt9 |= IPCFIFOCNT_RECVFULL;
        if (IPCFIFOCnt9 & IPCFIFOCNT_RECVIRQEN)
            NDS_makeIrq(ARM9, IRQ_BIT_IPCFIFO_RECVNONEMPTY);
        return;
    }else
    {
        IPC_FIFOsend(ARMCPU_ARM7, val);
    }
}

void HLE_Reset(){
    IPCSync9 = 0;
    IPCSync7 = 0;
    IPCFIFOCnt9 = IPCFIFOCNT_FIFOENABLE;  // 0x8000 - mimics NDS firmware init
    IPCFIFOCnt7 = IPCFIFOCNT_FIFOENABLE;  // 0x8000 - mimics NDS firmware init
    SM_Command = 0;
    SM_DataPos = 0;
    SM_Buffer = 0;

    Sound_Engine = -1;

    memset(PM_Data, 0, sizeof(PM_Data));

    memset(Mic_Data, 0, sizeof(Mic_Data));

    TS_Status = 0;
    memset(TS_Data, 0, sizeof(TS_Data));
    TS_NumSamples = 0;
    memset(TS_SamplePos, 0, sizeof(TS_SamplePos));

    memset(FW_Data, 0, sizeof(FW_Data));

    Sound_Nitro::Reset();
    WiFIReset();
}

uint8_t buffer[8192];

void OnIPCRequest_CartSave(u32 data)
{
    if (SM_DataPos == 0)
        SM_Command = data;

    //printf("OnIPCRequest_CartSave: %08X\n", SM_Command);

    switch (SM_Command)
    {
    case 0:
        if (SM_DataPos == 1)
        {
            SM_Buffer = data;
            SendIPCReply(0xB, 0x1, 1);
            SM_DataPos = 0;
            return;
        }
        break;

    case 2: // identify savemem
        if (MMU_new.backupDevice.info.mem_size == 0)
        {
            const u32 save_param = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x04);
            const u32 save_size_shift = (save_param >> 8) & 0xFF;
            MMU_new.backupDevice.info.mem_size = 1 << save_size_shift;
        }
        SendIPCReply(0xB, 0x1, 1);
        SM_DataPos = 0;
        return;

    case 6: // read
        {
            const u32 offset = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x0C);
            const u32 dst = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x10);
            const u32 len = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x14);

            u32 memlen = MMU_new.backupDevice.info.mem_size - 1;
            
            s32 remaining = len;
            u32 currOffset = offset;
            u32 currDst = dst;

            while (remaining > 0)
            {
                u32 toRead = (remaining > sizeof(buffer)) ? sizeof(buffer) : remaining;
                MMU_new.backupDevice.loadToBuffer(buffer, currOffset & memlen, toRead);

                for (u32 i = 0; i < toRead; i++)
                {
                    _MMU_write08<ARMCPU_ARM7>(currDst++, buffer[i]);
                }

                currOffset += toRead;
                remaining -= toRead;
            }


            SendIPCReply(0xB, 0x1, 1);
            
            SM_DataPos = 0;  
            return;
        }
        break;

    case 7:
    case 8: // write
        {
            const u32 src = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x0C);
            const u32 offset = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x10);
            const u32 len = _MMU_read32<ARMCPU_ARM7>(SM_Buffer+0x14);


            const u32 memlen = MMU_new.backupDevice.info.mem_size - 1;
            for (u32 i = 0; i < len; i++)
            {
                const char val = _MMU_read08<ARMCPU_ARM7>(src + i);
                MMU_new.backupDevice.writeByte((offset + i) & memlen, val);
            }

            _MMU_write16<ARMCPU_ARM7>(SM_Buffer + 0x02, 0);

            
            SendIPCReply(0xB, 0x1, 1);
            SM_DataPos = 0;
            return;
        }
        break;

    case 9: // verify
        {
            _MMU_write16<ARMCPU_ARM7>(SM_Buffer + 0x02, 0);
            SendIPCReply(0xB, 0x1, 1);
            SM_DataPos = 0;
            return;
        }
        break;

    default:
        printf("SAVEMEM: unknown cmd %08X\n", SM_Command);
        break;
    }

    SM_DataPos++;
}

void OnIPCRequest_Cart(u32 data)
{
    if ((data & 0x3F) == 1)
    {
        // TODO other shito?

        SendIPCReply(0xD, 0x1);
    }
    else
    {
        // do something else
    }
    /*if (data & 0x1)
    {
        // init

        SendIPCReply(0xD, 0x1);
    }*/
}

void Touchscreen_Sample()
{
    u32 ts = (((u32)_MMU_read16<ARMCPU_ARM7>(0x027FFFAA)) | ((u32)_MMU_read16<ARMCPU_ARM7>(0x027FFFAC) << 16));
    
    if (!nds.hw_status.Touching)
    {
        ts &= 0xFE000000;
        ts |= 0x06000000;
    }
    else
    {
        ts &= 0xF9000000;
        ts |= (nds.scr_touchX & 0xFFF);
        ts |= ((nds.scr_touchY & 0xFFF) << 12);
        ts |= 0x01000000;
    }

    _MMU_write16<ARMCPU_ARM7>(0x027FFFAA, ts & 0xFFFF);
    _MMU_write16<ARMCPU_ARM7>(0x027FFFAC, ts >> 16);
}

void OnIPCRequest_Touchscreen(u32 data)
{
    if (data & (1<<25))
    {
        memset(TS_Data, 0, sizeof(TS_Data));
    }

    TS_Data[(data >> 16) & 0xF] = data & 0xFFFF;

    if (!(data & (1<<24))) return;

    switch (TS_Data[0] >> 8)
    {
    case 0: // manual sampling
        {
            Touchscreen_Sample();
            SendIPCReply(0x6, 0x03008000);
        }
        break;

    case 1: // setup auto sampling
        {
            if (TS_Status != 0)
            {
                SendIPCReply(0x6, 0x03008103);
                break;
            }

            // samples per frame
            u8 num = TS_Data[0] & 0xFF;
            if (num == 0 || num > 4)
            {
                SendIPCReply(0x6, 0x03008102);
                break;
            }

            // offset in scanlines for first sample
            u16 offset = TS_Data[1];
            if (offset >= 263)
            {
                SendIPCReply(0x6, 0x03008102);
                break;
            }

            TS_Status = 1;

            TS_NumSamples = num;
            for (int i = 0; i < num; i++)
            {
                u32 ypos = (offset + ((i * 263) / num)) % 263;
                TS_SamplePos[i] = ypos;
            }

            TS_Status = 2;
            SendIPCReply(0x6, 0x03008100);
        }
        break;

    case 2: // stop autosampling
        {
            if (TS_Status != 2)
            {
                SendIPCReply(0x6, 0x03008203);
                break;
            }

            TS_Status = 3;

            // TODO CHECKME
            TS_NumSamples = 0;

            TS_Status = 0;
            SendIPCReply(0x6, 0x03008200);
        }
        break;

    case 3: // manual sampling but with condition (TODO)
        {
            Touchscreen_Sample();
            SendIPCReply(0x6, 0x03008300);
        }
        break;

    default:
        printf("unknown TS request %08X\n", data);
        break;
    }
}

void OnIPCRequest_Powerman(u32 data)
{
    extern void FASTCALL MMU_writeToSPIData(u16 val);

    if (data & (1<<25))
    {
        memset(PM_Data, 0, sizeof(PM_Data));
    }

    PM_Data[(data >> 16) & 0xF] = data & 0xFFFF;

    if (!(data & (1<<24))) return;

    u32 cmd = (PM_Data[0] >> 8) - 0x60;
    //printf("PM CMD %d %04X %04X\n", cmd, PM_Data[0], PM_Data[1]);
    switch (cmd)
    {
    case 1:
        MMU_writeToSPIData(PM_Data[0]); //?
        SendIPCReply(0x8, 0x03008000);
    break;
    case 3: // utility
        {
            switch (PM_Data[1] & 0xFF)
            {
            case 1: // power LED: steady
                MMU.powerMan_Reg[0] &= ~0x10;
                break;
            case 2: // power LED: fast blink
                MMU.powerMan_Reg[0] |= 0x30;
                break;
            case 3: // power LED: slow blink
                MMU.powerMan_Reg[0] &= ~0x20;
                MMU.powerMan_Reg[0] |= 0x10;
                break;
            case 4: // lower backlights on
                MMU.powerMan_Reg[0] |= 0x04;
                break;
            case 5: // lower backlights off
                MMU.powerMan_Reg[0] &= ~0x04;
                break;
            case 6: // upper backlights on
                MMU.powerMan_Reg[0] |= 0x08;
                break;
            case 7: // upper backlights off
                MMU.powerMan_Reg[0] &= ~0x08;
                break;
            case 8: // backlights on
                MMU.powerMan_Reg[0] |= 0x0C;
                break;
            case 9: // backlights off
                MMU.powerMan_Reg[0] &= ~0x0C;
                break;
            case 10: // sound amp on
                MMU.powerMan_Reg[0] |= 0x01;
                break;
            case 11: // sound amp off
                MMU.powerMan_Reg[0] &= ~0x01;
                break;
            case 12: // sound mute on
                MMU.powerMan_Reg[0] |= 0x02;
                break;
            case 13: // sound mute off
                MMU.powerMan_Reg[0] &= ~0x02;
                break;
            case 14: // shutdown
                MMU.powerMan_Reg[0] &= ~0x01;
                MMU.powerMan_Reg[0] |= 0x40;
                //NDS::Stop();
                break;
            case 15: // ????
                MMU.powerMan_Reg[0] &= ~0x40;
                break;
            }

            SendIPCReply(0x8, 0x0300E300);
        }
        break;

    case 4: // write register
        {
            u8 addr = PM_Data[0] & 0xFF;
            u8 val = PM_Data[1] & 0xFF;

            extern void MMU_writePowerMan(u8 val, bool hold);

            MMU_writePowerMan(addr & 0x7F, true);
            MMU_writePowerMan(val, false);

            SendIPCReply(0x8, 0x03008000 | (((PM_Data[1] + 0x70) & 0xFF) << 8));
        }
        break;

    case 5: // read register
        {
            u8 addr = PM_Data[0] & 0xFF;
            u8 reg = (addr & 0x7F) & 0x7;

            extern u32 MMU_readPowerMan();

            extern void MMU_writePowerMan(u8 val, bool hold);

            MMU_writePowerMan((addr & 0x7F) | 0x80, true);
            MMU_writePowerMan(0, false);

            u8 ret = MMU_readPowerMan();

            //printf("PM read reg=%02X val=%02X\n", addr & 0x7F, ret);

            SendIPCReply(0x8, 0x03008000 | (ret & 0xFF) | (((PM_Data[1] + 0x70) & 0xFF) << 8));
        }
        break;

    case 6:
        {
            // TODO

            SendIPCReply(0x8, 0x03008000 | (((PM_Data[1] + 0x70) & 0xFF) << 8));
        }
        break;

    default:
        printf("unknown PM request %08X, %08X, %08X\n", cmd, PM_Data[0], PM_Data[1]);
        break;
    }
}

void RTC_Read(u8 reg, u32 addr, u32 len)
{
    u8 old_cmd = rtc.cmd;

    rtc.cmd = reg;

    rtcRecv();

    static u8 prev_sec = 0xFF;
    u8 cur_sec = (len >= 7) ? rtc.data[6] : ((len == 3) ? rtc.data[2] : 0);
    if (cur_sec != prev_sec) {
        //printf("RTC read: sec=%02X (BCD)\n", cur_sec);
        prev_sec = cur_sec;
    }

    for (u32 i = 0; i < len; i++)
    {
        //printf("%d: %d\n", i, rtc.data[i]);
        _MMU_write08<ARMCPU_ARM7>(addr+i, rtc.data[i]);
    }
    //rtc.cmd = old_cmd;
}

void OnIPCRequest_RTC(u32 data)
{
    u32 cmd = (data >> 8) & 0x7F;

    if ((cmd >= 2 && cmd <= 15) ||
        (cmd >= 26 && cmd <= 34) ||
        (cmd >= 42))
    {
        SendIPCReply(0x5, 0x8001 | (cmd << 8));
        return;
    }

    switch (cmd)
    {
    case 0x10: // read date and time
        RTC_Read(0x4, 0x027FFDE8, 7);
        SendIPCReply(0x5, 0x9000);
        break;

    case 0x11: // read date
        RTC_Read(0x4, 0x027FFDE8, 4);
        SendIPCReply(0x5, 0x9100);
        break;

    case 0x12: // read time
        RTC_Read(0x6, 0x027FFDE8, 3);
        SendIPCReply(0x5, 0x9200);
        break;

    default:
        printf("HLE: unknown RTC command %02X (%08X)\n", cmd, data);
        break;
    }
}

void OnIPCRequest_Firmware(u32 data)
{
    if (data & (1<<25))
    {
        memset(FW_Data, 0, sizeof(FW_Data));
    }

    FW_Data[(data >> 16) & 0xF] = data & 0xFFFF;

    if (!(data & (1<<24))) return;

    u32 cmd = (FW_Data[0] >> 8) - 0x20;
    switch (cmd)
    {
    case 0: // write enable
        MMU.fw.write_enable = true;
        SendIPCReply(0x4, 0x0300A000);
        break;

    case 1: // write disable
        MMU.fw.write_enable = false;
        SendIPCReply(0x4, 0x0300A100);
        break;

    case 2: // read status register
        {
            u32 addr = ((FW_Data[0] & 0xFF) << 24) | (FW_Data[1] << 8) | ((FW_Data[2] >> 8) & 0xFF);
            if (addr < 0x02000000 || addr >= 0x02800000)
            {
                SendIPCReply(0x4, 0x0300A202);
                break;
            }

            _MMU_write08<ARMCPU_ARM7>(addr, MMU.fw.write_enable ? 0x02 : 0x00);

            SendIPCReply(0x4, 0x0300A200);
        }
        break;

    case 3: // firmware read
        {
            u32 addr = (FW_Data[4] << 16) | FW_Data[5];
            if (addr < 0x02000000 || addr >= 0x02800000)
            {
                SendIPCReply(0x4, 0x0300A302);
                break;
            }

            u32 src = ((FW_Data[0] & 0xFF) << 16) | FW_Data[1];
            u32 len = (FW_Data[2] << 16) | FW_Data[3];

            for (u32 i = 0; i < len; i++)
            {
                u8 val = MMU.fw.data[src & (0x20000 -1)];
                _MMU_write08<ARMCPU_ARM7>(addr, val);
                src++;
                addr++;
            }


            SendIPCReply(0x4, 0x0300A300);
        }
        break;

    case 5: // firmware write
        {
            u32 addr = (FW_Data[3] << 16) | FW_Data[4];
            if (addr < 0x02000000 || addr >= 0x02800000)
            {
                SendIPCReply(0x4, 0x0300A502);
                break;
            }

            u32 dst = ((FW_Data[0] & 0xFF) << 16) | FW_Data[1];
            u32 len = FW_Data[2];

            for (u32 i = 0; i < len; i++)
            {
                u8 val =_MMU_read08<ARMCPU_ARM7>(addr);
                MMU.fw.data[dst & (0x20000 -1)] = val;
                dst++;
                addr++;
            }


            SendIPCReply(0x4, 0x0300A500);
        }
        break;

    default:
        printf("unknown FW request %08X (%04X)\n", data, FW_Data[0]);
        break;
    }
}

void OnIPCRequest_Sound(u32 data)
{
    if (Sound_Engine == -1)
    {
        if (data >= 0x02000000)
        {
            Sound_Engine = 0;
            Sound_Nitro::Reset();
        }
        else
        {
            Sound_Engine = 1;
            printf("HLE: Peach Engine\n");
            //Sound_Peach::Reset();
        }
    }

    if (Sound_Engine == 0) return Sound_Nitro::OnIPCRequest(data);
   // if (Sound_Engine == 1) return Sound_Peach::OnIPCRequest(data);
}

void OnIPCRequest_Mic(u32 data)
{
    if (data & (1<<25))
    {
        memset(Mic_Data, 0, sizeof(Mic_Data));
    }

    Mic_Data[(data >> 16) & 0xF] = data & 0xFFFF;

    if ((data & (1<<24)) == 0) return;

    u32 cmd = (Mic_Data[0] >> 8) - 0x40;
    switch (cmd)
    {
    case 0: // sampling?
        {
            // TODO

            SendIPCReply(0x9, 0x0300C000);
        }
        break;

    default:
        //printf("unknown mic request %08X\n", data);
        SendIPCReply(0x9, 0x0300C000);
        break;
    }
}

void OnIPCRequest()
{
    u32 val = IPC_FIFOrecv(ARMCPU_ARM7);

    if (val == 0)
    {
        return;
    }

    
    //printf("%x %x\n", val, IPCFIFO7.Peek());

    u32 service = val & 0x1F;
    u32 data = val >> 6;
    bool flag = ((val >> 5) & 0x1) != 0;

    
    switch (service)
    {
    case 0x4: // firmware
        if (flag) break;
        OnIPCRequest_Firmware(data);
        break;

    case 0x5: // RTC
        if (flag) break;
        OnIPCRequest_RTC(data);
        break;

    case 0x6: // touchscreen
        if (flag) break;
        OnIPCRequest_Touchscreen(data);
        break;

    case 0x7: // sound
        OnIPCRequest_Sound(data);
        break;

    case 0x8: // powerman
        if (flag) break;
        OnIPCRequest_Powerman(data);
        break;

    case 0x9: // mic
        if (flag) break;
        OnIPCRequest_Mic(data);
        break;

    case 0xA: // wifi
        if (flag) break;
        printf("HLE: wifi request %08X\n", data);
        WifiOnIPCRequest(data);
        //Wifi::OnIPCRequest(data);
        break;

    case 0xB: // cart savemem
        if (!flag) break;
        OnIPCRequest_CartSave(data);
        break;

     case 0xC:
        if (data == 0x1000)
        {
            // TODO: stop/reset hardware

            SendIPCReply(0xC, 0x1000);
        }
        break;

    case 0xD: // cart
        OnIPCRequest_Cart(data);
        break;

    case 0xF:
        //if (data == 0x10000)
        {
            SendIPCReply(0xF, data);
        }
        break;

    default:
        printf("HLE: unknown IPC request %08X service=%02X data=%08X flag=%d\n", val, service, data, flag);
        break;
    }
}

void StartScanline(u16 line)
{
    for (int i = 0; i < TS_NumSamples; i++)
    {
        if (line == TS_SamplePos[i])
        {
            Touchscreen_Sample();
            SendIPCReply(0x6, 0x03009000 | i);
            break;
        }
    }
}

#define HW_WRAM_END                 0x03800000
#define HW_PRV_WRAM                 0x03800000
#define HW_PRV_WRAM_END             0x03810000

#define HW_PRV_WRAM_SIZE            (HW_PRV_WRAM_END-HW_PRV_WRAM)

#define HW_PRV_WRAM_SYSRV_SIZE      0x40

#define HW_PRV_WRAM_SYSRV           (HW_PRV_WRAM + HW_PRV_WRAM_SIZE - HW_PRV_WRAM_SYSRV_SIZE)

#define HW_INTR_CHECK_BUF           (HW_PRV_WRAM_SYSRV + 0x38)

void executeARM7Stuff(){
    extern u16 get_keypad();
	// 0x027FFFA8 holds ext key state: bits 10=X, 11=Y, 13=lid
	// get_keypad already returns regular keypad in bits 0-9 + X/Y in bits 10-11
	_MMU_write16<ARMCPU_ARM7>(0x027FFFA8, get_keypad() & 0x2C00);
   
   //u32 val = _MMU_ARM7_read32(HW_INTR_CHECK_BUF);

   //printf("ARM7: %08X\n", val);

   u32 fram_counter = _MMU_read32<ARMCPU_ARM7>(0x27FFC3C);
    _MMU_write32<ARM7>(0x27FFC3C, fram_counter+1);

    if (nds.is_twl_sdk()){
        bool sync = _MMU_read08<ARMCPU_ARM7>(0x2FFFFF0) & 0x1;
        _MMU_write08<ARM7>(0x2FFFFF1, !sync);
        _MMU_write08<ARM7>(0x2FFFFF2, 1);
        _MMU_write08<ARM7>(0x2FFFFF3, 1);
    }

   /* _MMU_write16<ARM7>(0x02FFFC20, 0);
    _MMU_write16<ARM7>(0x02FFFC22, 0);
    _MMU_write16<ARM7>(0x02FFFC24, 2);
    _MMU_write16<ARM7>(0x02FFFC26, 8);
    _MMU_write16<ARM7>(0x02FFFC28, 4);
    _MMU_write16<ARM7>(0x04000006, 0);*/

    //_MMU_write32<ARM7>(0x02067340, fram_counter+1);
    //_MMU_write32<ARM9>(0x02067340, fram_counter+1);

   //Sound_Nitro::Process(1);
}

void HLE_IPCSYNC(){
    u8 val = IPCSync7 & 0xF;

    printf("[HLE] HLE_IPCSYNC: IPCSync7=0x%04X IPCSync9=0x%04X val=%d\n",
        IPCSync7, IPCSync9, val);

    if (val < 5)
    {
        SendIPCSync(val+1);
    }
    else if (val == 5)
    {
        SendIPCSync(0);

        printf("[HLE] IPCSYNC handshake complete! Writing ARM7 ready flag\n");
        // presumably ARM7-side ready flags for each IPC service
        _MMU_write32<ARMCPU_ARM7>(0x027FFF8C, 0x3FFF0);
    }
    else
    {
        printf("[HLE] HLE_IPCSYNC: unexpected val=%d, ignoring\n", val);
    }
}