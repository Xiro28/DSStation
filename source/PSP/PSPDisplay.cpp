#include <pspkernel.h>
#include <pspdebug.h>
#include <pspdisplay.h>
#include <pspctrl.h>
#include <pspvfpu.h>
#include <stdio.h>
#include <pspgu.h>
#include <pspgum.h>
#include <psprtc.h>
#include <psppower.h>

#include <string.h>
#include <malloc.h>

#include "../common.h"
#include "../utils/decrypt/header.h"
#include "../ctrlssdl.h"
#include "vram.h"
#include "pspvfpu.h"
#include "PSPDisplay.h"
#include "pspDmac.h"
#include "../GPU.h"
#include "intraFont.h"
#include "pspdisplay.h"
#include "../rasterize.h"

#include <png.h>

#define SLICE_SIZE 16
#define MAX_COL 32
#define TOTAL_ICONS (MAX_COL * 2)
#define ICON_H 150
#define ICON_W 120
#define RGB(r, v, b) ((r) | ((v) << 8) | ((b) << 16) | (0xff << 24))

#define GU_VRAM_WIDTH 512
#define VRAM_START 0x4000000

// FIX: display list must be 64-byte aligned and sized correctly.
// A display list of 256KB is more than enough for any frame.
unsigned int __attribute__((aligned(64))) gulist[256 * 1024 / 4];

// VRAM layout (PSP VRAM = 2MB total):
// Each buffer: 512 * 272 * 2 bytes (GU_PSM_5551) = 0x44000 bytes
//   frameBuffer  @ 0x00000  (display buffer)
//   doubleBuffer @ 0x44000  (draw buffer)
//   depthBuffer  @ 0x88000  (depth buffer, same size)
// Total used: 0xCC000 = 835584 bytes < 2MB  ✓
//
// Vertex buffers must NOT be placed inside framebuffer/depth VRAM.
// FIX: use uncached system RAM for vertex data (memalign).
#define VRAM_BASE_UNCACHED  0x44000000u
#define VRAM_FB0_OFFSET     0x000000u   // frameBuffer
#define VRAM_FB1_OFFSET     0x044000u   // doubleBuffer
#define VRAM_DEPTH_OFFSET   0x088000u   // depthBuffer
#define VRAM_NDS2D_OFFSET   0x0CC000u   // NDS 2D framebuffer staging area

void* frameBuffer  = (void*)VRAM_FB0_OFFSET;
void* doubleBuffer = (void*)VRAM_FB1_OFFSET;
void* depthBuffer  = (void*)VRAM_DEPTH_OFFSET;


u8* DISP_POINTER = (u8*)(0x44000000u + 0x100000u); 

intraFont* Font;
intraFont* RomFont;

struct DispVertex {
    unsigned short u, v;
    signed short x, y, z;
};

struct DispVertexColored {
    unsigned short u, v;
    unsigned short color;
    signed short x, y, z;
};

struct DispVertexColoredNT {
    unsigned short color;
    signed short x, y, z;
};

#define TEXTURE_FLAGS          (GU_TEXTURE_16BIT | GU_VERTEX_16BIT | GU_TRANSFORM_2D)
#define TEXTURE_FLAGS_COLOR_NT (GU_COLOR_5551    | GU_VERTEX_16BIT | GU_TRANSFORM_2D)

// ─── vertex buffers in system RAM ────────────────────────────────────────────
#define MAX_SLICES 64   // ceil(512/SLICE_SIZE) = 32, ×2 for safety

static struct DispVertex          sprt_gpuvtx_buf[MAX_SLICES * 2] __attribute__((aligned(16)));
static struct DispVertexColoredNT bck_gpuvtx_buf[4]               __attribute__((aligned(16)));
static struct DispVertex          icons_gpuvtx_buf[2]              __attribute__((aligned(16)));
static struct DispVertex          mouse_vtx[2]                     __attribute__((aligned(16)));

struct DispVertex*           sprt_gpuvtx  = sprt_gpuvtx_buf;
struct DispVertexColoredNT*  bck_gpuvtx   = bck_gpuvtx_buf;
struct DispVertex*           icons_gpuvtx = icons_gpuvtx_buf;


// ─── Icon / menu ─────────────────────────────────────────────────────────────

class Icon {
public:
    u16*  GetIconData()  { return data; }
    char* GetIconName()  { return RomName; }
    char* GetDevName()   { return Developer; }
    char* GetFileName()  { return Filename; }

    void SetIconPixel(u8 X, u8 Y, u16 pixel) { data[X + Y * ICON_W] = pixel; }

    void SetIconName(const char* Name) {
        strncpy(RomName, (*Name == '.') ? "Homebrew" : Name, 11);
        RomName[11] = 0;
    }
    void SetDevName(const char* Name)  { strncpy(Developer, Name, 63); Developer[63] = 0; }
    void SetFileName(const char* Name) { strncpy(Filename,  Name, 127); Filename[127] = 0; }

    void ClearIcon(u16 color)   { memset(data, color, ICON_W * ICON_H * 2); }
    void MEMSetIcon(u16* buff)  { memcpy(data, buff, ICON_W * ICON_H * 2); }

private:
    char RomName[12];
    char Developer[64];
    char Filename[128];
    __attribute__((aligned(16))) u16 data[ICON_H * ICON_W];
};

#define ICON_SZ 32
Icon menu[TOTAL_ICONS];

void DrawIcon(u16 x, u16 y, u8 sprX, bool curON)
{
    sceGuColor(0xffffffff);

    struct DispVertex* vertices = (struct DispVertex*)sceGuGetMemory(2 * sizeof(struct DispVertex));

    sceGuTexMode(GU_PSM_5551, 0, 0, 0);
    sceGuTexImage(0, ICON_SZ, ICON_SZ, ICON_SZ, menu[sprX].GetIconData());
    sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGB);
    sceGuTexFilter(GU_LINEAR, GU_LINEAR);
    sceGuTexWrap(GU_CLAMP, GU_CLAMP);

    vertices[0].u = 0;      vertices[0].v = 0;
    vertices[0].x = x;      vertices[0].y = y - 5 * (1 + curON);  vertices[0].z = 0;

    vertices[1].u = ICON_SZ; vertices[1].v = ICON_SZ;
    vertices[1].x = x + 23;  vertices[1].y = y + 23 - 5 * (1 + curON);  vertices[1].z = 0;

    sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, vertices);
}

int curr_posX = -1;
int curr_page = 0;
int old_page  = -1;
int N_Roms    = 0;

void Set_POSX(int pos) { curr_posX = pos; }
void Set_PAGE(int pos) { curr_page = pos; }

void drawmenu()
{
    sceGuSync(0, 0);
    sceGuStart(GU_DIRECT, gulist);

    sceGuDisable(GU_DEPTH_TEST);
    sceGuDepthMask(GU_TRUE);
    sceGuDisable(GU_STENCIL_TEST);
    sceGuDisable(GU_CULL_FACE);
    sceGuDisable(GU_SCISSOR_TEST);
    sceGuDisable(GU_ALPHA_TEST);
    sceGuEnable(GU_BLEND);
    sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);
    sceGuEnable(GU_TEXTURE_2D);

    sceGuClearColor(0x10404047);
    sceGuClear(GU_COLOR_BUFFER_BIT);

    for (int y = 50, romX = 0; y <= 220; y += 32)
        for (int x = 30; x < 410; x += 32, romX++) {
            if (N_Roms <= romX) goto done;
            DrawIcon(x, y, romX, (curr_posX == romX));
            if (curr_posX == romX)
                intraFontPrintf(Font, 20, 240, "ROM: %s::%s",
                    menu[romX].GetIconName(), menu[romX].GetFileName());
        }
done:
    intraFontPrint(Font, 210, 15, "Release V3.1");
    intraFontPrintf(Font, 390, 15, "Battery:%d%%", scePowerGetBatteryLifePercent());

    sceGuFinish();
    sceGuSync(GU_SYNC_FINISH, GU_SYNC_WHAT_DONE);
    sceGuSwapBuffers();
}

// ─── Screen vertex buffers ────────────────────────────────────────────────────

static const float sw    = 511.0f;
static const int   scale = (int)(sw * (float)SLICE_SIZE) / (int)512;

// FIX: allocate from system RAM, not VRAM. Sized for the maximum slice count.
// Maximum slices = ceil(512 / SLICE_SIZE) = 32, each needs 2 vertices.
#define MAX_SLICES 32
int n_slices = 0;

// PSPDisplay.cpp — SetupDisplay: build separate slice arrays per screen half

#define MAX_SLICES_HALF 32

// Separate slice arrays: left half and right half of PSP screen
static struct DispVertex slices_left[MAX_SLICES_HALF  * 2] __attribute__((aligned(16)));
static struct DispVertex slices_right[MAX_SLICES_HALF * 2] __attribute__((aligned(16)));
int n_slices_left  = 0;
int n_slices_right = 0;

void SetupDisplay()
{
    n_slices_left  = 0;
    n_slices_right = 0;

    // NDS framebuffer: 512 wide, left 256px = left NDS screen, right 256px = right NDS screen
    // PSP display: left 240px = left half, right 240px = right half
    // Scale: 256 texels → 240 pixels

    const int texHalfW = 256;   // each NDS screen is 256px wide in texture
    const int dispHalfW = 240;  // each screen occupies 240 PSP pixels
    const int texH  = 192;
    const int startY = 40;
    const int endY   = 232;

    // Left half: texture U=[0,256], screen X=[0,240]
    for (int start = 0, idx = 0; start < texHalfW; start += SLICE_SIZE, idx += 2) {
        int width = std::min(SLICE_SIZE, texHalfW - start);
        int sx0 = (start         * dispHalfW) / texHalfW;
        int sx1 = ((start+width) * dispHalfW) / texHalfW;

        slices_left[idx  ].u = start;         slices_left[idx  ].v = 0;
        slices_left[idx  ].x = sx0;           slices_left[idx  ].y = startY; slices_left[idx  ].z = 0;
        slices_left[idx+1].u = start + width; slices_left[idx+1].v = texH;
        slices_left[idx+1].x = sx1;           slices_left[idx+1].y = endY;   slices_left[idx+1].z = 0;
        n_slices_left++;
    }

    // Right half: texture U=[256,512], screen X=[240,480]
    for (int start = 0, idx = 0; start < texHalfW; start += SLICE_SIZE, idx += 2) {
        int width = std::min(SLICE_SIZE, texHalfW - start);
        int sx0 = 240 + (start         * dispHalfW) / texHalfW;
        int sx1 = 240 + ((start+width) * dispHalfW) / texHalfW;

        slices_right[idx  ].u = 256 + start;         slices_right[idx  ].v = 0;
        slices_right[idx  ].x = sx0;                 slices_right[idx  ].y = startY; slices_right[idx  ].z = 0;
        slices_right[idx+1].u = 256 + start + width; slices_right[idx+1].v = texH;
        slices_right[idx+1].x = sx1;                 slices_right[idx+1].y = endY;   slices_right[idx+1].z = 0;
        n_slices_right++;
    }

    sceKernelDcacheWritebackRange(slices_left,  n_slices_left  * 2 * sizeof(DispVertex));
    sceKernelDcacheWritebackRange(slices_right, n_slices_right * 2 * sizeof(DispVertex));

    // Background quads unchanged
    bck_gpuvtx[0].x = 0;   bck_gpuvtx[0].y = startY; bck_gpuvtx[0].z = 0;
    bck_gpuvtx[1].x = 240; bck_gpuvtx[1].y = endY;   bck_gpuvtx[1].z = 0;
    bck_gpuvtx[2].x = 240; bck_gpuvtx[2].y = startY; bck_gpuvtx[2].z = 0;
    bck_gpuvtx[3].x = 480; bck_gpuvtx[3].y = endY;   bck_gpuvtx[3].z = 0;
    bck_gpuvtx[0].color = bck_gpuvtx[1].color = 0xFFFF;
    bck_gpuvtx[2].color = bck_gpuvtx[3].color = 0xFFFF;
    sceKernelDcacheWritebackRange(bck_gpuvtx, 4 * sizeof(DispVertexColoredNT));
}

void draw_mouse(int x, int y)
{
    mouse_vtx[0].u = 0; mouse_vtx[0].v = 0;
    mouse_vtx[0].x = 240 + x; mouse_vtx[0].y = 40 + y; mouse_vtx[0].z = 0;

    mouse_vtx[1].u = 8; mouse_vtx[1].v = 8;
    mouse_vtx[1].x = 240 + x + 8; mouse_vtx[1].y = 40 + y + 8; mouse_vtx[1].z = 0;
}

void DrawSprite()
{
    icons_gpuvtx[0].u = 0;   icons_gpuvtx[0].v = 0;
    icons_gpuvtx[0].x = 0;   icons_gpuvtx[0].y = 45;        icons_gpuvtx[0].z = 0;
    icons_gpuvtx[1].u = 512; icons_gpuvtx[1].v = 192;
    icons_gpuvtx[1].x = 470; icons_gpuvtx[1].y = 192 + 45;  icons_gpuvtx[1].z = 0;

    sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, icons_gpuvtx);
}

// ─── EMU_SCREEN ───────────────────────────────────────────────────────────────

u32 old_color_main = 0;
u32 old_color_sub  = 0;


static inline u16 getNDSBackdropColor(int core)
{
    // BG palette RAM layout in ARM9_VMEM (0x05000000):
    //   Main engine BG palette: offset 0x000 (512 bytes)
    //   Sub  engine BG palette: offset 0x200 (512 bytes)  ← FIX: was 0x400
    // Color index 0 = backdrop color.
    u32 offset = (core == 0) ? 0x000 : 0x200;
    u16 ndsColor = T1ReadWord(MMU.ARM9_VMEM, offset) & 0x7FFF;
    // Force alpha=1 (opaque) in GU_PSM_5551
    return ndsColor | 0x8000;
}


static bool emuFrameStarted = false;

void EMU_SCREEN(bool skip2d, bool skip3d)
{
    const bool do_3d = (((REG_DISPx*)&MMU.ARM9_REG[0])->dispx_DISPCNT.bits.BG0_3D)
                       && !skip3d;
    if (skip2d && !do_3d) return;

    const u16 _color_main = getNDSBackdropColor(MainScreen.gpu->core);
    const u16 _color_sub  = getNDSBackdropColor(SubScreen.gpu->core);
    const bool _3dOnLeft  = (MainScreen.offset == 0);

    struct DispVertex* slices_3d = _3dOnLeft ? slices_left  : slices_right;
    struct DispVertex* slices_2d = _3dOnLeft ? slices_right : slices_left;
    int n_3d = _3dOnLeft ? n_slices_left  : n_slices_right;
    int n_2d = _3dOnLeft ? n_slices_right : n_slices_left;

    sceGuSync(0, 0);
    sceGuStart(GU_DIRECT, gulist);

    // FIX problema 2: pulisci l'intero framebuffer a nero prima di ogni frame.
    // Questo elimina il grigio del menu che persiste fuori dall'area NDS (y<40, y>232).
    sceGuDisable(GU_SCISSOR_TEST);
    sceGuDisable(GU_DEPTH_TEST);
    sceGuDepthMask(GU_TRUE);
    sceGuClearColor(0xFF000000);
    sceGuClearDepth(0);
    sceGuClear(GU_COLOR_BUFFER_BIT | GU_DEPTH_BUFFER_BIT);

    sceGuDisable(GU_ALPHA_TEST);
    sceGuDisable(GU_STENCIL_TEST);
    sceGuDisable(GU_CULL_FACE);
    sceGuEnable(GU_BLEND);
    sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);

    if (do_3d)
    {
        if (old_color_main != _color_main || old_color_sub != _color_sub) {
            if (_3dOnLeft) {
                bck_gpuvtx[0].color = bck_gpuvtx[1].color = _color_main;
                bck_gpuvtx[2].color = bck_gpuvtx[3].color = _color_sub;
            } else {
                bck_gpuvtx[0].color = bck_gpuvtx[1].color = _color_sub;
                bck_gpuvtx[2].color = bck_gpuvtx[3].color = _color_main;
            }
            old_color_main = _color_main;
            old_color_sub  = _color_sub;
            sceKernelDcacheWritebackRange(bck_gpuvtx, 4 * sizeof(DispVertexColoredNT));
        }

        sceGuDisable(GU_TEXTURE_2D);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS_COLOR_NT, 4, NULL, bck_gpuvtx);

        if (!my_config._3d_always_on_top) {
            sceGuEnable(GU_DEPTH_TEST);
            sceGuDepthMask(GU_FALSE);
            gpu3D->NDS_3D_Render();
            sceGuDisable(GU_DEPTH_TEST);
            sceGuDepthMask(GU_TRUE);
        }

        // Sub screen: opaque blit
        sceGuEnable(GU_TEXTURE_2D);
        sceGuTexMode(GU_PSM_5551, 0, 0, 0);
        sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGB);
        sceGuTexImage(0, 512, 256, 512, DISP_POINTER);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, n_2d * 2, NULL, slices_2d);

        // 3D screen: alpha-tested overlay
        sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGBA);
        sceGuEnable(GU_ALPHA_TEST);
        sceGuAlphaFunc(GU_GREATER, 0, 0xFF);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, n_3d * 2, NULL, slices_3d);
        sceGuDisable(GU_ALPHA_TEST);

        if (my_config._3d_always_on_top) {
            sceGuEnable(GU_DEPTH_TEST);
            sceGuDepthMask(GU_FALSE);
            gpu3D->NDS_3D_Render();
            sceGuDisable(GU_DEPTH_TEST);
            sceGuDepthMask(GU_TRUE);
        }
    }
    else
    {
        sceGuDisable(GU_DEPTH_TEST);
        sceGuDepthMask(GU_TRUE);
        sceGuEnable(GU_TEXTURE_2D);
        sceGuTexMode(GU_PSM_5551, 0, 0, 0);
        sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGB);
        sceGuTexImage(0, 512, 256, 512, DISP_POINTER);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, n_slices_left  * 2, NULL, slices_left);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, n_slices_right * 2, NULL, slices_right);
    }

    if (my_config.cur) {
        static const u16 mouseCursor[64] = {
            0x0000,0x7FFF,0xFFFF,0xFFFF,0xFFFF,0xFFFF,0x7FFF,0x0000,
            0x7FFF,0xFFFF,0x8001,0x0000,0x0000,0x8001,0xFFFF,0x7FFF,
            0xFFFF,0x8001,0xF055,0xF055,0xF055,0xF055,0x8001,0xFFFF,
            0xFFFF,0x0000,0xF055,0xF000,0xF000,0xF055,0x0000,0xFFFF,
            0xFFFF,0x0000,0xF055,0xF000,0xF000,0xF055,0x0000,0xFFFF,
            0xFFFF,0x8001,0xF055,0xF055,0xF055,0xF055,0x8001,0xFFFF,
            0x7FFF,0xFFFF,0x8001,0x0000,0x0000,0x8001,0xFFFF,0x7FFF,
            0x0000,0x7FFF,0xFFFF,0xFFFF,0xFFFF,0xFFFF,0x7FFF,0x0000
        };
        sceGuEnable(GU_TEXTURE_2D);
        sceGuTexMode(GU_PSM_5551, 0, 0, 0);
        sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGBA);
        sceGuTexImage(0, 8, 8, 8, mouseCursor);
        draw_mouse(mouse.x % 256, mouse.y % 192);
        sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, mouse_vtx);
    }

    // FIX problema 3: NON fare sceGuSwapBuffers() qui.
    // Il menu HUD (configurazione) viene disegnato DOPO EMU_SCREEN
    // nella stessa chiamata sceGuStart/Finish, quindi deve restare
    // sullo stesso buffer. Lo swap avviene solo alla fine del frame completo.
    sceGuFinish();
    // NO sceGuSwapBuffers() qui
    emuFrameStarted = true;
}

void EMU_SCREEN_Finish()
{
    if (!emuFrameStarted) return;
    sceGuSync(0, 0);
    sceGuSwapBuffers();
    emuFrameStarted = false;
}

// ─── Init ─────────────────────────────────────────────────────────────────────

void Init_PSP_DISPLAY_FRAMEBUFF()
{
    static bool inited = false;

    sceGuInit();
    sceGuStart(GU_DIRECT, gulist);

    sceGuDrawBuffer(GU_PSM_5551, doubleBuffer, GU_VRAM_WIDTH);
    sceGuDispBuffer(SCR_WIDTH, SCR_HEIGHT, frameBuffer, GU_VRAM_WIDTH);
    sceGuDepthBuffer(depthBuffer, GU_VRAM_WIDTH);

    sceGuDepthRange(65535, 0);
    sceGuDisable(GU_DEPTH_TEST);
    sceGuDepthMask(GU_TRUE);
    sceGuDisable(GU_SCISSOR_TEST);
    sceGuDisable(GU_STENCIL_TEST);
    sceGuDisable(GU_CULL_FACE);
    sceGuDisable(GU_ALPHA_TEST);

    sceGuTexWrap(GU_CLAMP, GU_CLAMP);
    sceGuTexMode(GU_PSM_5551, 0, 0, 0);
    sceGuEnable(GU_TEXTURE_2D);
    sceGuEnable(GU_BLEND);
    sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);
    sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGBA);

    ScePspFMatrix4 identity = {
        {1.f,0,0,0},{0,1.f,0,0},{0,0,1.f,0},{0,0,0,1.f}
    };
    sceGuSetMatrix(GU_PROJECTION, &identity);
    sceGuSetMatrix(GU_TEXTURE,    &identity);
    sceGuSetMatrix(GU_MODEL,      &identity);
    sceGuSetMatrix(GU_VIEW,       &identity);

    sceGuViewport(0, 0, 480, 272);

    // Clear both buffers
    sceGuClearColor(0xFF000000);
    sceGuClearDepth(0);
    sceGuClear(GU_COLOR_BUFFER_BIT | GU_DEPTH_BUFFER_BIT);
    sceGuFinish();
    sceGuSync(GU_SYNC_FINISH, GU_SYNC_WHAT_DONE);

    sceGuSwapBuffers();
    sceGuStart(GU_DIRECT, gulist);
    sceGuClearColor(0xFF000000);
    sceGuClear(GU_COLOR_BUFFER_BIT | GU_DEPTH_BUFFER_BIT);
    sceGuFinish();
    sceGuSync(GU_SYNC_FINISH, GU_SYNC_WHAT_DONE);
    sceGuSwapBuffers();

    sceGuDisplay(GU_TRUE);

    if (inited) return;
    inited = true;

    intraFontInit();
    Font = intraFontLoad("flash0:/font/ltn1.pgf", INTRAFONT_CACHE_ASCII);
    intraFontActivate(Font);
    intraFontSetStyle(Font, 0.6f, 0xFFFFFFFF, 0, 0, 0);

    SetupDisplay();
}


// ─── ROM icon loading ─────────────────────────────────────────────────────────

Header header;

int readBanner(char* filename, tNDSBanner* banner)
{
    FILE* romF = fopen(filename, "rb");
    if (!romF) return 1;
    fread(&header, sizeof(header), 1, romF);
    fseek(romF, header.banner_offset, SEEK_SET);
    fread(banner, sizeof(*banner), 1, romF);
    fclose(romF);
    return 0;
}

void loadImage(unsigned short* image, unsigned short* palette, unsigned char* tileData)
{
    for (int tile = 0; tile < 16; tile++) {
        for (int pixel = 0; pixel < 32; pixel++) {
            unsigned char a = tileData[(tile << 5) + pixel];
            int px = ((tile & 3) << 3) + ((pixel << 1) & 7);
            int py = ((tile >> 2) << 3) + (pixel >> 2);

            unsigned short upper = (a & 0xF0) >> 4;
            unsigned short lower = (a & 0x0F);

            image[(px+1) + py * 32] = upper ? palette[upper] : 0;
            image[ px    + py * 32] = lower ? palette[lower] : 0;
        }
    }
}

bool CreateRomIcon(char* file, f_list* list)
{
    N_Roms = 0;
    tNDSBanner banner;

    for (int c = 0; c < TOTAL_ICONS; c++) {
        if (list->cnt <= c) break;

        int index = c + (curr_page * TOTAL_ICONS);
        if (list->cnt <= index) break;

        char rompath[256];
        strncpy(rompath, file, sizeof(rompath) - 1);
        rompath[sizeof(rompath)-1] = 0;
        strncat(rompath, list->fname[index].name, sizeof(rompath) - strlen(rompath) - 1);

        if (readBanner(rompath, &banner))
            return false;

        loadImage(menu[c].GetIconData(), banner.palette, banner.icon);
        menu[c].SetIconName(header.title);
        menu[c].SetFileName(list->fname[index].name);
        N_Roms++;
    }
    return true;
}

void DrawRom(char* file, f_list* list, int pos, bool reload)
{
    char rompath[256];
    strncpy(rompath, file, sizeof(rompath) - 1);
    rompath[sizeof(rompath)-1] = 0;

    curr_page = pos / TOTAL_ICONS;
    curr_posX = pos % TOTAL_ICONS;

    if (old_page != curr_page) {
        CreateRomIcon(rompath, list);
        old_page = curr_page;
    }
    drawmenu();
}