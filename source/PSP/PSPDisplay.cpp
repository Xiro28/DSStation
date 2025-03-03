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

unsigned int __attribute__((aligned(16))) gulist[256 * 192 * 4];

void *frameBuffer = (void *)0;
void *doubleBuffer = (void *)0x44000;
const void *depthBuffer = (void *)0x88000;

const int padding_top = (1024*1024*1024);
u8 *DISP_POINTER = (u8 *)(0x44100000);

intraFont *Font, *RomFont;

struct DispVertex
{
	unsigned short u, v;
	signed short x, y, z;
};

struct DispVertexColored
{
	unsigned short u, v;
	unsigned short color;
	signed short x, y, z; 
};

class Icon
{

public:
	u16 *GetIconData()
	{
		return data;
	}

	char *GetIconName()
	{
		return RomName;
	}

	char *GetDevName()
	{
		return Developer;
	}

	char *GetFileName()
	{
		return Filename;
	}

	void SetIconPixel(u8 X, u8 Y, u16 pixel)
	{
		data[X + (Y * ICON_W)] = pixel;
	}

	void SetIconName(const char *Name)
	{

		if (*Name == '.')
			strcpy(RomName, "Homebrew");
		else
			strcpy(RomName, Name);

		RomName[11] = 0;
	}
	void SetDevName(const char *Name)
	{
		strcpy(Developer, Name);
		Developer[63] = 0;
	}
	void SetFileName(const char *Name)
	{
		strcpy(Filename, Name);
		Filename[127] = 0;
	}

	void ClearIcon(u16 color)
	{
		memset(data, color, ICON_W * ICON_H);
	}

	void MEMSetIcon(u16 *buff)
	{
		memcpy(data, buff, ICON_W * ICON_H * 2);
	}

private:
	char RomName[12];
	char Developer[64];
	char Filename[128];
	__attribute__((aligned(16))) u16 data[ICON_H * ICON_W * 3];
};

#define ICON_SZ 32
Icon menu[TOTAL_ICONS];

void DrawIcon(u16 x, u16 y, u8 sprX, bool curON)
{

	sceGuColor(0xffffffff);

	struct DispVertex *vertices = (struct DispVertex *)sceGuGetMemory(2 * sizeof(struct DispVertex));

	sceGuTexMode(GU_PSM_5551, 0, 0, 0);
	sceGuTexImage(0, ICON_SZ, ICON_SZ, ICON_SZ, menu[sprX].GetIconData());
	sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGB);
	sceGuTexFilter(GU_LINEAR, GU_LINEAR);
	sceGuTexWrap(GU_CLAMP, GU_CLAMP);

	vertices[0].u = 0;
	vertices[0].v = 0;
	vertices[0].x = x;
	vertices[0].y = y - 5 * (1 + curON);
	vertices[0].z = 0;

	vertices[1].u = ICON_SZ;
	vertices[1].v = ICON_SZ;
	vertices[1].x = x + 8 + 15;
	vertices[1].y = y + 8 + 15 - 5 * (1 + curON);
	vertices[1].z = 0;

	sceKernelDcacheWritebackInvalidateAll();
	sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, vertices);
}

int curr_posX = -1;
int curr_page = 0;
int old_page = -1;
int N_Roms = 0;

void Set_POSX(int pos)
{
	curr_posX = pos;
}

void Set_PAGE(int pos)
{
	curr_page = pos;
}

void drawmenu()
{

	static u8 last_Xpos = 0;

	sceGuStart(GU_DIRECT, gulist);

	sceGuClearColor(0x10404047);
	sceGuClear(GU_COLOR_BUFFER_BIT);

	for (int y = 50, romX = 0; y <= 220; y += 32)
		for (int x = 30; x < 410; x += 32, romX++)
		{
			if (N_Roms <= romX)
				break;

			DrawIcon(x, y, romX, (curr_posX == romX));

			if (curr_posX == romX)
				intraFontPrintf(Font, 20, 240, "ROM: %s::%s", menu[romX].GetIconName(), menu[romX].GetFileName());
		}

	intraFontPrint(Font, 210, 15, "Release V3.1");
	intraFontPrintf(Font, 390, 15, "Battery:%d%%", scePowerGetBatteryLifePercent());

	sceGuFinish();
	sceGuSync(GU_SYNC_FINISH, GU_SYNC_WHAT_DONE);
}

const float sw = 511;
static const int scale = (int)(sw * (float)SLICE_SIZE) / (float)512;
struct DispVertexColored *screen_gpuvtx;
struct DispVertex *icons_gpuvtx;
struct DispVertex mouse_vtx[2];
int n_slices = 0;

void SetupDisplay(int dx)
{
	for (int start = 0, end = sw, idx = 0; start < end; start += SLICE_SIZE, dx += scale)
	{
		int width = (start + SLICE_SIZE) < end ? SLICE_SIZE : end - start;

		screen_gpuvtx[idx].u = start;
		screen_gpuvtx[idx].v = 0;
		screen_gpuvtx[idx].x = dx;
		screen_gpuvtx[idx].y = 40;
		screen_gpuvtx[idx].z = 0;

		screen_gpuvtx[idx + 1].u = start + width;
		screen_gpuvtx[idx + 1].v = 192;
		screen_gpuvtx[idx + 1].x = dx + scale;
		screen_gpuvtx[idx + 1].y = 192 + 40;
		screen_gpuvtx[idx + 1].z = 0;

		screen_gpuvtx[idx].color = 0x8000;
		screen_gpuvtx[idx + 1].color = 0x8000;

		icons_gpuvtx[idx].u = start;
		icons_gpuvtx[idx].v = 0;
		icons_gpuvtx[idx].x = dx;
		icons_gpuvtx[idx].y = 40;
		icons_gpuvtx[idx].z = 0;

		icons_gpuvtx[idx + 1].u = start + width;
		icons_gpuvtx[idx + 1].v = 192;
		icons_gpuvtx[idx + 1].x = dx + scale;
		icons_gpuvtx[idx + 1].y = 192 + 40;
		icons_gpuvtx[idx + 1].z = 0;

		idx += 2;

		n_slices++;
	}
}

void draw_mouse(int x, int y)
{
	mouse_vtx[0].u = 0;
	mouse_vtx[0].v = 0;
	mouse_vtx[0].x = 240 + x;
	mouse_vtx[0].y = 40 + y;
	mouse_vtx[0].z = 0;

	mouse_vtx[1].u = 8;
	mouse_vtx[1].v = 8;
	mouse_vtx[1].x = x + 8 + 240;
	mouse_vtx[1].y = y + 8 + 40;
	mouse_vtx[1].z = 0;
}

void DrawSprite()
{

	icons_gpuvtx[0].u = 0;
	icons_gpuvtx[0].v = 0;
	icons_gpuvtx[0].x = 0;
	icons_gpuvtx[0].y = 45;
	icons_gpuvtx[0].z = 0;

	icons_gpuvtx[1].u = 512;
	icons_gpuvtx[1].v = 192;
	icons_gpuvtx[1].x = 470;
	icons_gpuvtx[1].y = 192 + 45;
	icons_gpuvtx[1].z = 0;

	sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, &icons_gpuvtx[0]);
}

static inline uint32_t computePolyListSignature(const POLYLIST *polylist) {
    return (reinterpret_cast<uintptr_t>(polylist->list) & 0xFFFF) ^ polylist->count;
}

u32 old_color_main = 0;
u32 old_color_sub = 0;
u32 hash = 0;

#include <cstdint>
#include <cstddef>

uint32_t simpleHash(const uint8_t* data, size_t size) {
	uint32_t hash = 2166136261u;      // FNV-1a 32-bit offset basis
    const uint32_t prime = 16777619u;  // FNV-1a prime

    // Process as many 32-bit chunks as possible.
    size_t num32 = size / 4;
    const uint32_t* data32 = reinterpret_cast<const uint32_t*>(data);
    for (size_t i = 0; i < num32; ++i) {
        hash ^= data32[i];
        hash *= prime;
    }

    // Process any remaining bytes.
    size_t rem = size % 4;
    const uint8_t* data8 = data + (num32 * 4);
    for (size_t i = 0; i < rem; ++i) {
        hash ^= data8[i];
        hash *= prime;
    }
    return hash;
}


void EMU_SCREEN(bool skip2d, bool skip3d)
{
	static bool inited = false;
	if (skip2d && skip3d)
		return;

	const bool do_3d = ((((REG_DISPx*)&MMU.ARM9_REG[0])->dispx_DISPCNT.bits.BG0_3D)) && !skip3d;
	
	sceGuSync(0, 0);

	const u16 _color_main = (T1ReadWord(MMU.ARM9_VMEM, MainScreen.gpu->core * 0x400) & 0x7FFF) | 0x8000;
	const u16 _color_sub  = (T1ReadWord(MMU.ARM9_VMEM, SubScreen.gpu->core * 0x400) & 0x7FFF) | 0x8000;


	//if (old_color_main != _color_main || old_color_sub != _color_sub || do_3d || simpleHash((const uint8_t*)DISP_POINTER, 192 * 256 * 4) != hash)
	{

		//hash = simpleHash((const uint8_t*)DISP_POINTER, 192 * 256 * 4);
		sceGuStart(GU_DIRECT, gulist);

		if (!skip2d)
		{

			//
			
			//printf("Num slices: %d\n", n_slices);
			if (old_color_main != _color_main || old_color_sub != _color_sub){
				for (int i = 0; i < n_slices; i++)
				{
					screen_gpuvtx[i].color = _color_main;
					screen_gpuvtx[i + n_slices].color = _color_sub;
				}
			}

			old_color_main = _color_main;
			old_color_sub = _color_sub;

			if (do_3d || !inited){
				sceGuDrawBuffer(GU_PSM_5551, 0, GU_VRAM_WIDTH);
				if (!my_config.cur) sceGuEnable(GU_TEXTURE_2D);
				sceGuTexMode(GU_PSM_5551, 0, 0, 0);
				sceGuTexFunc(GU_TFX_DECAL , GU_TCC_RGBA);
				inited = true;
			}

			sceGuTexImage(0, 512, 256, 512, (const u32 *)&DISP_POINTER[0]);
			sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS_COLOR, n_slices * 2, NULL, &screen_gpuvtx[0]);
		}

		gpu3D->NDS_3D_Render();

		// render mouse
		if (my_config.cur)
		{
			int mouseX = mouse.x % 256; // Adjust to match rendering scale
			int mouseY = mouse.y % 192;
			static const u16 mouseCursor[8 * 8] = {
				0x0000, 0x7FFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0x7FFF, 0x0000,
				0x7FFF, 0xFFFF, 0x8001, 0x0000, 0x0000, 0x8001, 0xFFFF, 0x7FFF,
				0xFFFF, 0x8001, 0xF055, 0xF055, 0xF055, 0xF055, 0x8001, 0xFFFF,
				0xFFFF, 0x0000, 0xF055, 0xF000, 0xF000, 0xF055, 0x0000, 0xFFFF,
				0xFFFF, 0x0000, 0xF055, 0xF000, 0xF000, 0xF055, 0x0000, 0xFFFF,
				0xFFFF, 0x8001, 0xF055, 0xF055, 0xF055, 0xF055, 0x8001, 0xFFFF,
				0x7FFF, 0xFFFF, 0x8001, 0x0000, 0x0000, 0x8001, 0xFFFF, 0x7FFF,
				0x0000, 0x7FFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0x7FFF, 0x0000};

			if (do_3d){
				sceGuEnable(GU_TEXTURE_2D);
				sceGuTexMode(GU_PSM_5551, 0, 0, 0);
			}
			sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGBA);
			sceGuTexImage(0, 8, 8, 8, (const void *)&mouseCursor[0]);
			draw_mouse(mouseX, mouseY);
			sceGuDrawArray(GU_SPRITES, TEXTURE_FLAGS, 2, NULL, &mouse_vtx[0]);
		}

		sceGuFinish();
	}
}

void Init_PSP_DISPLAY_FRAMEBUFF()
{
	static bool inited = false;

	sceGuInit();

	sceGuStart(GU_DIRECT, gulist);

	ScePspFMatrix4 _default = {
		{0.998f, 0, 0, 0},
		{0, 0.998f, 0, 0},
		{0, 0, 1.f, 0},
		{0.001f, 0.001f, 0, 1.f}};

	// Init draw an disp buffers from the base of the vram

	// Reset 3D buffer
	// sceGuDrawBuffer(GU_PSM_5551, (void*)doubleBuffer, GU_VRAM_WIDTH);

	sceGuDrawBuffer(GU_PSM_5551, doubleBuffer, GU_VRAM_WIDTH);
	sceGuDispBuffer(SCR_WIDTH, SCR_HEIGHT, (void *)doubleBuffer, GU_VRAM_WIDTH);
	sceGuDepthBuffer((void *)depthBuffer, GU_VRAM_WIDTH);

	// sceGuDrawBufferList(GU_PSM_5551, (void*)depthBuffer, 512);

	sceGuDepthRange(65535, 0);

	sceGuDisable(GU_SCISSOR_TEST);

	sceGuDepthFunc(GU_GEQUAL);
	sceGuEnable(GU_DEPTH_TEST);
	// sceGuDepthBuffer(dbp0, 512);

	// Enable clamped rgba texture mode
	sceGuTexWrap(GU_CLAMP, GU_CLAMP);
	sceGuTexMode(GU_PSM_5551, 0, 0, 0);
	sceGuEnable(GU_TEXTURE_2D);

	// Enable modulate blend mode
	sceGuEnable(GU_BLEND);
	sceGuTexFunc(GU_TFX_MODULATE, GU_TCC_RGBA);
	sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);

	sceGuSetMatrix(GU_PROJECTION, &_default);
	sceGuSetMatrix(GU_TEXTURE, &_default);
	sceGuSetMatrix(GU_MODEL, &_default);
	sceGuSetMatrix(GU_VIEW, &_default);

	// sceGuOffset(2048 - (480 / 2), 2048 - (272 / 2));
	sceGuViewport(0, 0, 480, 272);

	// Turn the display on, and finish the current list
	sceGuFinish();
	sceGuSync(GU_SYNC_FINISH, GU_SYNC_WHAT_DONE);

	sceGuDisplay(GU_TRUE);

	if (inited)
		return;
	inited = true;

	screen_gpuvtx = (struct DispVertexColored *)((u32)sceGuGetMemory(2 * SLICE_SIZE * sizeof(struct DispVertexColored)) + (u32)doubleBuffer);
	icons_gpuvtx = (struct DispVertex *)((u32)sceGuGetMemory(2 * SLICE_SIZE * sizeof(struct DispVertex)) + (u32)doubleBuffer);

	static const char *font = "flash0:/font/ltn1.pgf";	// small font
	static const char *font2 = "flash0:/font/ltn0.pgf"; // small font

	intraFontInit();
	Font = intraFontLoad(font, INTRAFONT_CACHE_ASCII);
	intraFontActivate(Font);
	intraFontSetStyle(Font, 0.6f, 0xFFFFFFFF, 0, 0, 0);

	SetupDisplay(0);
}

// From: https://github.com/CTurt/IconExtractor/blob/master/source/main.c

Header header;

int readBanner(char *filename, tNDSBanner *banner)
{
	FILE *romF = fopen(filename, "rb");
	if (!romF)
		return 1;

	fread(&header, sizeof(header), 1, romF);
	fseek(romF, header.banner_offset, SEEK_SET);
	fread(banner, sizeof(*banner), 1, romF);
	fclose(romF);

	return 0;
}

void loadImage(unsigned short *image, unsigned short *palette, unsigned char *tileData)
{
	int tile, pixel;
	for (tile = 0; tile < 16; tile++)
	{
		for (pixel = 0; pixel < 32; pixel++)
		{
			unsigned short a = tileData[(tile << 5) + pixel];

			int px = ((tile & 3) << 3) + ((pixel << 1) & 7);
			int py = ((tile >> 2) << 3) + (pixel >> 2);

			unsigned short upper = (a & 0xf0) >> 4;
			unsigned short lower = (a & 0x0f);

			if (upper != 0)
				image[(px + 1) + (py * 32)] = palette[upper];
			else
				image[(px + 1) + (py * 32)] = 0;

			if (lower != 0)
				image[px + (py * 32)] = palette[lower];
			else
				image[px + (py * 32)] = 0;
		}
	}
}

bool CreateRomIcon(char *file, f_list *list)
{

	N_Roms = 0;

	tNDSBanner banner;

	for (int c = 0; c < TOTAL_ICONS; c++)
	{

		if (list->cnt <= c)
			break;

		char rompath[256];

		int index = c + (curr_page * TOTAL_ICONS);

		if (list->cnt < index)
			break;

		strcpy(rompath, file);
		strcat(rompath, list->fname[index].name);

		if (readBanner(rompath, &banner))
		{
			return false;
		}
		else
		{
			loadImage(menu[c].GetIconData(), banner.palette, banner.icon);
			// DStoRGBA(image, imageRGBA);
		}

		menu[c].SetIconName(header.title);
		// menu[c].SetDevName(getDeveloperNameByID(atoi(header.makercode)).c_str());
		menu[c].SetFileName(list->fname[index].name);
		N_Roms++;
	}

	return true;
}

void DrawRom(char *file, f_list *list, int pos, bool reload)
{

	char rompath[256];
	char RomFileName[128];
	// Get rom file path
	strcpy(rompath, file);

	curr_page = pos / TOTAL_ICONS;
	curr_posX = pos % TOTAL_ICONS;

	if (old_page != curr_page)
	{
		CreateRomIcon(rompath, list);
		// getImageData(_sel,"sel.   ");
		old_page = curr_page;
	}
	drawmenu();
}