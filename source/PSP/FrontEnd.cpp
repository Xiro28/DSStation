#include <pspkernel.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdarg.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <pspdebug.h>
#include <math.h>
#include <pspctrl.h>
#include <pspgu.h>
#include "FrontEnd.h"
#include <psprtc.h>
#include <pspdisplay.h>
#include <strings.h> // Provides strcasecmp
#include "PSPDisplay.h"

// JIT-vs-interpreter differential test (source/jit_difftest.cpp), run from the
// ROM-selection menu via TRIANGLE.
extern "C" void jit_difftest_run_force();

//---------------------------------------------------------------------
// SETTINGS structure: Holds a name, a description, and an integer value.
//---------------------------------------------------------------------
#define MAX_SETTINGS 30

typedef struct
{
	char name[64];
	char description[256];
	int value;
} SETTINGS;

SETTINGS settings[MAX_SETTINGS];
int totalSettings = 0;		// Count of the main settings
int totalSettingsDebug = 0; // Count of main settings plus debug settings

//---------------------------------------------------------------------
// Global variables used by the menus
//---------------------------------------------------------------------
int selposconfig = 0;
int selposDebug = 0;
bool changed = false;

//---------------------------------------------------------------------
// Helper function: Adds a new setting into the global settings array.
//---------------------------------------------------------------------
int addSetting(SETTINGS *setArr, int index, const char *name, const char *desc, int defaultValue)
{
	if (index >= MAX_SETTINGS)
		return index;
	strncpy(setArr[index].name, name, sizeof(setArr[index].name) - 1);
	setArr[index].name[sizeof(setArr[index].name) - 1] = '\0';
	strncpy(setArr[index].description, desc, sizeof(setArr[index].description) - 1);
	setArr[index].description[sizeof(setArr[index].description) - 1] = '\0';
	setArr[index].value = defaultValue;
	return index + 1;
}

//---------------------------------------------------------------------
// Helper function: Map a language number to its text representation.
// Mapping: 0 = JAP, 1 = ENG, 2 = FRE, 3 = GER, 4 = ITA, 5 = SPA, 6 = CHI, 7 = RES
//---------------------------------------------------------------------
const char *GetLanguageText(int lang)
{
	static const char *langMap[8] = {"JAP", "ENG", "FRE", "GER", "ITA", "SPA", "CHI", "RES"};
	if (lang < 0 || lang >= 8)
		return "UNK";
	return langMap[lang];
}

const char *GetFPSCapText(int val){
	static const char *capMap[] = {"No cap", "60", "50", "40", "30", "25"};
	if (val < 0 || val >= 6)
		return "UNK";
	return capMap[val];
}

//---------------------------------------------------------------------
// Initialize the main configuration settings and map them to the
// corresponding fields in the configured_features structure.
//---------------------------------------------------------------------
void InitMainSettings(configured_features *params)
{
	int c = 0;
	c = addSetting(settings, c, "Screen SWAP", "Swap the screen buffers", 0);
	params->swap = settings[0].value;

	c = addSetting(settings, c, "Show Touch Cursor", "Display the touch cursor", 0);
	params->cur = settings[1].value;

	c = addSetting(settings, c, "Show FPS", "Display frame rate on screen", 1);
	params->showfps = settings[2].value;

	c = addSetting(settings, c, "Enable Audio", "Enable sound output", 0);
	params->enable_sound = settings[3].value;

	c = addSetting(settings, c, "Frameskip", "Skip frames to improve performance", 0);
	params->frameskip = settings[4].value;

	// The language setting will be displayed as text.
	c = addSetting(settings, c, "Language", "Select firmware language", 1);
	params->firmware_language = settings[5].value;

	c = addSetting(settings, c, "Render 3D", "Enable 3D rendering", 1);
	params->Render3D = settings[6].value;

	//c = addSetting(settings, c, "Fast ME Rendering", "Enable fast ME rendering", 0);
	//params->FastMERendering = settings[7].value;

	c = addSetting(settings, c, "FPS Cap", "Limit the frames per second", 1);
	params->fps_cap_num = settings[7].value;

	//c = addSetting(settings, c, "Use cached Interpreter", "For a better stability but sometimes slower", 0);
	//params->cached_interpreter = settings[8].value;

	c = addSetting(settings, c, "Sort 3D polygons", "It helps in some game to improve the rendering. Can cause artifacts in other games", 0);
	params->sort_3d = settings[8].value;

	c = addSetting(settings, c, "3D always on top", "Draw 3D always on top of 2D scene", 0);
	params->_3d_always_on_top = settings[9].value;

	c = addSetting(settings, c, "AOT Pre-compile", "Compile all code before game starts (saved for next run)", 0);
	params->aot_precompile = settings[10].value;

	totalSettings = c;
}

void FinalizeMainSettings(configured_features *params)
{
	params->swap = settings[0].value;
	params->cur = settings[1].value;
	params->showfps = settings[2].value;
	params->enable_sound = settings[3].value;
	params->frameskip = settings[4].value;
	params->firmware_language = settings[5].value;
	params->Render3D = settings[6].value;
	//params->FastMERendering = settings[7].value;
	params->fps_cap_num = settings[7].value;
	params->sort_3d = settings[8].value;
	params->_3d_always_on_top = settings[9].value;
	params->aot_precompile = settings[10].value;
}



//---------------------------------------------------------------------
// Initialize the debug/display (GPU layer) settings.
// These settings are appended to the main settings.
//---------------------------------------------------------------------
void InitDisplayParams(configured_features *params)
{
	if (changed)
		return;

	int c = totalSettings;
	const char *namesTop[5] = {"BG0 TOP", "BG1 TOP", "BG2 TOP", "BG3 TOP", "OBJ TOP"};
	const char *namesBottom[5] = {"BG0 Bottom", "BG1 Bottom", "BG2 Bottom", "BG3 Bottom", "OBJ Bottom"};

	for (int j = 0; j < 5; j++)
	{
		char desc[128];
		sprintf(desc, "Display flag for %s", namesTop[j]);
		c = addSetting(settings, c, namesTop[j], desc, 1);
		params->gpuLayerEnabled[0][j] = settings[c - 1].value;
	}
	for (int j = 0; j < 5; j++)
	{
		char desc[128];
		sprintf(desc, "Display flag for %s", namesBottom[j]);
		c = addSetting(settings, c, namesBottom[j], desc, 1);
		params->gpuLayerEnabled[1][j] = settings[c - 1].value;
	}
	totalSettingsDebug = c;
}

//---------------------------------------------------------------------
// Update the GPU/display settings from the settings array into
// the configured_features structure.
//---------------------------------------------------------------------
void ChangeValueDebug(configured_features *params)
{
	int c = totalSettings;
	for (int j = 0; j < 5; j++, c++)
	{
		params->gpuLayerEnabled[0][j] = settings[c].value;
	}
	for (int j = 0; j < 5; j++, c++)
	{
		params->gpuLayerEnabled[1][j] = settings[c].value;
	}
	totalSettingsDebug = c;
}

//---------------------------------------------------------------------
// Display the main configuration settings. For the "Language" setting,
// show its mapped text (JAP, ENG, etc.) instead of a number.
//---------------------------------------------------------------------
void DisplayConfigParms()
{
	int yPos = 8;
	for (int i = 0; i < totalSettings; i++, yPos++)
	{
		// Insert section headers if desired.
		if (i == 3)
		{
			pspDebugScreenSetXY(5, yPos++);
			pspDebugScreenSetTextColor(0xff00ff00); // Green for sections
			pspDebugScreenPrintf("[ MISC ]\n");
		}
		else if (i == 0)
		{
			pspDebugScreenSetXY(5, yPos++);
			pspDebugScreenSetTextColor(0xff00ff00);
			pspDebugScreenPrintf("[ GUI ]\n");
		}
		pspDebugScreenSetXY(5, yPos);
		if (strcmp(settings[i].name, "Language") == 0)
		{
			// Display language value as text.
			if (i == selposconfig)
			{
				pspDebugScreenSetTextColor(0xffffff00);
				pspDebugScreenPrintf("> %-12s : %s\n", settings[i].name, GetLanguageText(settings[i].value));
			}
			else
			{
				pspDebugScreenSetTextColor(0xffffffff);
				pspDebugScreenPrintf("  %-12s : %s\n", settings[i].name, GetLanguageText(settings[i].value));
			}
		}
		else if (strcmp(settings[i].name, "FPS Cap") == 0)
		{
			// Display language value as text.
			if (i == selposconfig)
			{
				pspDebugScreenSetTextColor(0xffffff00);
				pspDebugScreenPrintf("> %-12s : %s\n", settings[i].name, GetFPSCapText(settings[i].value));
			}
			else
			{
				pspDebugScreenSetTextColor(0xffffffff);
				pspDebugScreenPrintf("  %-12s : %s\n", settings[i].name, GetFPSCapText(settings[i].value));
			}
		}
		else
		{
			// All other settings display as an integer.
			if (i == selposconfig)
			{
				pspDebugScreenSetTextColor(0xffffff00);
				pspDebugScreenPrintf("> %-12s : %d\n", settings[i].name, settings[i].value);
			}
			else
			{
				pspDebugScreenSetTextColor(0xffffffff);
				pspDebugScreenPrintf("  %-12s : %d\n", settings[i].name, settings[i].value);
			}
		}
	}

	// Leave a blank line and display the description of the currently selected setting.
	yPos += 5;
	pspDebugScreenSetXY(5, yPos);
	pspDebugScreenSetTextColor(0xffffffff); // Green for the description text
	pspDebugScreenPrintf("%s\n", settings[selposconfig].description);
}

//---------------------------------------------------------------------
// Display the debug (GPU/display) settings.
//---------------------------------------------------------------------
void DisplayDebugParms()
{
	for (int c = totalSettings; c < totalSettingsDebug; c++)
	{
		if (selposDebug == c)
			pspDebugScreenSetTextColor(0x0f00ffff); // Yellow highlight
		else
			pspDebugScreenSetTextColor(0xff00f55f); // Red
		pspDebugScreenPrintf("  %s : %d\n", settings[c].name, settings[c].value);
	}
}

//---------------------------------------------------------------------
// Debug menu loop for adjusting GPU/display settings.
//---------------------------------------------------------------------
void Debug(configured_features *params)
{
	int done = 0;
	SceCtrlData pad, oldPad = {0};
	pspDebugScreenSetXY(0, 0);
	selposDebug = totalSettings; // Start at first debug setting

	while (!done)
	{
		sceDisplayWaitVblankStart();
		pspDebugScreenSetTextColor(0xffffffff);
		pspDebugScreenSetXY(0, 3);
		pspDebugScreenPrintf("\n\n  Debug:\n\n  Disable Rendering: BG0 - BG1 - BG2 - BG3 - OBJ\n\n\n");

		ChangeValueDebug(params);
		DisplayDebugParms();

		if (sceCtrlPeekBufferPositive(&pad, 1))
		{
			if (pad.Buttons != oldPad.Buttons)
			{
				if (pad.Buttons & PSP_CTRL_LEFT)
					settings[selposDebug].value = 0;
				else if (pad.Buttons & PSP_CTRL_RIGHT)
				{
					settings[selposDebug].value = 1;
					changed = true;
				}
				if (pad.Buttons & PSP_CTRL_START)
				{
					pspDebugScreenSetTextColor(0xffffffff);
					done = 1;
					return;
				}
				if (pad.Buttons & PSP_CTRL_UP)
				{
					selposDebug--;
					if (selposDebug < totalSettings)
						selposDebug = totalSettings;
				}
				if (pad.Buttons & PSP_CTRL_DOWN)
				{
					selposDebug++;
					if (selposDebug >= totalSettingsDebug - 1)
						selposDebug = totalSettingsDebug - 1;
				}
			}
			oldPad = pad;
		}
	}
	pspDebugScreenSetTextColor(0xffffffff);
}

//---------------------------------------------------------------------
// Main configuration menu loop. Special handling is provided for the
// "Language" (displayed as text) and "Frameskip" settings.
//---------------------------------------------------------------------
void DoConfig(configured_features *params)
{
	int done = 0;
	SceCtrlData pad, oldPad = {0};

	pspDebugScreenSetXY(0, 0);
/*
#ifdef LOWRAM
	settings[5].value = 1;
	settings[6].value = 1;
#else
	settings[1].value = 1;
	settings[2].value = 1;
	settings[4].value = 1;
	settings[6].value = 1;
	settings[8].value = 1;
#endif
*/
	int langposconfig = 0;
	int frameposconfig = 0;
	
	InitMainSettings(params);

	while (!done)
	{
		sceDisplayWaitVblankStart();
		pspDebugScreenSetXY(5, 2);
		pspDebugScreenSetTextColor(0xff00ff00);
		pspDebugScreenPrintf("[ Emulator Settings ]\n");
		pspDebugScreenSetTextColor(0xffffffff);

		DisplayConfigParms();

		if (sceCtrlPeekBufferPositive(&pad, 1))
		{
			if (pad.Buttons != oldPad.Buttons)
			{
				switch (pad.Buttons)
				{
					case PSP_CTRL_LEFT:
						if (strcmp(settings[selposconfig].name, "Language") == 0)
						{
							settings[selposconfig].value = std::max(0, (settings[selposconfig].value - 1) % 8);
						}
						else if (strcmp(settings[selposconfig].name, "Frameskip") == 0)
						{
							settings[selposconfig].value = std::max(0, (settings[selposconfig].value - 1) % 10);
						}
						else if (strcmp(settings[selposconfig].name, "FPS Cap") == 0)
						{
							settings[selposconfig].value = std::max(0, (settings[selposconfig].value - 1) % 6);
						}
						else
						{
							settings[selposconfig].value = 0;
						}
					break;

					case PSP_CTRL_RIGHT:
						if (strcmp(settings[selposconfig].name, "Language") == 0)
						{
							settings[selposconfig].value = (settings[selposconfig].value + 1) % 8;
						}
						else if (strcmp(settings[selposconfig].name, "Frameskip") == 0)
						{
							settings[selposconfig].value = (settings[selposconfig].value + 1) % 10;
						}
						else if (strcmp(settings[selposconfig].name, "FPS Cap") == 0)
						{
							settings[selposconfig].value = (settings[selposconfig].value + 1) % 6;
						}
						else
						{
							settings[selposconfig].value = 1;
						}
					break;

					case PSP_CTRL_START:
						done = 1;
					break;

					case PSP_CTRL_UP:
						selposconfig = ((unsigned int)(selposconfig - 1)) % totalSettings;
					break;

					case PSP_CTRL_DOWN:
						selposconfig = ((unsigned int)(selposconfig + 1)) % totalSettings;
					break;
				
				default:
					break;
				}
			}
			oldPad = pad;
		}
	}
	pspDebugScreenSetTextColor(0xffffffff);
	FinalizeMainSettings(params);
}

//---------------------------------------------------------------------
// File Browser functions (unchanged)
//---------------------------------------------------------------------

f_list filelist;

void ClearFileList()
{
	filelist.cnt = 0;
	filelist.dir_cnt = 0;
}

#include <iostream>
#include <unordered_map>
#include <string_view>
#include <algorithm>
#include <cctype>
#include <array>

// File system includes for PSP (if required)
#include <pspiofilemgr.h>  

enum ExtId {
    EXT_NDS,
    EXT_GZ,
    EXT_ZIP,
    EXT_UNKNOWN
};

constexpr std::array extensions{
    std::pair<std::string_view, ExtId>{"nds", EXT_NDS},
    // {"gz", EXT_GZ},
    // {"zip", EXT_ZIP},
};

bool iequals(std::string_view a, std::string_view b) {
    return std::ranges::equal(a, b, [](char c1, char c2) {
        return std::tolower(c1) == std::tolower(c2);
    });
}

ExtId getExtId(std::string_view filePath) {
    auto pos = filePath.rfind('.');
    if (pos == std::string_view::npos || pos + 1 == filePath.size()) {
        return EXT_UNKNOWN; // No extension or empty extension
    }

    std::string_view ext = filePath.substr(pos + 1);
    for (const auto& [key, value] : extensions) {
        if (iequals(key, ext)) {
            return value;
        }
    }
    return EXT_UNKNOWN;
}


void GetFileList(const char *root) {
    int dfd = sceIoDopen(root);
    if (dfd <= 0) return;

    SceIoDirent dir;
    while (sceIoDread(dfd, &dir) > 0) {
        if (!(dir.d_stat.st_attr & FIO_SO_IFDIR)) { // Ignore directories
            if (getExtId(dir.d_name) != EXT_UNKNOWN) {
                strncpy(filelist.fname[filelist.cnt].name, dir.d_name, sizeof(filelist.fname[filelist.cnt].name) - 1);
                filelist.fname[filelist.cnt].name[sizeof(filelist.fname[filelist.cnt].name) - 1] = '\0'; // Null terminate
                filelist.cnt++;
            }
        }
    }
    sceIoDclose(dfd);
}




void GetPrevDir(char *path)
{
	int index = strlen(path) - 1;
	for (; path[--index] != '/' && index > 4;)
		;
	path[index] = 0;
}

int selpos = 0, oldpos = -1, oldpage = 0, ndir = 0;
void DisplayFileList(char *root)
{
	DrawRom(root, &filelist, selpos, true);
	return;
}

void DSEmuGui(char *path, char *out)
{
	char tmp[256];
	char app_path[128];
	SceCtrlData pad, oldPad = {0};

	printf("Starting UI\n");
	ClearFileList();
	printf("Cleared FILE list\n");
	getcwd(app_path, 128);
	printf("Got app_path\n");
	sprintf(tmp, "%s/ROMS/", app_path);
	printf("Added ROMS in path\n");
	GetFileList(tmp);
	printf("Got file list\n");

	while (1)
	{
		sceDisplayWaitVblankStart();
		pspDebugScreenSetXY(0, 3);
		DisplayFileList(tmp);
		if (sceCtrlPeekBufferPositive(&pad, 1))
		{
			if (pad.Buttons != oldPad.Buttons)
			{
				oldPad = pad;
				if (pad.Buttons & PSP_CTRL_HOME)
					sceKernelExitGame();
				if (pad.Buttons & PSP_CTRL_TRIANGLE)
				{
					// Run the JIT-vs-interpreter differential test over every
					// instruction, then wait for X to return to the ROM list.
					pspDebugScreenClear();
					pspDebugScreenSetXY(0, 0);
					jit_difftest_run_force();
					pspDebugScreenPrintf("\n  Press X to return.\n");
					SceCtrlData wpad;
					do { sceCtrlPeekBufferPositive(&wpad, 1); sceKernelDelayThread(50000); }
					while (!(wpad.Buttons & PSP_CTRL_CROSS));
					pspDebugScreenClear();
					oldPad = wpad;
					continue;
				}
				if (pad.Buttons & PSP_CTRL_CROSS)
				{
					sprintf(out, "%s/%s", tmp, filelist.fname[selpos].name);
					printf("ROM2: %s\n", out);
					break;
				}
				if (pad.Buttons & PSP_CTRL_UP)
				{
					selpos -= 1;
					if (selpos < 0)
						selpos = 0;
				}
				else if (pad.Buttons & PSP_CTRL_DOWN)
				{
					selpos += 1;
					if (selpos >= filelist.cnt)
						selpos = filelist.cnt - 1;
				}
				else if (pad.Buttons & PSP_CTRL_LEFT)
				{
					selpos -= 10;
					if (selpos < 0)
						selpos = 0;
				}
				else if (pad.Buttons & PSP_CTRL_RIGHT)
				{
					selpos += 10;
					if (selpos >= filelist.cnt - 1)
						selpos = filelist.cnt - 1;
				}
			}
		}
	}
}
