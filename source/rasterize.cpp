/*
	Copyright (C) 2009-2015 DeSmuME team
	This file is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 2 of the License, or
	(at your option) any later version.
	This file is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.
	You should have received a copy of the GNU General Public License
	along with the this software.  If not, see <http://www.gnu.org/licenses/>.
*/

//nothing in this file should be assumed to be accurate
//
//the shape rasterizers contained herein are based on code supplied by Chris Hecker from 
//http://chrishecker.com/Miscellaneous_Technical_Articles


//TODO - due to a late change of a y-coord flipping, our winding order is wrong
//this causes us to have to flip the verts for every front-facing poly.
//a performance improvement would be to change the winding order logic
//so that this is done less frequently

#include "rasterize.h"

#include <algorithm>
#include <assert.h>
#include <math.h>
#include <string.h>

#if defined(_MSC_VER) && _MSC_VER == 1600
#define SLEEP_HACK_2011
#endif

#ifdef SLEEP_HACK_2011
#include <Windows.h>
#endif

#ifndef _MSC_VER 
#include <stdint.h>
#endif

#include "bits.h"
#include "common.h"
#include "matrix.h"
#include "render3D.h"
#include "gfx3d.h"
#include "texcache.h"
#include "MMU.h"
#include "GPU.h"
#include "NDSSystem.h"


#include "PSP/vram.h"
#include "PSP/PSPDisplay.h"

#include <pspkernel.h>
#include <pspdisplay.h>

#include <pspgu.h>
#include <pspgum.h>
#include <malloc.h>


#define __MEM_START 0x04000000


inline void* vrelptr(void* ptr)
{
	return (void*)((u32)ptr & ~__MEM_START);
}

//volatile u32 _screen[GFX3D_FRAMEBUFFER_WIDTH * GFX3D_FRAMEBUFFER_HEIGHT];


CACHE_ALIGN const float divide5bitBy31_LUT[32] = { 0.0,             0.0322580645161, 0.0645161290323, 0.0967741935484,
													   0.1290322580645, 0.1612903225806, 0.1935483870968, 0.2258064516129,
													   0.2580645161290, 0.2903225806452, 0.3225806451613, 0.3548387096774,
													   0.3870967741935, 0.4193548387097, 0.4516129032258, 0.4838709677419,
													   0.5161290322581, 0.5483870967742, 0.5806451612903, 0.6129032258065,
													   0.6451612903226, 0.6774193548387, 0.7096774193548, 0.7419354838710,
													   0.7741935483871, 0.8064516129032, 0.8387096774194, 0.8709677419355,
													   0.9032258064516, 0.9354838709677, 0.9677419354839, 1.0 };

static bool softRastHasNewData = false;


struct PolyAttr
{ 
	u32 val;

	bool decalMode;
	bool translucentDepthWrite;
	bool drawBackPlaneIntersectingPolys;
	u8 polyid;
	u8 alpha;
	bool backfacing;
	bool translucent;
	u8 fogged;

	bool isVisible(bool backfacing) 
	{
		//this was added after adding multi-bit stencil buffer
		//it seems that we also need to prevent drawing back faces of shadow polys for rendering
		u32 mode = (val>>4)&0x3;
		if(mode==3 && polyid !=0) return !backfacing;
		//another reasonable possibility is that we should be forcing back faces to draw (mariokart doesnt use them)
		//and then only using a single bit buffer (but a cursory test of this doesnt actually work)
		//
		//this code needs to be here for shadows in wizard of oz to work.

		switch((val>>6)&3) {
			case 0: return false;
			case 1: return backfacing;
			case 2: return !backfacing;
			case 3: return true;
			default: /*assert(false);*/ return false;
		}
	}

	void setup(u32 polyAttr)
	{
		val = polyAttr;
		decalMode = BIT14(val);
		translucentDepthWrite = BIT11(val);
		polyid = (polyAttr>>24)&0x3F;
		alpha = (polyAttr>>16)&0x1F;
		drawBackPlaneIntersectingPolys = BIT12(val);
		fogged = BIT15(val);
	}

};

static void sortPolygons(SoftRasterizerEngine* engine) {
    POLY* polyArray = engine->polylist->list;
    size_t count = engine->polylist->count;
    std::sort(polyArray, polyArray + count, [](const POLY &a, const POLY &b) {
        if (a.texParam != b.texParam)
            return a.texParam < b.texParam;
        if (a.polyAttr != b.polyAttr)
            return a.polyAttr < b.polyAttr;
        return a.viewport < b.viewport;
    });
}

static inline void transformVertex(const VERT &vert, const VIEWPORT &viewport, Vertex &out) {
    __asm__ volatile(
        "lv.q       c000, 0 + %1      \n" // load vert.x,y,z,w into c000
        "vadd.s     s000, s000, s003   \n" // add w to x
        "vadd.s     s001, s001, s003   \n" // add w to y
        "vadd.s     s002, s002, s003   \n" // add w to z
        "vadd.s     s003, s003, s003   \n" // double w
        "vrcp.s     s003, s003         \n" // compute reciprocal 1/(w*2)
        "vscl.t     c000, c000, s003   \n" // scale vertex
        "ulv.q      c100, 0 + %2      \n" // load viewport params into c100
        "vi2f.q     c100, c100, 0      \n" // convert to float
        "vmul.p     c000, c000, c102   \n" // multiply with pre-set scale factor (c102)
        "vadd.p     c000, c000, c100   \n" // add viewport offset
        "vsub.s     s001, s200, s001   \n" // flip Y (S200 should hold constant 232)
		"vadd.s     s000, s000, s201   \n" // add viewport x offset
        "sv.s       s000, 0 + %0      \n" // store x
        "sv.s       s001, 4 + %0      \n" // store y
        "sv.s       s002, 8 + %0      \n" // store z
        : "=m"(out.x)
        : "m"(vert.x), "m"(viewport.x)
        : "memory"
    );
}

template<bool RENDERER>
class RasterizerUnit
{
public:
	RasterizerUnit(){}

	int polynum;

    PolyAttr polyAttr;
	SoftRasterizerEngine* engine;

	struct Vertex* __attribute__((aligned(32))) vertices;

	union{
		struct{ u8 r ; u8 g; u8 b; u8 a;};
		u32 color;
	}ArraytoColor;

	void SetupViewport(const u32 viewportValue) {
		sceGuViewport(0, 192,512,384);
	}

	u32 roundToExp2(u32 val)
	{
		u32 ret = 1;
		while(ret < val) ret <<= 1;
		return ret;
	}

	void SetupTexture(POLY& thePoly) {
		
		if (thePoly.texParam == 0 || thePoly.getTexParams().texFormat == TEXMODE_NONE) {
			sceGuDisable(GU_TEXTURE_2D);
		}
		else {

			TexCacheItem* newTexture = TexCache_SetTexture(TexFormat_32bpp, thePoly.texParam, thePoly.texPalette);

			sceGuEnable(GU_TEXTURE_2D);
			sceGumMatrixMode(GU_TEXTURE);

			/*sceGuTexFlush();
			sceGuTexProjMapMode(GU_UV);*/

			
			sceGuTexMode(GU_PSM_8888, 0, 0, 0);
			sceGuTexFilter(GU_NEAREST, GU_NEAREST);
			sceGuTexWrap(BIT16(newTexture->texformat) ? GU_REPEAT : GU_CLAMP, BIT17(newTexture->texformat) ? GU_REPEAT : GU_CLAMP);

			u16 tbw = (newTexture->bufferWidth + 15) & ~15;
			sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY, tbw, newTexture->decoded);

			
			
			//sceGuTexScale(newTexture->invSizeX, newTexture->invSizeY);
		}
	}

	void SetupPoly(POLY& thePoly)
	{
		static unsigned int lastTexBlendMode = 0;
		static int lastStencilState = -1;

		const PolygonAttributes attr = thePoly.getAttributes();

		static const int guTexBlendMode[4] = {GU_TFX_MODULATE, GU_TFX_DECAL, GU_TFX_MODULATE, GU_TFX_MODULATE};
		sceGuTexFunc(guTexBlendMode[attr.polygonMode], GU_TCC_RGBA);

		static const short GUDepthFunc[2] = { GU_LESS, GU_EQUAL };
		//sceGuDepthFunc(GUDepthFunc[attr.enableDepthTest]);
		
		// Set up culling mode
		static const uint8_t oglCullingMode[4] = {0, GU_CW, GU_CCW, 0};
		uint8_t cullingMode = oglCullingMode[attr.surfaceCullingMode];

	    if (cullingMode){
			sceGuEnable(GU_CULL_FACE);
			sceGuFrontFace(cullingMode);
		}
		else
		{
			sceGuDisable(GU_CULL_FACE);
		}

		bool enableDepthWrite = true;

		sceGuDisable(GU_STENCIL_TEST);
		if(attr.polygonMode == 3)
		{
			sceGuEnable(GU_STENCIL_TEST);

			if(attr.polygonID == 0)
			{
				//when the polyID is zero, we are writing the shadow mask.
				//set stencilbuf = 1 where the shadow volume is obstructed by geometry.
				//do not write color or depth information.
				sceGuStencilFunc(GU_ALWAYS, 65, 0xFF);
				sceGuStencilOp(GU_KEEP, GU_REPLACE, GU_KEEP);

				enableDepthWrite = false;
			}
			else
			{
				//when the polyid is nonzero, we are drawing the shadow poly.
				//only draw the shadow poly where the stencilbuf==1.
				//I am not sure whether to update the depth buffer here--so I chose not to.
				sceGuStencilFunc(GU_ALWAYS, 65, 0xFF);
				sceGuStencilOp(GU_KEEP, GU_KEEP, GU_REPLACE);
			}
		}
		else
		{
			sceGuEnable(GU_STENCIL_TEST);

			if(attr.isTranslucent)
			{
				sceGuStencilFunc(GU_NOTEQUAL, attr.polygonID, 255);
				sceGuStencilOp(GU_KEEP, GU_KEEP, GU_REPLACE);
			}
			else
			{
				sceGuStencilFunc(GU_ALWAYS, 64, 255);
				sceGuStencilOp(GU_REPLACE, GU_REPLACE, GU_REPLACE);
			}
		}

		if(attr.isTranslucent && !attr.enableAlphaDepthWrite)
			enableDepthWrite = false;
		
		sceGuDepthMask(enableDepthWrite);
	}

	bool init = false;
	FORCEINLINE void mainLoop()
	{
		using std::min;
		using std::max;

		const size_t polyCount = engine->polylist->count; //engine->clippedPolyCounter;

		static const int GUPrimitiveType[] = { GU_TRIANGLES , GU_TRIANGLE_FAN, GU_TRIANGLES , GU_TRIANGLE_FAN , GU_TRIANGLE_FAN, GU_TRIANGLE_FAN, GU_TRIANGLE_FAN, GU_TRIANGLE_FAN };

		static const int sz[] = {3, 4, 3, 4, 4, 4, 4, 4};
		
		bool first = true;
		int VertListIndex = 0;
		
		const bool _3dOnTop = MainScreen.offset == 0;


		VIEWPORT viewport;

		u32 lastTexParams = 0;
		u32 lastTexPalette = 0;
		u32 lastPolyAttr = 0;
		u32 lastViewport = 0xFFFFFFFF;

		int batching = 0;
		int batch_start = 0;
		size_t batched_draws = 0;
		int lastPolyPrimitive = GU_TRIANGLES;

		sceGuEnable(GU_SCISSOR_TEST);
		sceGuScissor((_3dOnTop ? 0 : 240), 40, (_3dOnTop ? 240 : 480), 232);

		__asm__ volatile("viim.s S200, 232\n");

		if (!_3dOnTop)
			__asm__ volatile("viim.s S201, 240\n");
		else
			__asm__ volatile("viim.s S201, 0\n");

		for(int i=0; i < polyCount; i++)
		{
			POLY &poly = engine->polylist->list[engine->indexlist->list[i]];
			int type = poly.type;

			if (lastPolyAttr != poly.polyAttr || i == 0)
			{
				
				if (batching){
					//sceKernelDcacheWritebackRange(&vertices[batch_start], batched_draws * sizeof(Vertex));
					sceGuDrawArray(lastPolyPrimitive, GU_TEXTURE_32BITF|GU_COLOR_8888|GU_VERTEX_32BITF|GU_TRANSFORM_2D, batched_draws, 0, &vertices[batch_start]);
				}
				lastPolyAttr = poly.polyAttr;
				SetupPoly(poly);
				polyAttr.setup(poly.polyAttr);

				batching = 0;

				if (!polyAttr.isVisible(poly.backfacing) && !polyAttr.drawBackPlaneIntersectingPolys)
                    continue;
					
			}


			if (lastTexParams != poly.texParam || lastTexPalette != poly.texPalette || i == 0)
			{

				if (batching){
					//sceKernelDcacheWritebackRange(&vertices[batch_start], batched_draws * sizeof(Vertex));
					sceGuDrawArray(lastPolyPrimitive, GU_TEXTURE_32BITF|GU_COLOR_8888|GU_VERTEX_32BITF|GU_TRANSFORM_2D, batched_draws, 0, &vertices[batch_start]);
				}

				this->SetupTexture(poly);
				lastTexParams = poly.texParam;
				lastTexPalette = poly.texPalette;
				//sceGuDrawArray(lastPolyPrimitive, GU_TRANSFORM_3D, 0, 0, &vertices[batch_start]);
				sceGuSendCommandi(0x12, (1<<23)); // Be able to transform using 2d draws the texture coordinates
				batching = 0;
			}

			if (lastViewport != poly.viewport || i == 0){

				if (batching){
					//sceKernelDcacheWritebackRange(&vertices[batch_start], batched_draws * sizeof(Vertex));
					sceGuDrawArray(lastPolyPrimitive, GU_TEXTURE_32BITF|GU_COLOR_8888|GU_VERTEX_32BITF|GU_TRANSFORM_2D, batched_draws, 0, &vertices[batch_start]);
				}
				viewport.decode(poly.viewport);
				
				lastViewport = poly.viewport;

				batching = 0;
			}

			const int polyPrimitive = !poly.isWireframe() ? GUPrimitiveType[poly.vtxFormat] : GU_LINE_STRIP;
			int vertexCount = sz[poly.vtxFormat];

		
			if (polyPrimitive != lastPolyPrimitive || polyPrimitive != GU_TRIANGLES) {
				if (batching){
					//sceKernelDcacheWritebackRange(&vertices[batch_start], batched_draws * sizeof(Vertex));
					sceGuDrawArray(lastPolyPrimitive, GU_TEXTURE_32BITF|GU_COLOR_8888|GU_VERTEX_32BITF|GU_TRANSFORM_2D, batched_draws, 0, &vertices[batch_start]);
				}
				lastPolyPrimitive = polyPrimitive;
				batching = 0;
			}

			const PolygonAttributes attr = poly.getAttributes();
                ArraytoColor.a = (!attr.isWireframe && attr.isTranslucent)
                                 ? static_cast<uint8_t>(divide5bitBy31_LUT[gfx3d.renderState.alphaTestRef] * 255)
                                 : 255;

			bool skip_vertex = false;

			for (int j = 0; j < vertexCount; j++) {
				VERT &vert = engine->vertlist->list[poly.vertIndexes[j]];

				if (vert.w < 0 && vert.z < 0) {
					skip_vertex = true;
					break;
				}
			}

			if (!skip_vertex)
			{
				for (int j = 0; j < vertexCount; j++) {
					VERT &vert = engine->vertlist->list[poly.vertIndexes[j]];
					Vertex &out = vertices[VertListIndex + j];

					ArraytoColor.r = static_cast<uint8_t>(vert.color[0] << 3);
					ArraytoColor.g = static_cast<uint8_t>(vert.color[1] << 3);
					ArraytoColor.b = static_cast<uint8_t>(vert.color[2] << 3);
					out.col = ArraytoColor.color;

					out.u = vert.u;
					out.v = vert.v;


					// Transform vertex position.
					transformVertex(vert, viewport, out);
				}


				if (batching) {
					batched_draws += vertexCount;
				} else {
					batch_start = VertListIndex;
					batched_draws = vertexCount;
					lastPolyPrimitive = polyPrimitive;
					batching = 1;
				}

				VertListIndex += vertexCount;
			}
		}

		//sceKernelDcacheWritebackRange(&vertices[batch_start], batched_draws * sizeof(Vertex));
		if (batching)
			sceGuDrawArray(lastPolyPrimitive, GU_TEXTURE_32BITF|GU_COLOR_8888|GU_VERTEX_32BITF|GU_TRANSFORM_2D, batched_draws, 0, &vertices[batch_start]);
		

		sceGuDisable(GU_STENCIL_TEST);
		sceGuDisable(GU_CULL_FACE);
		sceGuDisable(GU_SCISSOR_TEST);
		//sceGuEnable(GU_TEXTURE_2D);
	}
	

};

static SoftRasterizerEngine mainSoftRasterizer;
static RasterizerUnit<true> rasterizerUnit;

void GU_callback(int i){}

static char SoftRastInit(void)
{
	char result = Default3D_Init();
	if (result == 0)
	{
		return result;
	}

	
	rasterizerUnit.vertices = (struct Vertex*)sceGuGetMemory(1024 * sizeof(struct Vertex)) + (int)0x110000;
	rasterizerUnit.engine = &mainSoftRasterizer;
	memset(&rasterizerUnit.vertices[0], 0, 1024 * sizeof(struct Vertex));

	//sceGuSetCallback(GU_CALLBACK_FINISH, GU_callback);


	TexCache_Reset();
	return result;
}

static void SoftRastReset()
{
	softRastHasNewData = false;
	
	Default3D_Reset();
}

static void SoftRastClose()
{
	softRastHasNewData = false;
	
	Default3D_Close();
}

static void SoftRastVramReconfigureSignal()
{
	Default3D_VramReconfigureSignal();
}

static void SoftRastConvertFramebuffer(){ }


SoftRasterizerEngine::SoftRasterizerEngine()
{
	//clipper.clippedPolys = new GFX3D_Clipper::TClippedPoly[POLYLIST_SIZE];
}



void SoftRasterizerEngine::performClipping()
{
	/*clipper.reset();

	const size_t polyCount = polylist->count;

	for (size_t i = 0; i < polyCount; i++)
	{
		POLY* poly = &polylist->list[indexlist->list[i]];
		VERT* verts[4] = {
			&vertlist->list[poly->vertIndexes[0]],
			&vertlist->list[poly->vertIndexes[1]],
			&vertlist->list[poly->vertIndexes[2]],
			poly->type == 4
				? &vertlist->list[poly->vertIndexes[3]]
				: NULL
		};
		clipper.clipPoly<false>(poly,verts);

		/*const int n = poly->type - 1;

		//move that inside the clipper (vfpu? maybe)
		float facing = (verts[0]->y + verts[n]->y) * (verts[0]->x - verts[n]->x)
					 + (verts[1]->y + verts[0]->y) * (verts[1]->x - verts[0]->x)
					 + (verts[2]->y + verts[1]->y) * (verts[2]->x - verts[1]->x);

		for(int j = 2; j < n; j++)
			facing += (verts[j+1]->y + verts[j]->y) * (verts[j+1]->x - verts[j]->x);
		
		poly->backfacing = (facing < 0);*/
	/*}

	clippedPolyCounter = clipper.clippedPolyCounter;*/
}


static void SoftRastRender()
{
	mainSoftRasterizer.polylist = gfx3d.polylist;
	mainSoftRasterizer.vertlist = gfx3d.vertlist;
	mainSoftRasterizer.indexlist = &gfx3d.indexlist;
	mainSoftRasterizer.width = GFX3D_FRAMEBUFFER_WIDTH;
	mainSoftRasterizer.height = GFX3D_FRAMEBUFFER_HEIGHT;
	
	softRastHasNewData = true;

	// Sort polygons to minimize state changes.
	//sortPolygons(&mainSoftRasterizer);

	mainSoftRasterizer.performClipping();

	rasterizerUnit.mainLoop();
}

static void SoftRastRenderFinish()
{
	if (!softRastHasNewData) return;
	
	TexCache_EvictFrame();
	
	softRastHasNewData = false;
}

GPU3DInterface gpu3DRasterize = {
	"SoftRasterizer",
	SoftRastInit,
	SoftRastReset,
	SoftRastClose,
	SoftRastRender,
	SoftRastRenderFinish,
	SoftRastVramReconfigureSignal
};
