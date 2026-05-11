#include "rasterize.h"

#include <algorithm>
#include <assert.h>
#include <math.h>
#include <string.h>

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

CACHE_ALIGN const float divide5bitBy31_LUT[32] = {
    0.0,             0.0322580645161, 0.0645161290323, 0.0967741935484,
    0.1290322580645, 0.1612903225806, 0.1935483870968, 0.2258064516129,
    0.2580645161290, 0.2903225806452, 0.3225806451613, 0.3548387096774,
    0.3870967741935, 0.4193548387097, 0.4516129032258, 0.4838709677419,
    0.5161290322581, 0.5483870967742, 0.5806451612903, 0.6129032258065,
    0.6451612903226, 0.6774193548387, 0.7096774193548, 0.7419354838710,
    0.7741935483871, 0.8064516129032, 0.8387096774194, 0.8709677419355,
    0.9032258064516, 0.9354838709677, 0.9677419354839, 1.0
};

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
        u32 mode = (val>>4)&0x3;
        if(mode==3 && polyid !=0) return !backfacing;
        switch((val>>6)&3) {
            case 0: return false;
            case 1: return backfacing;
            case 2: return !backfacing;
            case 3: return true;
            default: return false;
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

// FIX: correct perspective divide (divide by w, not w*2)
// FIX: use proper temporaries, avoid clobbering GU registers (c100-c300 range)
// FIX: save/restore VFPU registers used by sceGu*
// The NDS clip-space range is [-w, w] for x,y and [0, w] for z.
// We need: x_screen = (x/w + 1) * viewport_w/2 + viewport_x
//          y_screen = (y/w + 1) * viewport_h/2 + viewport_y  (then flip)
//          z_ndc    = z / w  (for depth, [0,1] range on NDS)
static inline void transformVertex(const VERT &vert, const VIEWPORT &viewport,
                                   float screenY_max, float screenX_off,
                                   Vertex &out)
{
    if (vert.w <= 0.0f) {
        out.x = out.y = out.z = 0.0f;
        return;
    }

    const float inv_w = 1.0f / vert.w;
    const float nx = vert.x * inv_w;  // [-1,  1]
    const float ny = vert.y * inv_w;  // [-1,  1]
    const float nz = vert.z * inv_w;  // [ 0,  1] on NDS

    const float vw = viewport.width  ? (float)viewport.width  : 256.0f;
    const float vh = viewport.height ? (float)viewport.height : 192.0f;
    const float vx = (float)viewport.x;
    const float vy = (float)viewport.y;

    // Map NDC [-1,1] → viewport pixels, then offset to correct PSP screen half
    out.x = (nx + 1.0f) * (vw * 0.5f) + vx + screenX_off;

    // FIX: NDS y=+1 is screen TOP; PSP screen y grows downward from y=40.
    // screenY_max = 232 = 40 + 192.
    // ny=+1 → screen top    → PSP y = 40
    // ny=-1 → screen bottom → PSP y = 232
    out.y = screenY_max - ((ny + 1.0f) * (vh * 0.5f) + vy);

    // FIX: NDS z/w in [0,1], depth range is (65535→0), so z=0 (far) → depth=0,
    // z=1 (near) → depth=65535. Since depthRange(65535,0) maps [0,1]→[65535,0]:
    // GU applies: depth = near + z*(far-near) = 65535 + nz*(0-65535)
    // So nz=0 → depth=65535 (near clip?). That's inverted from what we want.
    // We want near geometry to WIN the depth test (GU_GEQUAL, larger=closer).
    // NDS: z/w=0 is far, z/w=1 is near.
    // We want far geometry to have small depth values, near to have large.
    // With depthRange(65535,0): z_float=0.0 → GU writes 65535, z_float=1.0 → writes 0.
    // That's BACKWARDS. We need to invert nz:
    out.z = 1.0f - nz;  // FIX: invert so near=large depth value for GU_GEQUAL
}

template<bool RENDERER>
class RasterizerUnit
{
public:
    RasterizerUnit(){}

    int polynum;
    PolyAttr polyAttr;
    SoftRasterizerEngine* engine;

    struct Vertex* __attribute__((aligned(64))) vertices;

    union {
        struct { u8 r; u8 g; u8 b; u8 a; };
        u32 color;
    } ArraytoColor;

    // FIX: SetupViewport now actually uses the value and sets GU depth range
    void SetupViewport(const u32 viewportValue)
    {
        VIEWPORT vp;
        vp.decode(viewportValue);
        // PSP GU viewport for 2D transform mode — we handle projection ourselves
        sceGuViewport(0, 0, 512, 272);
    }

    u32 roundToExp2(u32 val)
    {
        u32 ret = 1;
        while(ret < val) ret <<= 1;
        return ret;
    }

    // rasterize.cpp — fix problema 1: texture magenta

void SetupTexture(POLY& thePoly)
{
    if (thePoly.texParam == 0 || thePoly.getTexParams().texFormat == TEXMODE_NONE) {
        sceGuDisable(GU_TEXTURE_2D);
        return;
    }

    TexCacheItem* newTexture = TexCache_SetTexture(TexFormat_32bpp,
                                                    thePoly.texParam,
                                                    thePoly.texPalette);
    sceGuEnable(GU_TEXTURE_2D);
    sceGuTexMode(GU_PSM_8888, 0, 0, 0);
    sceGuTexFilter(GU_NEAREST, GU_NEAREST);
    sceGuTexWrap(
        BIT16(newTexture->texformat) ? GU_REPEAT : GU_CLAMP,
        BIT17(newTexture->texformat) ? GU_REPEAT : GU_CLAMP
    );

    // FIX: tbw must be a multiple of 16 pixels for GU_PSM_8888.
    // bufferWidth is already the POT texture width, but must be
    // explicitly rounded up to the nearest 16-pixel boundary.
    const u16 tbw = (u16)((newTexture->bufferWidth + 15) & ~15);

    sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY,
                  tbw, newTexture->decoded);

    // FIX: flush texture cache after uploading new texture data.
    // Without this the GU may read stale data from its internal cache.
    sceGuTexFlush();
    sceGuTexSync();

    sceGuTexScale(newTexture->invSizeX, newTexture->invSizeY);
    sceGuTexOffset(0.0f, 0.0f);
}

   void SetupPoly(POLY& thePoly)
{
    const PolygonAttributes attr = thePoly.getAttributes();

    static const int guTexBlendMode[4] = {
        GU_TFX_MODULATE, GU_TFX_DECAL, GU_TFX_MODULATE, GU_TFX_MODULATE
    };
    sceGuTexFunc(guTexBlendMode[attr.polygonMode], GU_TCC_RGBA);

    // FIX: depthRange(65535, 0) = reversed Z (larger value = closer to camera).
    // GU_LESS  would discard everything (buffer cleared to 0, all polys > 0).
    // GU_EQUAL would discard everything (no two polys share exact depth).
    // GU_GEQUAL is correct: passes when incoming depth >= buffer value.
    // Buffer starts at 0, first poly at any depth >= 0 passes. Correct.
    if (attr.enableDepthTest) {
    
        if (polyAttr.decalMode) {
            sceGuDepthFunc(GU_LEQUAL); // 1 = Sovrascrive i poligoni alla stessa profondità
        } else {
            //sceGuDepthFunc(GU_LESS);   // 0 = Rifiuta a parità di Z (Il background fallisce e resta DIETRO i bottoni!)
        }
        sceGuEnable(GU_DEPTH_TEST);
    } else {
        sceGuDepthFunc(GU_ALWAYS);
        sceGuEnable(GU_DEPTH_TEST);
    }

    // culling
    switch(attr.surfaceCullingMode) {
        case 1:
            sceGuEnable(GU_CULL_FACE);
            sceGuFrontFace(GU_CW);
            break;
        case 2:
            sceGuEnable(GU_CULL_FACE);
            sceGuFrontFace(GU_CCW);
            break;
        default:
            sceGuDisable(GU_CULL_FACE);
            break;
    }

    bool enableDepthWrite = true;

    sceGuDisable(GU_STENCIL_TEST);
    if (attr.polygonMode == 3) {
        sceGuEnable(GU_STENCIL_TEST);
        if (attr.polygonID == 0) {
            sceGuStencilFunc(GU_ALWAYS, 65, 0xFF);
            sceGuStencilOp(GU_KEEP, GU_REPLACE, GU_KEEP);
            enableDepthWrite = false;
        } else {
            sceGuStencilFunc(GU_EQUAL, 65, 0xFF);
            sceGuStencilOp(GU_KEEP, GU_KEEP, GU_REPLACE);
            enableDepthWrite = false;
        }
    } else {
        sceGuEnable(GU_STENCIL_TEST);
        if (attr.isTranslucent) {
            sceGuStencilFunc(GU_NOTEQUAL, attr.polygonID, 255);
            sceGuStencilOp(GU_KEEP, GU_KEEP, GU_REPLACE);
        } else {
            sceGuStencilFunc(GU_ALWAYS, 64, 255);
            sceGuStencilOp(GU_REPLACE, GU_REPLACE, GU_REPLACE);
        }
    }

    if (attr.isTranslucent && !attr.enableAlphaDepthWrite)
        enableDepthWrite = false;

    sceGuDepthMask(enableDepthWrite ? GU_FALSE : GU_TRUE);

     if (attr.isTranslucent) {
        // Poligono semitrasparente: alpha test con soglia dal registro NDS
        const u8 threshold = (u8)(divide5bitBy31_LUT[gfx3d.renderState.alphaTestRef % 32] * 255.0f);
        sceGuEnable(GU_ALPHA_TEST);
        sceGuAlphaFunc(GU_GREATER, threshold, 0xFF);
        sceGuEnable(GU_BLEND);
        sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);
    } else {
        // Poligono opaco: scarta solo i pixel completamente trasparenti (alpha=0)
        sceGuEnable(GU_ALPHA_TEST);
        sceGuAlphaFunc(GU_GREATER, 0, 0xFF);
        sceGuDisable(GU_BLEND);
    }
}

FORCEINLINE void mainLoop()
{
    const size_t polyCount = engine->polylist->count;
    if (polyCount == 0) return;
	

    const bool _3dOnTop   = (MainScreen.offset == 0);
    const float screenX_off = _3dOnTop ? 0.0f : 240.0f;
    const float screenY_top = 40.0f;

    sceGuEnable(GU_DEPTH_TEST);
    sceGuDepthFunc(GU_LEQUAL);      
    sceGuDepthMask(GU_FALSE);       // ABILITA la scrittura (False = Scrittura ON su PSP)
    
    // Puliamo lo Z-Buffer al valore "LONTANO"
    sceGuClearDepth(65535);         
    sceGuClear(GU_DEPTH_BUFFER_BIT | GU_STENCIL_BUFFER_BIT);


    // FIX B: scissor ai pixel PSP corretti per questo schermo
    sceGuEnable(GU_SCISSOR_TEST);
    sceGuScissor(_3dOnTop ? 0 : 240, 40, _3dOnTop ? 240 : 480, 232);

    sceGuEnable(GU_BLEND);
	sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);

    VIEWPORT viewport;
    u32 lastTexParams   = 0xFFFFFFFF;
    u32 lastTexPalette  = 0xFFFFFFFF;
    u32 lastPolyAttr    = 0xFFFFFFFF;
    u32 lastViewport    = 0xFFFFFFFF;
    int batching        = 0;
    int batch_start     = 0;
    int batched_draws   = 0;
    int VertListIndex   = 0;
    int lastPolyPrimitive = GU_TRIANGLES;

    auto flushBatch = [&]() {
        if (batching && batched_draws > 0) {
            /*sceKernelDcacheWritebackRange(
                &vertices[batch_start],
                batched_draws * sizeof(Vertex));*/
            sceGuDrawArray(
                lastPolyPrimitive,
                GU_TEXTURE_32BITF | GU_COLOR_8888 | GU_VERTEX_32BITF | GU_TRANSFORM_2D,
                batched_draws, 0, &vertices[batch_start]);
            batching = batched_draws = 0;
        }
    };

    static const int GUPrim[] = {
        GU_TRIANGLES, GU_TRIANGLE_FAN, GU_TRIANGLES, GU_TRIANGLE_FAN,
        GU_TRIANGLE_FAN, GU_TRIANGLE_FAN, GU_TRIANGLE_FAN, GU_TRIANGLE_FAN
    };
    static const int vsz[] = {3,4,3,4,4,4,4,4};

    for (int i = 0; i < (int)polyCount; i++)
    {
        POLY &poly = engine->polylist->list[engine->indexlist->list[i]];

        if (lastPolyAttr != poly.polyAttr) {
            flushBatch();
            lastPolyAttr = poly.polyAttr;
            polyAttr.setup(poly.polyAttr); 
            SetupPoly(poly);
        }

        if (!polyAttr.isVisible(poly.backfacing) &&
            !polyAttr.drawBackPlaneIntersectingPolys) continue;

        if (lastTexParams != poly.texParam || lastTexPalette != poly.texPalette) {
            flushBatch();
            SetupTexture(poly);
            lastTexParams  = poly.texParam;
            lastTexPalette = poly.texPalette;
            sceGuSendCommandi(0x12, (1<<23));
        }

        if (lastViewport != poly.viewport) {
            flushBatch();
            viewport.decode(poly.viewport);
            lastViewport = poly.viewport;
        }

        const int prim  = poly.isWireframe() ? GU_LINE_STRIP : GUPrim[poly.vtxFormat];
        const int vcnt  = vsz[poly.vtxFormat];

        if (batching && (prim != lastPolyPrimitive || prim != GU_TRIANGLES))
            flushBatch();
        lastPolyPrimitive = prim;

        const PolygonAttributes attr = poly.getAttributes();
        const u8 alpha = (!attr.isWireframe && attr.isTranslucent)
            ? (u8)(divide5bitBy31_LUT[attr.alpha] * 255.0f)
            : 255u;

        bool skip = false;
        for (int j = 0; j < vcnt; j++)
            if (engine->vertlist->list[poly.vertIndexes[j]].w <= 0.0f)
                { skip = true; break; }
        if (skip) continue;

        if (VertListIndex + vcnt > 1024) { flushBatch(); VertListIndex = 0; }

        for (int j = 0; j < vcnt; j++)
        {
            VERT   &v   = engine->vertlist->list[poly.vertIndexes[j]];
            Vertex &out = vertices[VertListIndex + j];

            // GU_COLOR_8888 su PSP = 0xAABBGGRR in memoria
            out.col = ((u32)alpha       << 24) |
                      ((u32)(v.color[2] << 2) << 16) |
                      ((u32)(v.color[1] << 2) <<  8) |
                      ((u32)(v.color[0] << 2));

            out.u = v.u;
            out.v = v.v;

            // Prospettiva
			const float inv_w = 1.0f / v.w;
        const float nx = v.x * inv_w;
        const float ny = v.y * inv_w;
        
        // Z normalizzata da 0.0 (vicino) a 1.0 (lontano)
        float nz = (v.z * inv_w + 1.0f) * 0.5f;

        const float vw = viewport.width  ? (float)viewport.width  : 256.0f;
        const float vh = viewport.height ? (float)viewport.height : 192.0f;

        out.x = (nx + 1.0f) * (vw * 0.5f) + viewport.x + screenX_off;
        out.y = 232.0f - ((ny + 1.0f) * (vh * 0.5f) + viewport.y);

        if (nz < 0.0f) nz = 0.0f;
        if (nz > 1.0f) nz = 1.0f;

        // Distribuiamo la Z sui 16-bit
        out.z = 65535.0f * nz;
        }

        if (batching) batched_draws += vcnt;
        else { batch_start = VertListIndex; batched_draws = vcnt; batching = 1; }
        VertListIndex += vcnt;
    }

    flushBatch();

    sceGuDisable(GU_SCISSOR_TEST);
    sceGuDisable(GU_STENCIL_TEST);
    sceGuDisable(GU_CULL_FACE);
    sceGuDisable(GU_DEPTH_TEST);
    sceGuDepthMask(GU_TRUE);
}
};

static SoftRasterizerEngine mainSoftRasterizer;
static RasterizerUnit<true> rasterizerUnit;

static char SoftRastInit(void)
{
    char result = Default3D_Init();
    if (result == 0)
        return result;

    // FIX: allocate from system heap aligned to 64 bytes, not from GU EDRAM
    // with an arbitrary offset that corrupted the pointer
    rasterizerUnit.vertices = (struct Vertex*)memalign(64, 1024 * sizeof(struct Vertex));
    if (!rasterizerUnit.vertices)
        return 0;

    rasterizerUnit.engine = &mainSoftRasterizer;
    memset(rasterizerUnit.vertices, 0, 1024 * sizeof(struct Vertex));

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

    // FIX: free the vertex buffer we allocated
    if (rasterizerUnit.vertices) {
        free(rasterizerUnit.vertices);
        rasterizerUnit.vertices = nullptr;
    }

    Default3D_Close();
}

static void SoftRastVramReconfigureSignal()
{
    Default3D_VramReconfigureSignal();
}

static void SoftRastConvertFramebuffer() {}

SoftRasterizerEngine::SoftRasterizerEngine() {}

void SoftRasterizerEngine::performClipping() {}

static void SoftRastRender()
{
    mainSoftRasterizer.polylist  = gfx3d.polylist;
    mainSoftRasterizer.vertlist  = gfx3d.vertlist;
    mainSoftRasterizer.indexlist = &gfx3d.indexlist;
    mainSoftRasterizer.width     = GFX3D_FRAMEBUFFER_WIDTH;
    mainSoftRasterizer.height    = GFX3D_FRAMEBUFFER_HEIGHT;

    softRastHasNewData = true;

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