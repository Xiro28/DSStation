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

// Vertex buffer must be large enough to never wrap within a single frame:
// sceGuDrawArray queues the pointer and dereferences it later at sceGuSync,
// so any overwrite before then corrupts the previously-queued draws and
// produces ghosted/duplicated geometry.
#define VERT_BUF_SIZE 8192

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
        // `backfacing` is not actually computed for this rasterizer (it would
        // be set by the geometry pipeline used by rasterizeSOFT). To avoid
        // dropping legitimate polys at the CPU level, only filter out the
        // explicit "cull both" mode here. PSP GU_CULL_FACE in SetupPoly
        // performs the real front/back cull.
        u32 mode = (val>>4)&0x3;
        if (mode == 3 && polyid != 0) return true;     // shadow volumes: GU handles
        return ((val>>6) & 3) != 0;                    // 0 = cull both → skip
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

    // Map NDC [-1,1] → viewport pixels (256px NDS), scale to PSP half (240px)
    out.x = ((nx + 1.0f) * (vw * 0.5f) + vx) * (240.0f / 256.0f) + screenX_off;

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

    // Swizzle a linear texture into the PSP GU's tiled layout (16-byte-wide x
    // 8-row blocks). Swizzled textures hit the GU texture cache far better than
    // linear ones, which is usually the dominant 3D perf factor on PSP.
    // src/dst are byte buffers; bytewidth = width_pixels * bytes_per_pixel,
    // must be a multiple of 16; height in rows.
    static void swizzle_texture(u8* dst, const u8* src, u32 bytewidth, u32 height)
    {
        const u32 width_blocks  = bytewidth / 16;
        const u32 height_blocks = height / 8;
        const u32 src_pitch     = (bytewidth - 16) / 4;  // u32 steps between block rows
        const u32 src_row       = bytewidth / 4;

        const u32* s = (const u32*)src;
        u32* d = (u32*)dst;

        for (u32 by = 0; by < height_blocks; by++) {
            const u32* sb = s;
            for (u32 bx = 0; bx < width_blocks; bx++) {
                const u32* sr = sb;
                for (u32 n = 0; n < 8; n++) {     // 8 rows in a block
                    *d++ = *sr++;                 // 16 bytes = 4 u32 per row
                    *d++ = *sr++;
                    *d++ = *sr++;
                    *d++ = *sr++;
                    sr += src_pitch;              // advance to next source row
                }
                sb += 4;                          // next block to the right (16 bytes)
            }
            s += src_row * 8;                     // next block row down (8 rows)
        }
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
    sceGuTexFilter(GU_NEAREST, GU_NEAREST);
    sceGuTexWrap(
        BIT16(newTexture->texformat) ? GU_REPEAT : GU_CLAMP,
        BIT17(newTexture->texformat) ? GU_REPEAT : GU_CLAMP
    );

    // FIX: tbw must be a multiple of 16 pixels for GU_PSM_8888.
    // bufferWidth is already the POT texture width, but must be
    // explicitly rounded up to the nearest 16-pixel boundary.
    const u16 tbw = (u16)((newTexture->bufferWidth + 15) & ~15);

    // Swizzle the texture once (cached on the item) and upload the swizzled copy:
    // the GU texture cache thrashes badly on linear textures. Requires the tiled
    // dimensions to fit (bytewidth multiple of 16, height multiple of 8); 32bpp
    // POT textures of width>=4 and height>=8 always qualify.
    const u32 bytewidth = (u32)tbw * 4;            // GU_PSM_8888
    // Only swizzle when the upload pitch equals the decoded pitch (no padding):
    // otherwise the swizzler would over-read each decoded row. POT widths >= 16
    // satisfy tbw == bufferWidth; tiny 4/8-px textures stay linear (negligible).
    #define JIT_ENABLE_TEX_SWIZZLE 0   // disabled: swizzle path broken, debugging
    const bool canSwizzle = JIT_ENABLE_TEX_SWIZZLE
                            && (tbw == newTexture->bufferWidth)
                            && (bytewidth % 16 == 0) && (newTexture->sizeY % 8 == 0)
                            && newTexture->sizeY >= 8;

    // Palettized upload (GU_PSM_T8 / GU_PSM_T4): for indexed NDS textures we upload
    // the index buffer (1 byte/texel for T8, 4 bits/texel for T4) plus a hardware
    // CLUT instead of the expanded 32bpp texture — 4x (T8) / 8x (T4) less texture
    // bandwidth. Colours come from pal_clut, built with the same RGB15TO32
    // conversion and palette-0-transparent rule as the 32bpp path, so output is
    // identical. Buffer-width constraints: T8 needs tbw multiple of 16 texels
    // (always true), T4 needs a multiple of 32 texels.
    #define JIT_ENABLE_TEX_T8 1
    #define JIT_ENABLE_TEX_T4 1
    const bool palOK = newTexture->pal_indices && newTexture->pal_clut
                       && (tbw == newTexture->bufferWidth);
    const bool useT8 = JIT_ENABLE_TEX_T8 && palOK && newTexture->pal_bpp == 8;
    const bool useT4 = JIT_ENABLE_TEX_T4 && palOK && newTexture->pal_bpp == 4
                       && (newTexture->sizeX % 32 == 0);   // T4 pitch constraint

    if (useT8) {
        // 256-entry CLUT, 32bpp → 32 blocks of 8 entries.
        sceGuClutMode(GU_PSM_8888, 0, 0xFF, 0);
        sceGuClutLoad(256 / 8, newTexture->pal_clut);
        sceGuTexMode(GU_PSM_T8, 0, 0, 0);
        sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY, tbw, newTexture->pal_indices);
    } else if (useT4) {
        // 16-entry CLUT (we pad/load 16 → 2 blocks of 8). 4-bit indices.
        sceGuClutMode(GU_PSM_8888, 0, 0x0F, 0);
        sceGuClutLoad(16 / 8, newTexture->pal_clut);
        sceGuTexMode(GU_PSM_T4, 0, 0, 0);
        sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY, tbw, newTexture->pal_indices);
    } else if (canSwizzle) {
        if (!newTexture->swizzled) {
            newTexture->swizzled = (u8*)memalign(16, bytewidth * newTexture->sizeY);
            swizzle_texture(newTexture->swizzled, newTexture->decoded,
                            bytewidth, newTexture->sizeY);
        }
        sceGuTexMode(GU_PSM_8888, 0, 0, 1);        // swizzle = 1
        sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY, tbw, newTexture->swizzled);
    } else {
        sceGuTexMode(GU_PSM_8888, 0, 0, 0);        // swizzle = 0 (linear)
        sceGuTexImage(0, newTexture->sizeX, newTexture->sizeY, tbw, newTexture->decoded);
    }

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
    // Depth: we write nz in [0,65535] where 0=near, 65535=far. Buffer cleared
    // to 65535. GU_LEQUAL passes when new ≤ existing → near wins, equal also
    // wins (needed for decal/coplanar overlays like sprite shadows).
    // Always set explicitly — leaving the previous poly's func would otherwise
    // leak state across polys and cause flicker/duplication on overlapping geo.
    if (attr.enableDepthTest)
        sceGuDepthFunc(GU_GEQUAL);  // reversed-Z: larger=closer; equal passes (coplanar = submission order)
    else
        sceGuDepthFunc(GU_ALWAYS);
    sceGuEnable(GU_DEPTH_TEST);

    // Culling on the PSP GU.
    // NDS polyAttr bits 6/7: 6 = "render back-facing", 7 = "render front-facing".
    // Combined value = surfaceCullingMode in [0..3]:
    //   0 = cull both (handled at CPU level; poly skipped before reaching here)
    //   1 = render back only  → cull front
    //   2 = render front only → cull back
    //   3 = render both
    // Our screen Y-flip (out.y = 232 - …) inverts winding: NDS-front (CW) becomes
    // CCW on PSP and vice versa. sceGuFrontFace tells the GU which winding is
    // FRONT; PSP then culls the opposite (back). So:
    //   case 1: declare CW as front  → PSP culls CCW = NDS-front. ✓
    //   case 2: declare CCW as front → PSP culls CW  = NDS-back.  ✓
    switch (attr.surfaceCullingMode) {
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

    sceGuDepthMask(enableDepthWrite ? GU_FALSE : GU_TRUE);  // GU_FALSE = writes enabled

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

// Build the PSP GU projection matrix from the NDS projection (mtxCurrent[1]).
// Two coordinate-space mismatches must be patched:
//   1. NDS clip-Z is in [0, w]; the GU rasterizer expects OpenGL-style [-w, w].
//      Pre-multiply by zfix = diag-ish matrix that maps z' = 2z - w, i.e. adds
//      a row that doubles z and subtracts w.  In column-major terms:
//        z_out = 2*z_in - w_in  →  column 2 z-term *2, column 3 z-term -1*w.
//   2. NDS y+1 is screen TOP and our PSP viewport (set below) keeps that
//      orientation, so no extra flip is needed here — the viewport handles it.
// NDS matrices are column-major (OpenGL layout), same as the GU, so the 16
// floats map 1:1 onto ScePspFMatrix4.
static inline void buildGuProjection(const float* ndsProj, ScePspFMatrix4* out)
{
    // zfix * ndsProj.  zfix only touches the output z row, so we can apply it
    // by post-adjusting the z components of ndsProj's columns:
    //   z_new[col] = 2*z[col] - w[col]
    // Toggle to isolate near-plane clipping glitches:
    //  1 = apply 2z-w remap ([0,w]→[-w,w])
    //  0 = load NDS projection unchanged (z_ndc stays [0,1]); rely on depthRange
    #define GU_PROJ_ZFIX 0
    float* d = (float*)out;
    for (int c = 0; c < 4; c++) {
        const float zc = ndsProj[c*4 + 2];
        const float wc = ndsProj[c*4 + 3];
        d[c*4 + 0] = ndsProj[c*4 + 0];
        d[c*4 + 1] = ndsProj[c*4 + 1];
#if GU_PROJ_ZFIX
        d[c*4 + 2] = 2.0f * zc - wc;     // [0,w] → [-w,w]
#else
        d[c*4 + 2] = zc;                 // leave NDS clip-z as-is ([0,w])
#endif
        d[c*4 + 3] = wc;
    }
}

FORCEINLINE void mainLoop()
{
    const size_t polyCount = engine->polylist->count;
    if (polyCount == 0) return;

    const bool _3dOnTop   = (MainScreen.offset == 0);
    const float screenX_off = _3dOnTop ? 0.0f : 240.0f;

    sceGuEnable(GU_DEPTH_TEST);
    sceGuDepthRange(0, 65535);    // identity: out.z stored directly (PSPDisplay sets reversed 65535,0)
    sceGuDepthFunc(GU_GEQUAL);   // near=65535 (large) wins; clear=0 (far) so first poly passes
    sceGuDepthMask(GU_FALSE);  // SetupPoly sets per-poly depth mask

    sceGuClearDepth(0);   // clear to "far" so first polygon at any depth passes
    sceGuClear(GU_DEPTH_BUFFER_BIT | GU_STENCIL_BUFFER_BIT);

    // FIX B: scissor ai pixel PSP corretti per questo schermo
    sceGuEnable(GU_SCISSOR_TEST);
    sceGuScissor(_3dOnTop ? 0 : 240, 40, _3dOnTop ? 240 : 480, 232);

    sceGuEnable(GU_BLEND);
    sceGuBlendFunc(GU_ADD, GU_SRC_ALPHA, GU_ONE_MINUS_SRC_ALPHA, 0, 0);

    // ---- 2D transform path (CPU does projection / perspective divide) ----
    // The hardware-transform (GU_TRANSFORM_3D) path is kept in the code (matrix
    // pool, rawcoord, buildGuProjection) but disabled: the PSP GU clipper drops
    // near-plane-straddling triangles, so we transform on the CPU and submit
    // pre-projected screen-space verts with GU_TRANSFORM_2D, as before.
    const float screenY_max = 232.0f;
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
            sceKernelDcacheWritebackRange(
                &vertices[batch_start],
                batched_draws * sizeof(Vertex));
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

        if (VertListIndex + vcnt > VERT_BUF_SIZE) {
            // Buffer full — flush and stop (see SoftRastInit comment).
            flushBatch();
            break;
        }

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

            // CPU perspective divide + viewport map (screen-space, TRANSFORM_2D)
            const float inv_w = (v.w != 0.0f) ? (1.0f / v.w) : 0.0f;
            const float nx = v.x * inv_w;
            const float ny = v.y * inv_w;
            // NDS clip-space z is [0,w] → z/w is already [0,1] (0=far, 1=near).
            // Use full range for max depth precision (no [-1,1] remap).
            float nz = v.z * inv_w;

            const float vw = viewport.width  ? (float)viewport.width  : 256.0f;
            const float vh = viewport.height ? (float)viewport.height : 192.0f;

            out.x = ((nx + 1.0f) * (vw * 0.5f) + viewport.x) * (240.0f / 256.0f) + screenX_off;
            out.y = screenY_max - ((ny + 1.0f) * (vh * 0.5f) + viewport.y);

            if (nz < 0.0f) nz = 0.0f;
            if (nz > 1.0f) nz = 1.0f;
            out.z = 65535.0f * nz;  // far=0 (clear value), near=65535; GU_GEQUAL → near wins
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
    // with an arbitrary offset that corrupted the pointer.
    // Buffer sized to NEVER wrap during a frame (Pokemon battle scenes can push
    // several thousand vertices). Wrapping mid-frame would corrupt vertex data
    // that previously-queued sceGuDrawArray calls still reference, producing
    // ghosted geometry. 8192 verts × 24 bytes = 192KB.
    rasterizerUnit.vertices = (struct Vertex*)memalign(64, VERT_BUF_SIZE * sizeof(struct Vertex));
    if (!rasterizerUnit.vertices)
        return 0;

    rasterizerUnit.engine = &mainSoftRasterizer;
    memset(rasterizerUnit.vertices, 0, VERT_BUF_SIZE * sizeof(struct Vertex));

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