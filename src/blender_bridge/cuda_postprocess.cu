/**
 * @file cuda_postprocess.cu
 * @brief CUDA post-processing kernels matching the main app's GLSL pipeline.
 *
 * Pipeline order:
 *   1. Bloom: bright-pass threshold -> multi-scale separable Gaussian blur -> additive composite.
 *   2. ACES tonemapping + chromatic aberration + vignette + film grain + gamma.
 *
 * WHY: The raw geodesic kernel output is dim and lacks the cinematic look
 *      of the main app. These kernels replicate the same post-processing
 *      pipeline used in shader/bloom_*.frag and shader/tonemapping.frag.
 *
 * HOW: Called by cuda_renderer.cu after the geodesic kernel.
 *      All operations are in-place on the linear float4 framebuffer.
 */

#include <cuda_runtime.h>
#include <cstdio>

/* ========================================================================
 * Bloom: bright-pass threshold -> separable Gaussian blur -> additive mix
 *
 * Simplified from the main app's 6-iteration downsample/upsample pyramid
 * into a single separable blur at multiple scales, additively composited.
 * This is faster and produces a similar visual result.
 * ======================================================================== */

/** @brief Compute perceptual luminance of an RGBA pixel (Rec. 709 coefficients). */
static __device__ float luminance(float4 c) {
    return 0.2126f * c.x + 0.7152f * c.y + 0.0722f * c.z;
}

/**
 * @brief Horizontal separable Gaussian blur pass.
 *
 * @param src    Input framebuffer [w * h].
 * @param dst    Output framebuffer [w * h].
 * @param w      Image width.
 * @param h      Image height.
 * @param radius Half-kernel radius in pixels; sigma = radius * 0.5.
 */
__global__ void bloom_blur_h(const float4* __restrict__ src, float4* __restrict__ dst,
                              int w, int h, int radius) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= w || py >= h) return;

    float4 sum = make_float4(0, 0, 0, 0);
    float wt = 0;
    float sigma = radius * 0.5f;
    float inv2s2 = 1.0f / (2.0f * sigma * sigma);

    for (int dx = -radius; dx <= radius; dx++) {
        int sx = min(max(px + dx, 0), w - 1);
        float g = expf(-(float)(dx * dx) * inv2s2);
        float4 s = src[py * w + sx];
        sum.x += s.x * g;
        sum.y += s.y * g;
        sum.z += s.z * g;
        wt += g;
    }
    float inv_wt = 1.0f / wt;
    dst[py * w + px] = make_float4(sum.x * inv_wt, sum.y * inv_wt, sum.z * inv_wt, 1.0f);
}

/**
 * @brief Vertical separable Gaussian blur pass (complement to bloom_blur_h).
 *
 * @param src    Input framebuffer [w * h].
 * @param dst    Output framebuffer [w * h].
 * @param w      Image width.
 * @param h      Image height.
 * @param radius Half-kernel radius in pixels; sigma = radius * 0.5.
 */
__global__ void bloom_blur_v(const float4* __restrict__ src, float4* __restrict__ dst,
                              int w, int h, int radius) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= w || py >= h) return;

    float4 sum = make_float4(0, 0, 0, 0);
    float wt = 0;
    float sigma = radius * 0.5f;
    float inv2s2 = 1.0f / (2.0f * sigma * sigma);

    for (int dy = -radius; dy <= radius; dy++) {
        int sy = min(max(py + dy, 0), h - 1);
        float g = expf(-(float)(dy * dy) * inv2s2);
        float4 s = src[sy * w + px];
        sum.x += s.x * g;
        sum.y += s.y * g;
        sum.z += s.z * g;
        wt += g;
    }
    float inv_wt = 1.0f / wt;
    dst[py * w + px] = make_float4(sum.x * inv_wt, sum.y * inv_wt, sum.z * inv_wt, 1.0f);
}

/**
 * @brief Bright-pass filter: retain only pixels whose luminance exceeds @p threshold.
 *
 * The excess energy above the threshold is preserved in color proportion, so
 * only the bloom-contributing portion of each pixel is extracted.
 *
 * @param src       Input framebuffer.
 * @param dst       Output framebuffer (bright regions only).
 * @param w         Image width.
 * @param h         Image height.
 * @param threshold Luminance threshold; pixels below this contribute zero bloom.
 */
__global__ void bloom_bright_pass(const float4* __restrict__ src, float4* __restrict__ dst,
                                   int w, int h, float threshold) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= w || py >= h) return;

    float4 c = src[py * w + px];
    float lum = luminance(c);
    float excess = fmaxf(0.0f, lum - threshold);
    float scale = (lum > 0.001f) ? excess / lum : 0.0f;
    dst[py * w + px] = make_float4(c.x * scale, c.y * scale, c.z * scale, 1.0f);
}

/**
 * @brief Additive bloom composite: base[i] += bloom_buf[i] * strength.
 *
 * @param base      Base framebuffer modified in-place.
 * @param bloom_buf Bloom contribution buffer.
 * @param w         Image width.
 * @param h         Image height.
 * @param strength  Bloom mix weight.
 */
__global__ void bloom_composite(float4* __restrict__ base, const float4* __restrict__ bloom_buf,
                                 int w, int h, float strength) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= w || py >= h) return;

    int idx = py * w + px;
    float4 b = base[idx];
    float4 bl = bloom_buf[idx];
    base[idx] = make_float4(b.x + bl.x * strength, b.y + bl.y * strength,
                             b.z + bl.z * strength, 1.0f);
}

/* ========================================================================
 * Tonemapping: ACES + chromatic aberration + vignette + film grain
 * Matches shader/tonemapping.frag exactly.
 * ======================================================================== */

/**
 * @brief Combined tonemapping kernel: exposure -> ACES filmic -> chromatic aberration
 *        -> vignette -> film grain -> gamma 2.2.
 *
 * Matches shader/tonemapping.frag exactly. All operations are in-place on @p fb.
 *
 * @param fb            Framebuffer to process in-place [w * h].
 * @param w             Image width.
 * @param h             Image height.
 * @param time_sec      Render time used to animate film grain noise.
 * @param exposure_gain Linear exposure multiplier applied before ACES.
 */
__global__ void tonemap_kernel(float4* __restrict__ fb, int w, int h,
                                float time_sec, float exposure_gain) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= w || py >= h) return;

    float u = (float)px / (float)w;
    float v = (float)py / (float)h;
    float2 texCoord = make_float2(u, v);
    float2 center = make_float2(0.5f, 0.5f);
    float dist = sqrtf((u - 0.5f) * (u - 0.5f) + (v - 0.5f) * (v - 0.5f));

    /* Chromatic aberration */
    float caStrength = 0.002f * dist;
    float2 dir = make_float2(u - 0.5f, v - 0.5f);
    int rx = min(max((int)((u - dir.x * caStrength) * w), 0), w - 1);
    int ry = min(max((int)((v - dir.y * caStrength) * h), 0), h - 1);
    int bx = min(max((int)((u + dir.x * caStrength) * w), 0), w - 1);
    int by = min(max((int)((v + dir.y * caStrength) * h), 0), h - 1);

    float r = fb[ry * w + rx].x;
    float g = fb[py * w + px].y;
    float b = fb[by * w + bx].z;
    float3 color = make_float3(r, g, b);

    /* Exposure gain (applied before tonemapping to bring kernel output into visible range) */
    color.x *= exposure_gain;
    color.y *= exposure_gain;
    color.z *= exposure_gain;

    /* Vignette */
    float vignette = 1.0f - dist * dist * 0.5f;
    vignette = fmaxf(vignette, 0.0f);
    vignette = sqrtf(vignette);  /* smooth falloff */
    color.x *= vignette;
    color.y *= vignette;
    color.z *= vignette;

    /* ACES Filmic (Narkowicz 2015) */
    float a = 2.51f, bb = 0.03f, c = 2.43f, d = 0.59f, e = 0.14f;
    color.x = fminf(fmaxf((color.x * (a * color.x + bb)) / (color.x * (c * color.x + d) + e), 0.0f), 1.0f);
    color.y = fminf(fmaxf((color.y * (a * color.y + bb)) / (color.y * (c * color.y + d) + e), 0.0f), 1.0f);
    color.z = fminf(fmaxf((color.z * (a * color.z + bb)) / (color.z * (c * color.z + d) + e), 0.0f), 1.0f);

    /* Film grain */
    float grainStrength = 0.005f;
    float noise = fmodf(fabsf(sinf((float)px * 12.9898f + (float)py * 78.233f + time_sec) * 43758.5453f), 1.0f);
    color.x += (noise - 0.5f) * grainStrength;
    color.y += (noise - 0.5f) * grainStrength;
    color.z += (noise - 0.5f) * grainStrength;

    /* Gamma */
    float gamma = 1.0f / 2.2f;
    color.x = powf(fmaxf(color.x, 0.0f), gamma);
    color.y = powf(fmaxf(color.y, 0.0f), gamma);
    color.z = powf(fmaxf(color.z, 0.0f), gamma);

    fb[py * w + px] = make_float4(color.x, color.y, color.z, 1.0f);
}

/* ========================================================================
 * Host API: apply full post-processing pipeline to a framebuffer
 * ======================================================================== */

extern "C" {

/**
 * @brief Apply the full post-processing pipeline to a device framebuffer in-place.
 *
 * Steps: bright-pass -> multi-scale separable Gaussian blur (radii 4/8/16/32) ->
 * additive bloom composite -> ACES tonemap + CA + vignette + grain + gamma.
 *
 * @param d_framebuffer   Device float4 framebuffer [width * height], modified in-place.
 * @param width           Image width in pixels.
 * @param height          Image height in pixels.
 * @param bloom_threshold Luminance threshold for the bright-pass.
 * @param bloom_strength  Bloom additive mix weight.
 * @param exposure_gain   Linear exposure multiplier applied before tonemapping.
 * @param time_sec        Render time for animated film grain [s].
 * @return 0 (CUDA errors are currently not checked; caller should synchronize).
 */
int bhb_cuda_postprocess(float4* d_framebuffer, int width, int height,
                          float bloom_threshold, float bloom_strength,
                          float exposure_gain, float time_sec) {
    dim3 block(16, 16);
    dim3 grid((width + 15) / 16, (height + 15) / 16);

    /* Allocate temp buffers for bloom */
    size_t fb_size = (size_t)width * height * sizeof(float4);
    float4 *d_bright = nullptr, *d_temp = nullptr, *d_bloom_accum = nullptr;
    cudaMalloc(&d_bright, fb_size);
    cudaMalloc(&d_temp, fb_size);
    cudaMalloc(&d_bloom_accum, fb_size);
    cudaMemset(d_bloom_accum, 0, fb_size);

    /* 1. Bright-pass */
    bloom_bright_pass<<<grid, block>>>(d_framebuffer, d_bright, width, height, bloom_threshold);

    /* 2. Multi-scale separable Gaussian blur + accumulate */
    int radii[] = {4, 8, 16, 32};
    for (int i = 0; i < 4; i++) {
        bloom_blur_h<<<grid, block>>>(d_bright, d_temp, width, height, radii[i]);
        bloom_blur_v<<<grid, block>>>(d_temp, d_bright, width, height, radii[i]);
        /* Accumulate into bloom_accum */
        bloom_composite<<<grid, block>>>(d_bloom_accum, d_bright, width, height, 1.0f);
        /* Re-extract bright for next scale */
        bloom_bright_pass<<<grid, block>>>(d_framebuffer, d_bright, width, height, bloom_threshold);
    }

    /* 3. Composite bloom onto original */
    bloom_composite<<<grid, block>>>(d_framebuffer, d_bloom_accum, width, height, bloom_strength);

    /* 4. Tonemap (exposure + ACES + CA + vignette + grain + gamma) */
    tonemap_kernel<<<grid, block>>>(d_framebuffer, width, height, time_sec, exposure_gain);

    cudaFree(d_bright);
    cudaFree(d_temp);
    cudaFree(d_bloom_accum);

    return 0;
}

} /* extern "C" */
