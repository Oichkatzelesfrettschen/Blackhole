/**
 * @file cuda_renderer.cu
 * @brief Standalone CUDA renderer for the Blender bridge.
 *
 * WHY: Render physically-correct black hole images (with actual Kerr geodesic
 *      ray tracing, photon ring, disk warping, Doppler beaming) to a host
 *      buffer that Blender can consume as a texture.
 * WHAT: Allocates a CUDA framebuffer, calls bh_launch_geodesic_kernel, copies
 *       the result back to host memory.
 * HOW: Called from blender_bridge.cpp when CUDA is available.
 */

#include <cuda_runtime.h>
#include <cstring>
#include <cstdio>
#include <cmath>

#include "../cuda/kernel_launch.h"

/**
 * @brief Populate a BH_LaunchParams struct for the geodesic kernel, matching main.cpp conventions.
 *
 * Sets rs = 1.0 (Schwarzschild radius in internal units), computes the ISCO,
 * and builds the camera position and orthonormal basis from @p observer_r and
 * @p inclination_rad. Feature flags are set for disk + redshift rendering.
 *
 * @param p              Output params struct (zeroed on entry).
 * @param spin           Dimensionless spin a*.
 * @param observer_r     Observer distance [r_s].
 * @param inclination_rad Observer inclination from spin axis [rad].
 * @param width          Framebuffer width in pixels.
 * @param height         Framebuffer height in pixels.
 */
static void fill_params(struct BH_LaunchParams *p,
                        float spin, float observer_r, float inclination_rad,
                        int width, int height) {
    memset(p, 0, sizeof(*p));

    /* The renderer uses rs=1.0 internally (schwarzschildRadius=1.0 in main.cpp).
     * All distances are in units of r_s. observer_r is already in r_s units. */
    float rs = 1.0f;

    /* ISCO in units of r_s (not M). r_s = 2M, so ISCO_M * M = ISCO_M * rs/2. */
    float a = spin;
    float z1 = 1.0f + powf(1.0f - a * a, 1.0f / 3.0f) *
               (powf(1.0f + a, 1.0f / 3.0f) + powf(1.0f - a, 1.0f / 3.0f));
    float z2 = sqrtf(3.0f * a * a + z1 * z1);
    float isco_M = 3.0f + z2 - sqrtf((3.0f - z1) * (3.0f + z1 + 2.0f * z2));
    float isco_rs = isco_M * 0.5f;  /* convert from M to r_s units */

    p->rs = rs;
    p->spin = spin;
    p->isco = isco_rs;
    p->step_size = 0.15f;      /* matches main.cpp default interopStepSize */
    p->fov_scale = 1.0f;       /* matches main.cpp: full NDC range */
    p->max_dist = 100.0f;      /* depthFar from main.cpp */
    p->max_steps = 300;        /* reasonable quality/speed tradeoff */
    p->width = width;
    p->height = height;

    /* Camera: orbit at observer_r, tilted by inclination.
     * Matches cameraPositionFromYawPitch in main.cpp:
     *   x = r * cos(pitch) * sin(yaw)
     *   y = r * sin(pitch)
     *   z = r * cos(pitch) * cos(yaw)
     * For our purposes: yaw=0, pitch=inclination, camera looks at origin. */
    float ci = cosf(inclination_rad);
    float si = sinf(inclination_rad);

    /* Camera position */
    p->cam_pos[0] = 0.0f;
    p->cam_pos[1] = observer_r * si;   /* up by inclination */
    p->cam_pos[2] = observer_r * ci;   /* forward */

    /* Camera basis (column-major mat3, matching glm):
     * forward = normalize(target - cam_pos) = normalize(-cam_pos)
     * right = normalize(cross(forward, world_up))
     * up = cross(right, forward) */
    float fx = 0.0f, fy = -si, fz = -ci;  /* forward = -normalized(cam_pos) */
    /* world_up = (0, 1, 0) when looking from above, but we need the
     * BH spin axis as up. For the standard view: world_up = (0, 1, 0). */
    /* right = cross(forward, (0,1,0)) = (fz, 0, -fx) normalized */
    float rx = -ci, ry = 0.0f, rz = 0.0f;
    /* Hmm, that gives right=(−ci, 0, 0) which isn't right for all angles.
     * Use proper cross product: */
    float wu_x = 0.0f, wu_y = 1.0f, wu_z = 0.0f;
    rx = fy * wu_z - fz * wu_y;  /* = -si*0 - (-ci)*1 = ci */
    ry = fz * wu_x - fx * wu_z;  /* = (-ci)*0 - 0*0 = 0 */
    rz = fx * wu_y - fy * wu_x;  /* = 0*1 - (-si)*0 = 0 */
    float rlen = sqrtf(rx*rx + ry*ry + rz*rz);
    if (rlen < 1e-6f) { rx = 1.0f; ry = 0.0f; rz = 0.0f; rlen = 1.0f; }
    rx /= rlen; ry /= rlen; rz /= rlen;

    /* up = cross(right, forward) */
    float ux = ry * fz - rz * fy;
    float uy = rz * fx - rx * fz;
    float uz = rx * fy - ry * fx;

    /* Column-major: col0=right, col1=up, col2=forward */
    p->cam_basis[0] = rx; p->cam_basis[1] = ry; p->cam_basis[2] = rz;
    p->cam_basis[3] = ux; p->cam_basis[4] = uy; p->cam_basis[5] = uz;
    p->cam_basis[6] = fx; p->cam_basis[7] = fy; p->cam_basis[8] = fz;

    /* Feature flags */
    p->adisk_enabled = 1;
    p->redshift_enabled = 1;
    p->kerr_enabled = (fabsf(spin) > 1e-6f) ? 1 : 0;
    p->use_luts = 0;
    p->time_sec = 0.0f;
    p->doppler_strength = 1.0f;
    p->background_intensity = 0.0f;
    p->background_enabled = 0;
}

extern "C" {

/**
 * @brief Render a physically correct black hole image on the CUDA device.
 *
 * Allocates a device float4 framebuffer, runs bh_launch_geodesic_kernel with
 * the best available variant, applies bhb_cuda_postprocess() (bloom + ACES
 * tonemap + chromatic aberration + vignette + film grain), then copies the
 * result to @p out_rgba.
 *
 * @param spin            Dimensionless spin a*.
 * @param observer_r      Observer distance [r_s].
 * @param inclination_rad Observer inclination [rad].
 * @param width           Image width in pixels.
 * @param height          Image height in pixels.
 * @param out_rgba        Caller-allocated host buffer: width * height * 4 floats.
 * @return 0 on success, -1 on any CUDA error or invalid arguments.
 */
int bhb_cuda_render_raytraced(
    float spin, float observer_r, float inclination_rad,
    int width, int height,
    float *out_rgba)
{
    if (!out_rgba || width <= 0 || height <= 0) return -1;

    /* Allocate device framebuffer */
    float4 *d_framebuffer = nullptr;
    size_t fb_size = (size_t)width * height * sizeof(float4);

    cudaError_t err = cudaMalloc(&d_framebuffer, fb_size);
    if (err != cudaSuccess) {
        fprintf(stderr, "[cuda_renderer] cudaMalloc failed: %s\n", cudaGetErrorString(err));
        return -1;
    }

    /* Clear to black */
    cudaMemset(d_framebuffer, 0, fb_size);

    /* Fill launch params */
    struct BH_LaunchParams params;
    fill_params(&params, spin, observer_r, inclination_rad, width, height);

    /* Select best kernel variant */
    int variant = bh_select_kernel_variant();

    /* Launch */
    int ret = bh_launch_geodesic_kernel(d_framebuffer, &params, variant, nullptr);
    if (ret != 0) {
        fprintf(stderr, "[cuda_renderer] Kernel launch failed: %d\n", ret);
        cudaFree(d_framebuffer);
        return -1;
    }

    /* Synchronize after geodesic kernel */
    err = cudaDeviceSynchronize();
    if (err != cudaSuccess) {
        fprintf(stderr, "[cuda_renderer] Sync failed: %s\n", cudaGetErrorString(err));
        cudaFree(d_framebuffer);
        return -1;
    }

    /* Apply CUDA post-processing: bloom + ACES tonemap + CA + vignette + grain.
     * This matches the main app's shader/bloom_*.frag + shader/tonemapping.frag. */
    extern int bhb_cuda_postprocess(float4*, int, int, float, float, float, float);
    bhb_cuda_postprocess(d_framebuffer, width, height,
                          0.8f,   /* bloom threshold (matches bloom_brightness_pass.frag) */
                          0.1f,   /* bloom strength (matches bloom_composite.frag) */
                          30.0f,  /* exposure gain (kernel output is dim, ~0.01-1.3 per channel) */
                          params.time_sec);

    cudaDeviceSynchronize();

    /* Copy to host (float4 -> flat float RGBA) */
    err = cudaMemcpy(out_rgba, d_framebuffer, fb_size, cudaMemcpyDeviceToHost);
    cudaFree(d_framebuffer);

    if (err != cudaSuccess) {
        fprintf(stderr, "[cuda_renderer] Memcpy failed: %s\n", cudaGetErrorString(err));
        return -1;
    }

    return 0;
}

} /* extern "C" */
