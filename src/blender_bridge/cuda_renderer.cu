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
#include <array>
#include <cmath>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <string>

#include "../cuda/kernel_launch.h"
#include "stb_image.h"

namespace {

int env_flag(const char *name, int fallback) {
    if (const char *raw = std::getenv(name)) {
        if (*raw == '\0') {
            return fallback;
        }
        if (std::strcmp(raw, "0") == 0 || std::strcmp(raw, "false") == 0 ||
            std::strcmp(raw, "FALSE") == 0 || std::strcmp(raw, "off") == 0 ||
            std::strcmp(raw, "OFF") == 0) {
            return 0;
        }
        return 1;
    }
    return fallback;
}

float env_float(const char *name, float fallback) {
    if (const char *raw = std::getenv(name)) {
        if (*raw == '\0') {
            return fallback;
        }
        char *end = nullptr;
        float const value = std::strtof(raw, &end);
        if (end != raw) {
            return value;
        }
    }
    return fallback;
}

int env_int(const char *name, int fallback) {
    if (const char *raw = std::getenv(name)) {
        if (*raw == '\0') {
            return fallback;
        }
        char *end = nullptr;
        long const value = std::strtol(raw, &end, 10);
        if (end != raw) {
            return static_cast<int>(value);
        }
    }
    return fallback;
}

struct BridgeBackgroundState {
    cudaArray_t layered_array = nullptr;
    cudaTextureObject_t texture = 0;
    std::string loaded_dir;
};

BridgeBackgroundState &bridge_background_state() {
    static BridgeBackgroundState state;
    return state;
}

void release_bridge_background(BridgeBackgroundState &state) {
    if (state.texture != 0) {
        (void)cudaDestroyTextureObject(state.texture);
        state.texture = 0;
    }
    if (state.layered_array != nullptr) {
        (void)cudaFreeArray(state.layered_array);
        state.layered_array = nullptr;
    }
    state.loaded_dir.clear();
}

std::filesystem::path resolve_bridge_skybox_dir() {
    if (const char *explicit_dir = std::getenv("BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR")) {
        if (*explicit_dir != '\0') {
            return std::filesystem::path(explicit_dir);
        }
    }

    if (const char *source_dir = std::getenv("BLACKHOLE_SOURCE_DIR")) {
        if (*source_dir != '\0') {
            return std::filesystem::path(source_dir) / "assets" / "skybox_eso_milkyway";
        }
    }

    if (const char *showcase_dir = std::getenv("BLACKHOLE_SHOWCASE_SOURCE_DIR")) {
        if (*showcase_dir != '\0') {
            return std::filesystem::path(showcase_dir) / "assets" / "skybox_eso_milkyway";
        }
    }

    return {};
}

int ensure_bridge_background_loaded() {
    BridgeBackgroundState &state = bridge_background_state();
    std::filesystem::path const skybox_dir = resolve_bridge_skybox_dir();
    if (skybox_dir.empty()) {
        release_bridge_background(state);
        return 0;
    }

    std::string const canonical_dir = skybox_dir.lexically_normal().string();
    if (state.texture != 0 && state.loaded_dir == canonical_dir) {
        return 0;
    }

    release_bridge_background(state);

    static const char *kFaces[6] = {"right.png", "left.png", "top.png",
                                    "bottom.png", "front.png", "back.png"};

    int width = 0;
    int height = 0;
    cudaChannelFormatDesc const desc = cudaCreateChannelDesc<uchar4>();
    cudaExtent const extent = make_cudaExtent(0, 0, 6);
    (void)extent;

    std::array<unsigned char *, 6> face_pixels = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};

    for (int face = 0; face < 6; ++face) {
        int face_width = 0;
        int face_height = 0;
        int components = 0;
        std::filesystem::path const face_path = skybox_dir / kFaces[face];
        face_pixels[face] = stbi_load(face_path.string().c_str(), &face_width, &face_height, &components, 4);
        if (face_pixels[face] == nullptr) {
            std::fprintf(stderr, "[cuda_renderer] Failed to load skybox face: %s\n",
                         face_path.string().c_str());
            for (unsigned char *pixels : face_pixels) {
                if (pixels != nullptr) {
                    stbi_image_free(pixels);
                }
            }
            return -1;
        }
        if (face == 0) {
            width = face_width;
            height = face_height;
        } else if (face_width != width || face_height != height) {
            std::fprintf(stderr,
                         "[cuda_renderer] Skybox face dimensions do not match in %s\n",
                         skybox_dir.string().c_str());
            for (unsigned char *pixels : face_pixels) {
                if (pixels != nullptr) {
                    stbi_image_free(pixels);
                }
            }
            return -1;
        }
    }

    cudaExtent const layered_extent = make_cudaExtent(
        static_cast<size_t>(width),
        static_cast<size_t>(height),
        6);
    cudaError_t err = cudaMalloc3DArray(&state.layered_array, &desc, layered_extent, cudaArrayLayered);
    if (err != cudaSuccess) {
        std::fprintf(stderr, "[cuda_renderer] cudaMalloc3DArray skybox failed: %s\n",
                     cudaGetErrorString(err));
        for (unsigned char *pixels : face_pixels) {
            stbi_image_free(pixels);
        }
        release_bridge_background(state);
        return -1;
    }

    for (int face = 0; face < 6; ++face) {
        cudaMemcpy3DParms parms = {};
        parms.srcPtr = make_cudaPitchedPtr(
            face_pixels[face],
            static_cast<size_t>(width) * 4U * sizeof(unsigned char),
            static_cast<size_t>(width),
            static_cast<size_t>(height));
        parms.dstArray = state.layered_array;
        parms.dstPos = make_cudaPos(0, 0, static_cast<size_t>(face));
        parms.extent = make_cudaExtent(
            static_cast<size_t>(width),
            static_cast<size_t>(height),
            1);
        parms.kind = cudaMemcpyHostToDevice;
        err = cudaMemcpy3D(&parms);
        stbi_image_free(face_pixels[face]);
        face_pixels[face] = nullptr;
        if (err != cudaSuccess) {
            std::fprintf(stderr, "[cuda_renderer] cudaMemcpy3D skybox face failed: %s\n",
                         cudaGetErrorString(err));
            release_bridge_background(state);
            return -1;
        }
    }

    cudaResourceDesc res_desc = {};
    res_desc.resType = cudaResourceTypeArray;
    res_desc.res.array.array = state.layered_array;

    cudaTextureDesc tex_desc = {};
    tex_desc.addressMode[0] = cudaAddressModeClamp;
    tex_desc.addressMode[1] = cudaAddressModeClamp;
    tex_desc.filterMode = cudaFilterModeLinear;
    tex_desc.readMode = cudaReadModeNormalizedFloat;
    tex_desc.normalizedCoords = 1;

    err = cudaCreateTextureObject(&state.texture, &res_desc, &tex_desc, nullptr);
    if (err != cudaSuccess) {
        std::fprintf(stderr, "[cuda_renderer] cudaCreateTextureObject skybox failed: %s\n",
                     cudaGetErrorString(err));
        release_bridge_background(state);
        return -1;
    }

    state.loaded_dir = canonical_dir;
    return 0;
}

} // namespace

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
                        float spin, float observer_r, float inclination_rad, float fov_scale,
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
    p->step_size = env_float("BLACKHOLE_BRIDGE_STEP_SIZE", 0.08f);
    p->fov_scale = fmaxf(fov_scale, 0.05f);
    p->max_dist = env_float("BLACKHOLE_BRIDGE_MAX_DIST", 500.0f);
    p->max_steps = env_int("BLACKHOLE_BRIDGE_MAX_STEPS", 600);
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
    p->adisk_enabled = env_flag("BLACKHOLE_BRIDGE_ADISK_ENABLED", 1);
    p->redshift_enabled = env_flag("BLACKHOLE_BRIDGE_REDSHIFT_ENABLED", 1);
    p->kerr_enabled = (fabsf(spin) > 1e-6f) ? 1 : 0;
    p->use_luts = 0;
    p->time_sec = 0.0f;
    p->doppler_strength = env_float("BLACKHOLE_BRIDGE_DOPPLER_STRENGTH", 1.0f);
    p->background_intensity = env_float("BLACKHOLE_BRIDGE_BACKGROUND_INTENSITY", 0.8f);
    p->background_enabled = env_flag("BLACKHOLE_BRIDGE_BACKGROUND_ENABLED", 1);
    p->photon_glow_strength = env_float("BLACKHOLE_BRIDGE_PHOTON_GLOW_STRENGTH", 1.0f);
    p->adisk_lit = env_float("BLACKHOLE_BRIDGE_ADISK_LIT", 0.35f);
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
int bhb_cuda_render_raytraced_camera(
    float spin, float observer_r, float inclination_rad, float fov_scale,
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
    fill_params(&params, spin, observer_r, inclination_rad, fov_scale, width, height);

    unsigned long long galaxy_texture = 0ULL;
    if (ensure_bridge_background_loaded() == 0) {
        galaxy_texture = static_cast<unsigned long long>(bridge_background_state().texture);
    }
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, galaxy_texture, 0ULL, 0ULL, 0ULL);

    /* Bridge renders prioritize visual correctness over benchmark throughput.
     * The aggressive FP16/ILP variants are still valuable in the desktop app,
     * but the Blender bridge should start from the conservative baseline so the
     * addon does not surface architecture-specific striping artifacts. */
    int variant = BH_KERNEL_FP32_BASELINE;

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

    /* Apply restrained post-processing for the bridge path.
     * WHY: the addon/render-engine lane should stay diagnostic and stable, not
     * inherit every cinematic embellishment from the interactive desktop app. */
    extern int bhb_cuda_postprocess(float4*, int, int, float, float, float, float);
    float const bloom_threshold = env_float("BLACKHOLE_BRIDGE_BLOOM_THRESHOLD", 1.0f);
    float const bloom_strength = env_float("BLACKHOLE_BRIDGE_BLOOM_STRENGTH", 0.0f);
    float const exposure_gain = env_float("BLACKHOLE_BRIDGE_EXPOSURE", 12.0f);
    bhb_cuda_postprocess(d_framebuffer, width, height,
                          bloom_threshold,
                          bloom_strength,
                          exposure_gain,
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

int bhb_cuda_render_raytraced(
    float spin, float observer_r, float inclination_rad,
    int width, int height,
    float *out_rgba)
{
    return bhb_cuda_render_raytraced_camera(
        spin,
        observer_r,
        inclination_rad,
        1.0f,
        width,
        height,
        out_rgba);
}

} /* extern "C" */

/* ========================================================================
 * Lensing map kernel: per-pixel equatorial Kerr geodesic -> (redshift, Doppler, hit, 1)
 * ======================================================================== */

/*
 * WHY: The lensing map is a diagnostic texture used by the Blender addon to
 *      modulate surface shading: R channel = gravitational redshift factor,
 *      G channel = Doppler beaming factor, B channel = disk hit flag.
 *      Running this on the GPU is ~100x faster than the CPU path for HD images.
 *
 * Units: all inputs in r_g = M units (same as bhbRenderLensingMap CPU version).
 */

/** @brief Equatorial Kerr geodesic state: (r, phi, p_r). */
struct BhbKerrState2D {
    float r;
    float phi;
    float pr;
};

/** @brief Evaluate equatorial Kerr null geodesic derivatives. */
static __device__ void bhb_eq_deriv(float a, float b_imp,
                                     BhbKerrState2D s, BhbKerrState2D &ds) {
    float const r2    = s.r * s.r;
    float const delta = r2 - (2.0f * s.r) + (a * a);
    /* sigma = r^2 for equatorial plane (theta = pi/2) */
    float const p = r2 + (a * a) - (a * b_imp);

    ds.r   = s.pr * delta / r2;
    ds.phi = ((a * p / delta) - a + b_imp) / r2;
    ds.pr  = -(
        (s.r * s.pr * s.pr * ((2.0f * s.r) - 2.0f) / (2.0f * r2))
        - ((((2.0f * s.r * p) - (((2.0f * s.r) - 2.0f) * (p * p / delta))) / (r2 * delta)))
        + (2.0f * s.r * s.pr * s.pr / r2));
}

/** @brief Single RK4 step of equatorial Kerr null geodesic. */
static __device__ void bhb_eq_step(float a, float b_imp, BhbKerrState2D &s, float h) {
    BhbKerrState2D k1{}, k2{}, k3{}, k4{}, tmp{};

    bhb_eq_deriv(a, b_imp, s, k1);

    tmp = {s.r + 0.5f * h * k1.r,  s.phi + 0.5f * h * k1.phi,  s.pr + 0.5f * h * k1.pr};
    bhb_eq_deriv(a, b_imp, tmp, k2);

    tmp = {s.r + 0.5f * h * k2.r,  s.phi + 0.5f * h * k2.phi,  s.pr + 0.5f * h * k2.pr};
    bhb_eq_deriv(a, b_imp, tmp, k3);

    tmp = {s.r + h * k3.r,  s.phi + h * k3.phi,  s.pr + h * k3.pr};
    bhb_eq_deriv(a, b_imp, tmp, k4);

    s.r   += h * (k1.r   + (2.0f * k2.r)   + (2.0f * k3.r)   + k4.r)   / 6.0f;
    s.phi += h * (k1.phi + (2.0f * k2.phi) + (2.0f * k3.phi) + k4.phi) / 6.0f;
    s.pr  += h * (k1.pr  + (2.0f * k2.pr)  + (2.0f * k3.pr)  + k4.pr)  / 6.0f;
}

/**
 * @brief GPU lensing map kernel.
 *
 * Each thread handles one pixel.  Traces a simplified 2D equatorial Kerr
 * null geodesic and records per-pixel (redshift, Doppler, diskHit, 1.0).
 *
 * @param out        Output buffer: width * height * 4 floats (RGBA).
 * @param width      Image width.
 * @param height     Image height.
 * @param a_star     Dimensionless spin.
 * @param obs_r      Observer radial coordinate [r_g].
 * @param inc_rad    Observer inclination from spin axis [rad].
 * @param r_isco     Prograde ISCO radius [r_g].
 * @param r_horizon  Outer horizon radius [r_g].
 */
__global__ void bhb_lensing_map_kernel(float * __restrict__ out,
                                        int width, int height,
                                        float a_star, float obs_r, float inc_rad,
                                        float r_isco, float r_horizon) {
    int const px = blockIdx.x * blockDim.x + threadIdx.x;
    int const py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= width || py >= height) return;

    /* Image-plane coordinates in r_g units (30 r_g total extent, matches CPU) */
    constexpr float kFov = 30.0f;
    float const alpha = kFov * ((float(px) / float(width))  - 0.5f);
    float const beta  = kFov * (0.5f - (float(py) / float(height)));
    float const b     = fmaxf(sqrtf((alpha * alpha) + (beta * beta)), 1e-5f);

    /* Initial state: observer at r=obs_r, radially infalling */
    BhbKerrState2D state{obs_r, 0.0f, -sqrtf(fmaxf(0.0f, 1.0f - (b / obs_r) * (b / obs_r)))};

    constexpr float kStep = 0.05f;
    int   hitDisk = 0;
    float finalR  = obs_r;

    for (int step = 0; step < 2000; ++step) {
        bhb_eq_step(a_star, b, state, kStep);
        if (state.r < r_horizon * 1.01f) {
            finalR = 0.0f;
            break;
        }
        if (state.r > obs_r * 3.0f) {
            finalR = state.r;
            break;
        }
        if (state.r > r_isco && state.r < 100.0f) {
            hitDisk = 1;
        }
        finalR = state.r;
    }

    /* Gravitational redshift: sqrt(1 - 2M/r) in M units (r_g=M) */
    float const redshift = (finalR > 2.0f) ? sqrtf(1.0f - (2.0f / finalR)) : 0.0f;

    float doppler = 1.0f;
    if ((hitDisk != 0) && finalR > 3.0f) {
        float const vOrb     = 1.0f / sqrtf(finalR);
        float const cosTheta = cosf(state.phi) * sinf(inc_rad);
        float const gamma_v  = 1.0f / sqrtf(fmaxf(1e-10f, 1.0f - (vOrb * vOrb)));
        doppler = 1.0f / (gamma_v * (1.0f - (vOrb * cosTheta)));
    }

    int const pi = (py * width + px) * 4;
    out[pi + 0] = redshift;
    out[pi + 1] = doppler;
    out[pi + 2] = float(hitDisk);
    out[pi + 3] = 1.0f;
}

/* ========================================================================
 * Disk texture kernel: analytical NT temperature + Doppler modulation
 * ======================================================================== */

/**
 * @brief GPU disk texture kernel.
 *
 * Analytically computes the Novikov-Thorne temperature profile and azimuthal
 * Doppler modulation.  No geodesic tracing -- purely algebraic per pixel.
 *
 * @param out       Output: width * height * 4 floats.
 * @param width     Image width (u direction, maps to azimuthal angle phi).
 * @param height    Image height (v direction, maps to r_isco..r_out).
 * @param r_isco    Prograde ISCO [r_g].
 * @param r_out     Outer disk edge [r_g].
 * @param inc_rad   Observer inclination [rad].
 */
__global__ void bhb_disk_texture_kernel(float * __restrict__ out,
                                         int width, int height,
                                         float r_isco, float r_out, float inc_rad) {
    int const px = blockIdx.x * blockDim.x + threadIdx.x;
    int const py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= width || py >= height) return;

    float const v    = float(py) / float(height);
    float const u    = float(px) / float(width);
    float const r_rg = r_isco + (r_out - r_isco) * v;

    /* Novikov-Thorne radiated flux shape: F ~ (1 - sqrt(r_isco/r)) / r^3.
     * T^4 ~ F, so T ~ F^0.25.  Normalize against peak T near r ~ 1.5 * r_isco. */
    float tNorm = 0.0f;
    if (r_rg > r_isco * 1.0001f) {
        float const sqrt_ratio = sqrtf(r_isco / r_rg);
        float const flux = (1.0f - sqrt_ratio) / (r_rg * r_rg * r_rg);
        /* Normalization: peak flux at r = (3/2) * r_isco */
        float const r_pk          = 1.5f * r_isco;
        float const sqrt_ratio_pk = sqrtf(r_isco / r_pk);
        float const flux_pk       = (1.0f - sqrt_ratio_pk) / (r_pk * r_pk * r_pk);
        tNorm = (flux_pk > 1e-20f)
                    ? fminf(1.0f, sqrtf(sqrtf(flux / flux_pk)))
                    : 0.0f;
    }

    /* Simplified blackbody color mapping (hot = blue-white, cool = red-orange) */
    float const cr = fminf(1.0f, tNorm * 2.0f);
    float const cg = fminf(1.0f, fmaxf(0.0f, (tNorm * 3.0f) - 0.5f));
    float const cb = fminf(1.0f, fmaxf(0.0f, (tNorm * 4.0f) - 1.5f));

    /* Azimuthal Doppler modulation */
    float const phi        = u * 6.28318530718f;
    float const vOrb       = (r_rg > 3.0f) ? 1.0f / sqrtf(r_rg) : 0.0f;
    float const dopplerMod = 1.0f + (0.5f * vOrb * sinf(phi) * sinf(inc_rad));

    int const pi = (py * width + px) * 4;
    out[pi + 0] = fminf(2.0f, cr * dopplerMod);  /* clamp to avoid NaN from high Doppler */
    out[pi + 1] = fminf(2.0f, cg * dopplerMod);
    out[pi + 2] = fminf(2.0f, cb * dopplerMod);
    out[pi + 3] = tNorm;
}

/* ========================================================================
 * Host-side wrappers (called from blender_bridge.cpp)
 * ======================================================================== */

extern "C" {

/**
 * @brief GPU lensing map renderer.
 *
 * @param a_star     Dimensionless spin.
 * @param obs_r      Observer radius [r_g = M units].
 * @param inc_rad    Observer inclination [rad].
 * @param width      Image width in pixels.
 * @param height     Image height in pixels.
 * @param out_rgba   Caller-allocated host buffer: width * height * 4 floats.
 * @return 0 on success, -1 on CUDA error or invalid args.
 */
int bhb_cuda_render_lensing_map(float a_star, float obs_r, float inc_rad,
                                 int width, int height, float *out_rgba) {
    if (!out_rgba || width <= 0 || height <= 0) { return -1; }

    size_t const fb_bytes = static_cast<size_t>(width) * height * 4 * sizeof(float);
    float *d_out = nullptr;
    if (cudaMalloc(&d_out, fb_bytes) != cudaSuccess) { return -1; }

    /* Kerr horizon and ISCO in r_g = M units */
    float const r_horizon = 1.0f + sqrtf(fmaxf(0.0f, 1.0f - a_star * a_star));

    /* Prograde ISCO (Bardeen 1972 formula) */
    float const z1 = 1.0f + powf(1.0f - a_star * a_star, 1.0f / 3.0f)
                              * (powf(1.0f + a_star, 1.0f / 3.0f)
                                 + powf(1.0f - a_star, 1.0f / 3.0f));
    float const z2     = sqrtf(3.0f * a_star * a_star + z1 * z1);
    float const r_isco = 3.0f + z2 - sqrtf((3.0f - z1) * (3.0f + z1 + 2.0f * z2));

    dim3 const block(16, 16);
    dim3 const grid((width + 15) / 16, (height + 15) / 16);
    bhb_lensing_map_kernel<<<grid, block>>>(d_out, width, height,
                                             a_star, obs_r, inc_rad,
                                             r_isco, r_horizon);

    cudaError_t err = cudaDeviceSynchronize();
    if (err != cudaSuccess) {
        cudaFree(d_out);
        return -1;
    }

    err = cudaMemcpy(out_rgba, d_out, fb_bytes, cudaMemcpyDeviceToHost);
    cudaFree(d_out);
    return (err == cudaSuccess) ? 0 : -1;
}

/**
 * @brief GPU disk texture renderer.
 *
 * @param a_star    Dimensionless spin (used to compute ISCO).
 * @param r_out_rg  Outer disk radius [r_g].
 * @param inc_rad   Observer inclination [rad].
 * @param width     Image width.
 * @param height    Image height.
 * @param out_rgba  Caller-allocated host buffer: width * height * 4 floats.
 * @return 0 on success, -1 on CUDA error or invalid args.
 */
int bhb_cuda_render_disk_texture(float a_star, float r_out_rg, float inc_rad,
                                  int width, int height, float *out_rgba) {
    if (!out_rgba || width <= 0 || height <= 0) { return -1; }

    size_t const fb_bytes = static_cast<size_t>(width) * height * 4 * sizeof(float);
    float *d_out = nullptr;
    if (cudaMalloc(&d_out, fb_bytes) != cudaSuccess) { return -1; }

    /* Prograde ISCO in r_g units */
    float const z1 = 1.0f + powf(1.0f - a_star * a_star, 1.0f / 3.0f)
                              * (powf(1.0f + a_star, 1.0f / 3.0f)
                                 + powf(1.0f - a_star, 1.0f / 3.0f));
    float const z2     = sqrtf(3.0f * a_star * a_star + z1 * z1);
    float const r_isco = 3.0f + z2 - sqrtf((3.0f - z1) * (3.0f + z1 + 2.0f * z2));

    dim3 const block(16, 16);
    dim3 const grid((width + 15) / 16, (height + 15) / 16);
    bhb_disk_texture_kernel<<<grid, block>>>(d_out, width, height,
                                              r_isco, r_out_rg, inc_rad);

    cudaError_t err = cudaDeviceSynchronize();
    if (err != cudaSuccess) {
        cudaFree(d_out);
        return -1;
    }

    err = cudaMemcpy(out_rgba, d_out, fb_bytes, cudaMemcpyDeviceToHost);
    cudaFree(d_out);
    return (err == cudaSuccess) ? 0 : -1;
}

int bhb_cuda_reset_device_impl(void) {
    cudaError_t err = cudaDeviceSynchronize();
    if (err != cudaSuccess) {
        cudaGetLastError();
    }
    err = cudaDeviceReset();
    if (err != cudaSuccess) {
        fprintf(stderr, "[cuda_renderer] cudaDeviceReset failed: %s\n", cudaGetErrorString(err));
        return -1;
    }
    return 0;
}

} /* extern "C" (lensing map + disk texture wrappers) */
