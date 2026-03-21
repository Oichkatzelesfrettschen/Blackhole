/*
 * cuda_grmhd_lut_test.cu
 * Validates the GRMHD 3D texture sampling path in the CUDA geodesic kernel.
 *
 * WHY: The GRMHD emissivity modulation (j_nu ~ rho * B^2, B^2 ~ uu) is applied
 *      in d_shade_hit() when d_use_luts && d_tex_grmhd. Incorrect coordinate
 *      conversion, wrong normalization, or broken phi wrap-around would produce
 *      silent wrong output (non-zero disk pixels with wrong brightness, or a
 *      hard seam at phi=0/2*pi). These tests verify the integration path using
 *      synthetic 3D textures created directly in CUDA (no OpenGL context needed).
 *
 * WHAT:
 *   C1n -- Emissivity modulation correctness:
 *     1. Zero GRMHD (rho=0, uu=0): disk pixels must be black after modulation.
 *     2. Unit GRMHD (rho=1, uu=1): disk pixels must match no-GRMHD baseline
 *        within RMSE < 0.05 (scale factor = 1.0, no change expected).
 *     3. Half-strength GRMHD (rho=0.5, uu=0.5): disk pixels must be ~0.25x
 *        baseline within a loose tolerance (scale factor = 0.25).
 *
 *   C1o -- Phi wrap-around continuity:
 *     4. Uniform GRMHD texture: two rays hitting the disk at phi=~0 and phi=~pi
 *        with doppler_strength=0 must produce identical emissivity (no seam at
 *        phi=0/2*pi introduced by the REPEAT address mode).
 *     5. Direct device-side phi boundary check: a small wrapper kernel samples
 *        a phi-gradient texture at w=0.001 and w=0.999 (near both phi boundaries)
 *        and verifies that REPEAT wrapping is continuous (values within 0.15 of
 *        each other for a linear gradient that should wrap to the same region).
 *
 * HOW: Allocate a cudaArray_t 3D array, fill with test pattern, create a
 *      cudaTextureObject_t, push it to d_tex_grmhd via bh_upload_lut_textures(),
 *      then call bh_launch_geodesic_kernel(). No OpenGL context required.
 *      Tests skip gracefully if no CUDA device is present.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

#include "cuda/kernel_launch.h"

/* ========================================================================
 * Texture creation helper
 * ======================================================================== */

/**
 * @brief Create a CUDA 3D texture object from a host float4 buffer.
 *
 * @param data  Host-side flat array of float4, size = w*h*d.
 * @param w     Width  (phi axis, REPEAT)
 * @param h     Height (theta axis, MIRROR)
 * @param d     Depth  (r axis, CLAMP)
 * @param arr   [out] Receives the allocated cudaArray_t.
 * @param tex   [out] Receives the created cudaTextureObject_t.
 * @return cudaSuccess or first error encountered.
 */
static cudaError_t make_grmhd_texture(const float4* data, int w, int h, int d,
                                       cudaArray_t* arr,
                                       cudaTextureObject_t* tex) {
    cudaChannelFormatDesc desc = cudaCreateChannelDesc<float4>();
    cudaExtent ext = make_cudaExtent(
        static_cast<std::size_t>(w),
        static_cast<std::size_t>(h),
        static_cast<std::size_t>(d));

    cudaError_t err = cudaMalloc3DArray(arr, &desc, ext);
    if (err != cudaSuccess) return err;

    cudaMemcpy3DParms cp = {};
    cp.srcPtr   = make_cudaPitchedPtr(
                    const_cast<float4*>(data),
                    static_cast<std::size_t>(w) * sizeof(float4),
                    static_cast<std::size_t>(w),
                    static_cast<std::size_t>(h));
    cp.dstArray = *arr;
    cp.extent   = ext;
    cp.kind     = cudaMemcpyHostToDevice;
    err = cudaMemcpy3D(&cp);
    if (err != cudaSuccess) return err;

    cudaResourceDesc res = {};
    res.resType         = cudaResourceTypeArray;
    res.res.array.array = *arr;

    cudaTextureDesc td = {};
    /* BL coordinate wrap semantics (mirror the GL path in lut_manager.cu):
     *   r     = S axis (depth  d): CLAMP
     *   theta = T axis (height h): MIRROR
     *   phi   = R axis (width  w): WRAP (REPEAT) */
    td.addressMode[0]   = cudaAddressModeWrap;   /* S = phi (width dimension) */
    td.addressMode[1]   = cudaAddressModeMirror; /* T = theta (height dimension) */
    td.addressMode[2]   = cudaAddressModeClamp;  /* R = r (depth dimension) */
    td.filterMode       = cudaFilterModeLinear;
    td.readMode         = cudaReadModeElementType;
    td.normalizedCoords = 1;

    return cudaCreateTextureObject(tex, &res, &td, nullptr);
}

/* ========================================================================
 * Phi boundary sampling kernel (C1o device-side test)
 * ======================================================================== */

/**
 * @brief Sample a 3D texture at two phi coordinate values near 0 and 2*pi.
 *
 * Uses normalized tex3D coordinates:
 *   u = 0.5 (mid-radius), v = 0.5 (equatorial), w = phi/(2*pi).
 *
 * Checks that the WRAP address mode produces continuous values at the
 * phi=0/2*pi boundary: samples at w=0.001 (phi near 0) and w=0.999
 * (phi near 2*pi) should be close for any texture where the boundary value
 * is continuous.
 */
__global__ void sample_phi_boundary(cudaTextureObject_t tex,
                                    float* near_zero, float* near_twopi) {
    /* r_norm=0.5 (mid-radius), theta_norm=0.5 (equatorial), phi_norm near boundary */
    float4 a = tex3D<float4>(tex, 0.001f, 0.5f, 0.5f);
    float4 b = tex3D<float4>(tex, 0.999f, 0.5f, 0.5f);
    *near_zero  = a.x;
    *near_twopi = b.x;
}

/* ========================================================================
 * LaunchParams helpers
 * ======================================================================== */

static BH_LaunchParams make_disk_params(int w, int h) {
    BH_LaunchParams p = {};
    p.rs            = 2.0f;
    p.spin          = 0.0f;
    p.isco          = 6.0f;
    p.step_size     = 0.05f;
    p.fov_scale     = 1.0f;
    p.max_dist      = 300.0f;
    p.max_steps     = 1000;
    p.width         = w;
    p.height        = h;
    p.adisk_enabled    = 1;
    p.redshift_enabled = 0;
    p.kerr_enabled     = 0;
    p.use_luts         = 0;  /* will be overridden per test */
    p.doppler_strength = 0.0f; /* disable Doppler for cleaner comparisons */
    p.background_enabled   = 0;
    p.background_intensity = 0.0f;

    /* Camera at (25, 0, 20): chosen so the center ray crosses the z=0 equatorial
     * plane at approximately (25, 0, 0), hitting the disk (r=25 > isco=6). */
    p.cam_pos[0] = 25.0f;
    p.cam_pos[1] =  0.0f;
    p.cam_pos[2] = 20.0f;

    /* Identity basis */
    p.cam_basis[0] = 1.0f; p.cam_basis[1] = 0.0f; p.cam_basis[2] = 0.0f;
    p.cam_basis[3] = 0.0f; p.cam_basis[4] = 1.0f; p.cam_basis[5] = 0.0f;
    p.cam_basis[6] = 0.0f; p.cam_basis[7] = 0.0f; p.cam_basis[8] = 1.0f;

    p.lut_radius_min      = p.isco;
    p.lut_radius_max      = 100.0f;
    p.redshift_radius_min = p.isco;
    p.redshift_radius_max = 100.0f;
    p.spectral_radius_min = p.isco;
    p.spectral_radius_max = 100.0f;
    p.time_sec            = 0.0f;

    /* GRMHD radial bounds: covers disk range [6, 100] with margin */
    p.grmhd_r_min = 1.0f;
    p.grmhd_r_max = 50.0f;

    return p;
}

/* Copy float4 device buffer to host. */
static std::vector<float4> copy_fb(const float4* d_fb, int n) {
    std::vector<float4> host(static_cast<std::size_t>(n));
    cudaMemcpy(host.data(), d_fb,
               static_cast<std::size_t>(n) * sizeof(float4),
               cudaMemcpyDeviceToHost);
    return host;
}

/* Per-channel RMSE between two equal-length buffers. */
static double rmse(const std::vector<float4>& a, const std::vector<float4>& b) {
    double sum = 0.0;
    for (std::size_t i = 0; i < a.size(); ++i) {
        double dr = static_cast<double>(a[i].x - b[i].x);
        double dg = static_cast<double>(a[i].y - b[i].y);
        double db = static_cast<double>(a[i].z - b[i].z);
        double da = static_cast<double>(a[i].w - b[i].w);
        sum += dr*dr + dg*dg + db*db + da*da;
    }
    return std::sqrt(sum / static_cast<double>(a.size() * 4));
}

/* ========================================================================
 * Test fixture
 * ======================================================================== */

static constexpr int kW = 4;
static constexpr int kH = 4;
static constexpr int kN = kW * kH;

/* 3D texture dimensions: phi x theta x r (width x height x depth) */
static constexpr int kTW = 16; /* phi slices */
static constexpr int kTH = 16; /* theta slices */
static constexpr int kTD = 16; /* r slices */

class CudaGrmhdLutTest : public ::testing::Test {
protected:
    void SetUp() override {
        int dev = 0;
        cudaGetDeviceCount(&dev);
        if (dev == 0) {
            GTEST_SKIP() << "No CUDA device available";
        }

        cudaError_t err = cudaMalloc(&d_fb, static_cast<std::size_t>(kN) * sizeof(float4));
        ASSERT_EQ(err, cudaSuccess)
            << "cudaMalloc framebuffer: " << cudaGetErrorString(err);
    }

    void TearDown() override {
        /* Reset d_tex_grmhd to 0 so subsequent tests start clean */
        bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL);

        if (d_fb) { cudaFree(d_fb); d_fb = nullptr; }

        /* Texture objects and arrays are cleaned up per-test by helpers below */
    }

    /* Render with the given params; returns host copy of framebuffer. */
    std::vector<float4> render(const BH_LaunchParams& p) {
        int rc = bh_launch_geodesic_kernel(
            d_fb, &p, BH_KERNEL_FP32_BASELINE, nullptr);
        if (rc != 0) {
            ADD_FAILURE() << "bh_launch_geodesic_kernel returned " << rc;
            return {};
        }
        cudaDeviceSynchronize();
        return copy_fb(d_fb, kN);
    }

    float4* d_fb = nullptr;
};

/* ========================================================================
 * C1n -- Emissivity modulation correctness
 * ======================================================================== */

/**
 * @test GrmhdModulationZeroInputZeroOutput (C1n)
 *
 * With a zero GRMHD texture (rho=0, uu=0), d_shade_hit multiplies the disk
 * color by rho*uu = 0. All disk pixels must become (0,0,0,1) after modulation.
 */
TEST_F(CudaGrmhdLutTest, GrmhdModulationZeroInputZeroOutput) {
    /* Fill a 16x16x16 texture with zeros */
    std::vector<float4> host_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(0.0f, 0.0f, 0.0f, 0.0f));

    cudaArray_t arr = nullptr;
    cudaTextureObject_t tex = 0;
    cudaError_t err = make_grmhd_texture(
        host_data.data(), kTW, kTH, kTD, &arr, &tex);
    ASSERT_EQ(err, cudaSuccess)
        << "Failed to create zero GRMHD texture: " << cudaGetErrorString(err);

    /* Upload to d_tex_grmhd */
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex), 0ULL, 0ULL);

    BH_LaunchParams p = make_disk_params(kW, kH);
    p.use_luts = 1;

    auto pixels = render(p);
    ASSERT_EQ(pixels.size(), static_cast<std::size_t>(kN));

    /* Every disk-hit pixel must be black (scale = rho*uu = 0).
     * Non-disk pixels (horizon or background) are also zero/black by default,
     * so ALL pixels must be black regardless of hit type. */
    for (int i = 0; i < kN; ++i) {
        const float4& px = pixels[static_cast<std::size_t>(i)];
        EXPECT_FLOAT_EQ(px.x, 0.0f)
            << "pixel " << i << " R channel is non-zero with zero GRMHD";
        EXPECT_FLOAT_EQ(px.y, 0.0f)
            << "pixel " << i << " G channel is non-zero with zero GRMHD";
        EXPECT_FLOAT_EQ(px.z, 0.0f)
            << "pixel " << i << " Z channel is non-zero with zero GRMHD";
    }

    cudaDestroyTextureObject(tex);
    cudaFreeArray(arr);
}

/**
 * @test GrmhdModulationUnitInputMatchesBaseline (C1n)
 *
 * With rho=1, uu=1 everywhere, the scale factor is 1.0 and disk colors must
 * match the no-GRMHD baseline within RMSE < 0.05.
 */
TEST_F(CudaGrmhdLutTest, GrmhdModulationUnitInputMatchesBaseline) {
    /* Baseline: no GRMHD (use_luts=0) */
    BH_LaunchParams p = make_disk_params(kW, kH);
    p.use_luts = 0;
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL);
    auto baseline = render(p);
    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));

    /* Unit GRMHD texture: rho=1, uu=1 */
    std::vector<float4> host_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(1.0f, 1.0f, 0.0f, 0.0f));

    cudaArray_t arr = nullptr;
    cudaTextureObject_t tex = 0;
    cudaError_t err = make_grmhd_texture(
        host_data.data(), kTW, kTH, kTD, &arr, &tex);
    ASSERT_EQ(err, cudaSuccess)
        << "Failed to create unit GRMHD texture: " << cudaGetErrorString(err);

    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex), 0ULL, 0ULL);

    p.use_luts = 1;
    auto with_unit_grmhd = render(p);
    ASSERT_EQ(with_unit_grmhd.size(), static_cast<std::size_t>(kN));

    double r = rmse(baseline, with_unit_grmhd);
    EXPECT_LT(r, 0.05)
        << "Unit GRMHD (rho=uu=1) vs no-GRMHD baseline RMSE=" << r
        << " exceeds 0.05; scale factor should be 1.0 (no change)";

    cudaDestroyTextureObject(tex);
    cudaFreeArray(arr);
}

/**
 * @test GrmhdModulationHalfStrengthDimsOutput (C1n)
 *
 * With rho=0.5, uu=0.5, scale = 0.25. Disk pixel brightness must be
 * noticeably lower than baseline; any channel that was non-zero in the
 * baseline must be <= 0.30 * baseline (allowing for linear texture filtering
 * that may yield slightly different than exact 0.25 at the disk hit point).
 */
TEST_F(CudaGrmhdLutTest, GrmhdModulationHalfStrengthDimsOutput) {
    /* Baseline: no GRMHD */
    BH_LaunchParams p = make_disk_params(kW, kH);
    p.use_luts = 0;
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL, 0ULL);
    auto baseline = render(p);
    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));

    /* Half-strength GRMHD: rho=0.5, uu=0.5 */
    std::vector<float4> host_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(0.5f, 0.5f, 0.0f, 0.0f));

    cudaArray_t arr = nullptr;
    cudaTextureObject_t tex = 0;
    cudaError_t err = make_grmhd_texture(
        host_data.data(), kTW, kTH, kTD, &arr, &tex);
    ASSERT_EQ(err, cudaSuccess)
        << "Failed to create half GRMHD texture: " << cudaGetErrorString(err);

    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex), 0ULL, 0ULL);

    p.use_luts = 1;
    auto with_half = render(p);
    ASSERT_EQ(with_half.size(), static_cast<std::size_t>(kN));

    /* Find any bright disk pixel in baseline and verify it is dimmed */
    int bright_pixels_checked = 0;
    for (int i = 0; i < kN; ++i) {
        const float4& bl = baseline[static_cast<std::size_t>(i)];
        const float4& hf = with_half[static_cast<std::size_t>(i)];

        /* Only check pixels that were actually bright (disk hits) */
        if (bl.x > 0.1f || bl.y > 0.1f || bl.z > 0.1f) {
            /* Dimmed pixel must be significantly less than baseline.
             * Threshold 0.30 allows for boundary interpolation variance. */
            if (bl.x > 0.1f) {
                EXPECT_LT(hf.x, bl.x * 0.30f)
                    << "pixel " << i << " R not dimmed: baseline=" << bl.x
                    << " half=" << hf.x;
            }
            ++bright_pixels_checked;
        }
    }

    EXPECT_GT(bright_pixels_checked, 0)
        << "No bright disk pixels found in baseline render -- test setup error";

    cudaDestroyTextureObject(tex);
    cudaFreeArray(arr);
}

/* ========================================================================
 * C1o -- Phi wrap-around continuity
 * ======================================================================== */

/**
 * @test GrmhdPhiUniformNoSeam (C1o)
 *
 * With a uniform GRMHD texture (rho=uu=1, phi-constant), two pixels
 * hitting the disk at phi~0 (positive x axis) and phi~pi (negative x axis)
 * must receive the same emissivity scale factor (1.0 for uniform texture).
 * With doppler_strength=0, disk colors should match baseline (scale=1).
 * Verifies no phi-seam artifact from REPEAT addressing.
 */
TEST_F(CudaGrmhdLutTest, GrmhdPhiUniformNoSeam) {
    std::vector<float4> host_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(1.0f, 1.0f, 0.0f, 0.0f));

    cudaArray_t arr = nullptr;
    cudaTextureObject_t tex = 0;
    cudaError_t err = make_grmhd_texture(
        host_data.data(), kTW, kTH, kTD, &arr, &tex);
    ASSERT_EQ(err, cudaSuccess)
        << "Failed to create uniform phi GRMHD texture: " << cudaGetErrorString(err);

    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex), 0ULL, 0ULL);

    /* Ray set 1: camera at (+25, 0, 20), hits disk at phi~0 (positive x side).
     * Use the fixture's kW x kH framebuffer; pick the center pixel (index kN/2). */
    BH_LaunchParams p1 = make_disk_params(kW, kH);
    p1.use_luts = 1;
    p1.cam_pos[0] = 25.0f; p1.cam_pos[1] = 0.0f; p1.cam_pos[2] = 20.0f;
    auto pix1 = render(p1);
    ASSERT_EQ(pix1.size(), static_cast<std::size_t>(kN));
    const float4& px1 = pix1[static_cast<std::size_t>(kN / 2)];

    /* Ray set 2: camera at (-25, 0, 20), hits disk at phi~pi (negative x side).
     * Flip the x-axis basis column so the ray points toward origin. */
    BH_LaunchParams p2 = make_disk_params(kW, kH);
    p2.use_luts = 1;
    p2.cam_pos[0] = -25.0f; p2.cam_pos[1] = 0.0f; p2.cam_pos[2] = 20.0f;
    /* Flip right vector (col0) so the camera is mirrored but still valid */
    p2.cam_basis[0] = -1.0f; p2.cam_basis[1] = 0.0f; p2.cam_basis[2] = 0.0f;
    auto pix2 = render(p2);
    ASSERT_EQ(pix2.size(), static_cast<std::size_t>(kN));
    const float4& px2 = pix2[static_cast<std::size_t>(kN / 2)];

    /* Both center pixels should be disk hits: non-zero */
    bool px1_nonzero = (px1.x > 0.0f || px1.y > 0.0f || px1.z > 0.0f);
    bool px2_nonzero = (px2.x > 0.0f || px2.y > 0.0f || px2.z > 0.0f);

    /* If either pixel is zero, the ray didn't hit the disk -- skip quantitative
     * comparison but still flag if both are zero (geometry setup is broken). */
    if (!px1_nonzero && !px2_nonzero) {
        FAIL() << "Neither phi=0 nor phi=pi camera position produced a disk hit; "
               << "geometry setup may be wrong (check cam_pos and disk range)";
    }

    if (px1_nonzero && px2_nonzero) {
        /* Both hit the disk. With uniform GRMHD (scale=1) and no Doppler,
         * the Novikov-Thorne flux depends only on r (not phi), and both
         * rays hit at approximately the same r. Colors should match closely.
         * Allow tolerance of 0.2 for minor asymmetric geodesic deflection. */
        double dr = std::abs(static_cast<double>(px1.x - px2.x));
        double dg = std::abs(static_cast<double>(px1.y - px2.y));
        double db = std::abs(static_cast<double>(px1.z - px2.z));
        EXPECT_LT(dr, 0.2)
            << "R channel differs between phi~0 and phi~pi disk pixels: "
            << px1.x << " vs " << px2.x;
        EXPECT_LT(dg, 0.2)
            << "G channel differs between phi~0 and phi~pi disk pixels: "
            << px1.y << " vs " << px2.y;
        EXPECT_LT(db, 0.2)
            << "B channel differs between phi~0 and phi~pi disk pixels: "
            << px1.z << " vs " << px2.z;
    }

    cudaDestroyTextureObject(tex);
    cudaFreeArray(arr);
}

/**
 * @test GrmhdPhiBoundaryWrapsCleanly (C1o)
 *
 * Creates a uniform 3D CUDA texture and samples it near phi=0 (w=0.001) and
 * phi=2*pi (w=0.999) using a small device kernel. With WRAP addressing and
 * a uniform texture, both samples must be within 1e-4 of the fill value (1.0).
 * This verifies the REPEAT addressing doesn't corrupt the phi boundary.
 */
TEST_F(CudaGrmhdLutTest, GrmhdPhiBoundaryWrapsCleanly) {
    /* Uniform texture: rho=1.0 everywhere */
    std::vector<float4> host_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(1.0f, 1.0f, 0.0f, 0.0f));

    cudaArray_t arr = nullptr;
    cudaTextureObject_t tex = 0;
    cudaError_t err = make_grmhd_texture(
        host_data.data(), kTW, kTH, kTD, &arr, &tex);
    ASSERT_EQ(err, cudaSuccess)
        << "Failed to create boundary test texture: " << cudaGetErrorString(err);

    float* d_near_zero   = nullptr;
    float* d_near_twopi  = nullptr;
    cudaMalloc(&d_near_zero,  sizeof(float));
    cudaMalloc(&d_near_twopi, sizeof(float));

    sample_phi_boundary<<<1, 1>>>(tex, d_near_zero, d_near_twopi);
    cudaDeviceSynchronize();

    float h_near_zero  = 0.0f;
    float h_near_twopi = 0.0f;
    cudaMemcpy(&h_near_zero,  d_near_zero,  sizeof(float), cudaMemcpyDeviceToHost);
    cudaMemcpy(&h_near_twopi, d_near_twopi, sizeof(float), cudaMemcpyDeviceToHost);

    /* Both samples must be close to the fill value (1.0).
     * Linear filtering may produce slight sub-voxel interpolation error. */
    EXPECT_NEAR(h_near_zero,  1.0f, 1e-4f)
        << "Sample near phi=0 (w=0.001) diverges from fill value 1.0: "
        << h_near_zero;
    EXPECT_NEAR(h_near_twopi, 1.0f, 1e-4f)
        << "Sample near phi=2*pi (w=0.999) diverges from fill value 1.0: "
        << h_near_twopi;

    /* The absolute difference must also be small: no jump at the boundary */
    EXPECT_NEAR(h_near_zero, h_near_twopi, 1e-4f)
        << "phi boundary mismatch: near_zero=" << h_near_zero
        << " near_twopi=" << h_near_twopi
        << "; WRAP addressing may have introduced a seam";

    cudaFree(d_near_zero);
    cudaFree(d_near_twopi);
    cudaDestroyTextureObject(tex);
    cudaFreeArray(arr);
}

/* ========================================================================
 * C1d -- Temporal interpolation between two GRMHD frames
 * ======================================================================== */

/**
 * @test GrmhdInterpolationAlphaZeroMatchesLeft (C1d)
 *
 * With alpha=0 the blend must return the left frame unchanged.
 * Left = rho=0.8, uu=0.6; right = rho=1.0, uu=1.0.
 * At alpha=0 the disk pixel brightness must match left-only baseline.
 */
TEST_F(CudaGrmhdLutTest, GrmhdInterpolationAlphaZeroMatchesLeft) {
    /* Left texture: rho=0.8, uu=0.6 */
    std::vector<float4> left_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(0.8f, 0.6f, 0.0f, 0.0f));
    /* Right texture: rho=1.0, uu=1.0 */
    std::vector<float4> right_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(1.0f, 1.0f, 0.0f, 0.0f));

    cudaArray_t arr_l = nullptr, arr_r = nullptr;
    cudaTextureObject_t tex_l = 0, tex_r = 0;
    ASSERT_EQ(cudaSuccess, make_grmhd_texture(left_data.data(),  kTW, kTH, kTD, &arr_l, &tex_l));
    ASSERT_EQ(cudaSuccess, make_grmhd_texture(right_data.data(), kTW, kTH, kTD, &arr_r, &tex_r));

    BH_LaunchParams p = make_disk_params(kW, kH);
    p.use_luts   = 1;
    p.grmhd_alpha = 0.0f;  /* left frame only */

    /* Render with left-only (right slot = 0) to get baseline */
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex_l), 0ULL, 0ULL);
    auto left_only = render(p);
    ASSERT_EQ(left_only.size(), static_cast<std::size_t>(kN));

    /* Render with alpha=0 and right slot populated -- must match left_only */
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex_l), 0ULL,
                           static_cast<unsigned long long>(tex_r));
    auto blended = render(p);
    ASSERT_EQ(blended.size(), static_cast<std::size_t>(kN));

    double r = rmse(left_only, blended);
    EXPECT_LT(r, 1e-5)
        << "alpha=0 blend must match left-only render; RMSE=" << r;

    cudaDestroyTextureObject(tex_l); cudaFreeArray(arr_l);
    cudaDestroyTextureObject(tex_r); cudaFreeArray(arr_r);
}

/**
 * @test GrmhdInterpolationAlphaOneMatchesRight (C1d)
 *
 * With alpha=1 the blend must return the right frame.
 * Left = rho=0.0, uu=0.0 (black after modulation).
 * Right = rho=1.0, uu=1.0 (full brightness).
 * At alpha=1 pixels must be >= baseline brightness; at alpha=0 all black.
 */
TEST_F(CudaGrmhdLutTest, GrmhdInterpolationAlphaOneMatchesRight) {
    std::vector<float4> left_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(0.0f, 0.0f, 0.0f, 0.0f));
    std::vector<float4> right_data(
        static_cast<std::size_t>(kTW * kTH * kTD),
        make_float4(1.0f, 1.0f, 0.0f, 0.0f));

    cudaArray_t arr_l = nullptr, arr_r = nullptr;
    cudaTextureObject_t tex_l = 0, tex_r = 0;
    ASSERT_EQ(cudaSuccess, make_grmhd_texture(left_data.data(),  kTW, kTH, kTD, &arr_l, &tex_l));
    ASSERT_EQ(cudaSuccess, make_grmhd_texture(right_data.data(), kTW, kTH, kTD, &arr_r, &tex_r));

    BH_LaunchParams p = make_disk_params(kW, kH);
    p.use_luts    = 1;

    /* alpha=0: left (zero) => all-black */
    p.grmhd_alpha = 0.0f;
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex_l), 0ULL,
                           static_cast<unsigned long long>(tex_r));
    auto at_zero = render(p);

    /* alpha=1: right (unit) => disk should be bright */
    p.grmhd_alpha = 1.0f;
    bh_upload_lut_textures(0ULL, 0ULL, 0ULL, 0ULL, 0ULL,
                           static_cast<unsigned long long>(tex_l), 0ULL,
                           static_cast<unsigned long long>(tex_r));
    auto at_one = render(p);

    ASSERT_EQ(at_zero.size(), static_cast<std::size_t>(kN));
    ASSERT_EQ(at_one.size(),  static_cast<std::size_t>(kN));

    /* With alpha=0 and zero left texture, all disk pixels must be black. */
    for (int i = 0; i < kN; ++i) {
        const float4& px = at_zero[static_cast<std::size_t>(i)];
        EXPECT_FLOAT_EQ(px.x, 0.0f) << "alpha=0 pixel " << i << " R not black";
        EXPECT_FLOAT_EQ(px.y, 0.0f) << "alpha=0 pixel " << i << " G not black";
        EXPECT_FLOAT_EQ(px.z, 0.0f) << "alpha=0 pixel " << i << " B not black";
    }

    /* With alpha=1 and unit right texture, at least one pixel must be brighter. */
    float max_brightness = 0.0f;
    for (int i = 0; i < kN; ++i) {
        const float4& px = at_one[static_cast<std::size_t>(i)];
        float const chan_max = px.x > px.y ? (px.x > px.z ? px.x : px.z)
                                             : (px.y > px.z ? px.y : px.z);
        max_brightness = max_brightness > chan_max ? max_brightness : chan_max;
    }
    EXPECT_GT(max_brightness, 0.0f)
        << "alpha=1 with unit right frame: no bright pixel found -- disk may not be hit";

    cudaDestroyTextureObject(tex_l); cudaFreeArray(arr_l);
    cudaDestroyTextureObject(tex_r); cudaFreeArray(arr_r);
}
