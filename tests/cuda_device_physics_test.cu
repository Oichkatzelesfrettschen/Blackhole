/*
 * cuda_device_physics_test.cu
 * Validates the CUDA geodesic tracing physics via the bh_launch_geodesic_kernel
 * C API.
 *
 * WHY: The device physics functions in device_physics.cuh implement Kerr and
 *      Schwarzschild geodesic integration. Incorrect constant-memory uploads,
 *      wrong RK4 step formulas, or incorrect horizon/disk detection all produce
 *      visual artifacts that are hard to diagnose from the rendered image alone.
 *      These unit tests verify the end-to-end physics path for known scenarios
 *      with analytically predictable outcomes.
 *
 * WHAT: Tests via bh_launch_geodesic_kernel (C API only -- does NOT include
 *       device_physics.cuh to avoid multiply-defined __constant__ symbols):
 *   1. Schwarzschild horizon hit: ray aimed at BH center must produce black pixel.
 *   2. Schwarzschild escape: ray aimed away from BH must produce non-black pixel.
 *   3. Kerr horizon hit: same scenario with spin=0.9 must also produce black pixel.
 *   4. Disk intersection: with adisk_enabled, camera in equatorial plane sees disk.
 *   5. No NaN/Inf: any valid launch must produce finite float4 values everywhere.
 *
 * HOW: Allocate float4 device buffer, call bh_launch_geodesic_kernel, copy to
 *      host, inspect. All tests skip gracefully if no CUDA device is present.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

#include "cuda/kernel_launch.h"

/* ========================================================================
 * Helpers
 * ======================================================================== */

/* Build a minimal valid BH_LaunchParams for Schwarzschild (spin=0). */
static BH_LaunchParams make_schwarzschild_params(int w, int h) {
    BH_LaunchParams p = {};

    p.rs            = 2.0f;     /* Event horizon at r = rs for Schwarzschild */
    p.spin          = 0.0f;
    p.isco          = 6.0f;     /* 3*rs for Schwarzschild */
    p.step_size     = 0.05f;
    p.fov_scale     = 1.0f;
    p.max_dist      = 200.0f;
    p.max_steps     = 1000;
    p.width         = w;
    p.height        = h;
    p.adisk_enabled    = 0;
    p.redshift_enabled = 0;
    p.kerr_enabled     = 0;
    p.use_luts         = 0;

    /* Camera at (0, 0, 10): 5x the event horizon radius */
    p.cam_pos[0] = 0.0f;
    p.cam_pos[1] = 0.0f;
    p.cam_pos[2] = 10.0f;

    /* Identity basis: local (u, v, -1) maps to world (u, v, -1).
     * Column-major storage (matching glm): col0 = right, col1 = up, col2 = fwd.
     *   m[0..2] = col0 = (1, 0, 0)
     *   m[3..5] = col1 = (0, 1, 0)
     *   m[6..8] = col2 = (0, 0, 1)
     * d_mat3_mul: row r, col c -> m[c*3+r]. Identity: m[0]=m[4]=m[8]=1, rest 0.
     */
    p.cam_basis[0] = 1.0f; p.cam_basis[1] = 0.0f; p.cam_basis[2] = 0.0f;
    p.cam_basis[3] = 0.0f; p.cam_basis[4] = 1.0f; p.cam_basis[5] = 0.0f;
    p.cam_basis[6] = 0.0f; p.cam_basis[7] = 0.0f; p.cam_basis[8] = 1.0f;

    p.lut_radius_min      = p.isco;
    p.lut_radius_max      = 100.0f;
    p.redshift_radius_min = p.isco;
    p.redshift_radius_max = 100.0f;
    p.spectral_radius_min = p.isco;
    p.spectral_radius_max = 100.0f;

    p.time_sec             = 0.0f;
    p.doppler_strength     = 1.0f;
    p.background_intensity = 0.1f;
    p.background_enabled   = 0;

    return p;
}

/* Copy float4 device buffer to host vector. */
static std::vector<float4> copy_framebuffer(const float4* d_fb, int n) {
    std::vector<float4> host(static_cast<std::size_t>(n));
    cudaMemcpy(host.data(), d_fb, static_cast<std::size_t>(n) * sizeof(float4),
               cudaMemcpyDeviceToHost);
    return host;
}

/* Check that a pixel is the horizon color (0, 0, 0, 1). */
static bool is_horizon(const float4& px) {
    return px.x == 0.0f && px.y == 0.0f && px.z == 0.0f && px.w == 1.0f;
}

/* Check that a pixel has no NaN or Inf. */
static bool is_finite(const float4& px) {
    return std::isfinite(px.x) && std::isfinite(px.y)
        && std::isfinite(px.z) && std::isfinite(px.w);
}

/* ========================================================================
 * Test fixture: allocates/frees a 1x1 device framebuffer.
 * ======================================================================== */

class CudaDevicePhysicsTest : public ::testing::Test {
protected:
    void SetUp() override {
        int dev_count = 0;
        cudaGetDeviceCount(&dev_count);
        if (dev_count == 0) {
            GTEST_SKIP() << "No CUDA device available";
        }

        cudaError_t err = cudaMalloc(&d_fb_1x1, sizeof(float4));
        ASSERT_EQ(err, cudaSuccess) << "cudaMalloc failed: " << cudaGetErrorString(err);

        err = cudaMalloc(&d_fb_8x8, 64 * sizeof(float4));
        ASSERT_EQ(err, cudaSuccess) << "cudaMalloc 8x8 failed: " << cudaGetErrorString(err);
    }

    void TearDown() override {
        if (d_fb_1x1) { cudaFree(d_fb_1x1); d_fb_1x1 = nullptr; }
        if (d_fb_8x8) { cudaFree(d_fb_8x8); d_fb_8x8 = nullptr; }
    }

    float4* d_fb_1x1 = nullptr;
    float4* d_fb_8x8 = nullptr;
};

/* ========================================================================
 * 1. Schwarzschild horizon hit
 *    A 1x1 framebuffer where the single pixel aims at BH center.
 *    Camera at (0, 0, 10), identity basis, fov_scale=1.0:
 *      pixel (0,0): u=(2*0.5/1-1)*1=0, v=0 => local_dir=(0,0,-1) => world (0,0,-1)
 *    Angular momentum h = cross((0,0,10),(0,0,-1)) = 0 => no deflection.
 *    Ray falls straight to r=0; hits horizon at r <= rs=2.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, SchwarzschildHorizonHit) {
    BH_LaunchParams p = make_schwarzschild_params(1, 1);

    int rc = bh_launch_geodesic_kernel(d_fb_1x1, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "bh_launch_geodesic_kernel returned error " << rc;

    /* Synchronize before reading results */
    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_1x1, 1);
    EXPECT_TRUE(is_finite(host[0])) << "horizon pixel is NaN or Inf";
    EXPECT_TRUE(is_horizon(host[0]))
        << "center ray aimed at BH must hit horizon; got ("
        << host[0].x << ", " << host[0].y << ", "
        << host[0].z << ", " << host[0].w << ")";
}

/* ========================================================================
 * 2. Schwarzschild escape
 *    Camera at (0, 0, 10), ray aimed in +Z direction (away from BH).
 *    We flip the camera basis so that local (0,0,-1) maps to world (0,0,+1).
 *    The ray moves away from BH and should escape (reach max_dist).
 *    Escaped pixels are not the black horizon color.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, SchwarzschildEscape) {
    BH_LaunchParams p = make_schwarzschild_params(1, 1);

    /* Rotate camera to look in +Y direction (away from BH, which is at origin).
     * local (0,0,-1) must map to world (0,1,0), so col2 = (0,-1,0).
     * col0=(1,0,0) right, col1=(0,0,-1) up, col2=(0,-1,0) forward-storage.
     * Column-major m[c*3+r]: col0 -> m[0..2], col1 -> m[3..5], col2 -> m[6..8]. */
    p.cam_basis[0] = 1.0f; p.cam_basis[1] = 0.0f; p.cam_basis[2] = 0.0f;
    p.cam_basis[3] = 0.0f; p.cam_basis[4] = 0.0f; p.cam_basis[5] =-1.0f;
    p.cam_basis[6] = 0.0f; p.cam_basis[7] =-1.0f; p.cam_basis[8] = 0.0f;
    /* Enable background so escaped rays return a gradient color instead of (0,0,0,1)
     * which is indistinguishable from the horizon when background_enabled=0. */
    p.background_enabled = 1;
    /* Ray goes in +Y from (0,0,10): n.y=1 in the sky gradient, so background
     * color = (0.01*intensity, 0.01*intensity, 0.03*intensity) != horizon. */

    int rc = bh_launch_geodesic_kernel(d_fb_1x1, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "bh_launch_geodesic_kernel returned error " << rc;

    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_1x1, 1);
    EXPECT_TRUE(is_finite(host[0])) << "escape pixel is NaN or Inf";
    EXPECT_FALSE(is_horizon(host[0]))
        << "ray aimed away from BH must not hit horizon; got ("
        << host[0].x << ", " << host[0].y << ", "
        << host[0].z << ", " << host[0].w << ")";
}

/* ========================================================================
 * 3. Kerr horizon hit
 *    Same 1x1 center scenario but with spin=0.9.
 *    The Kerr horizon is at r_+ = M + sqrt(M^2 - a^2) < rs.
 *    A ray aimed at BH center still falls in.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, KerrHorizonHit) {
    BH_LaunchParams p = make_schwarzschild_params(1, 1);
    p.spin         = 0.9f;
    p.kerr_enabled = 1;
    /* ISCO for Kerr a=0.9M: approximately 2.32 rs for prograde.
     * Use a conservative value; for this test the exact ISCO does not matter. */
    p.isco = 4.0f;

    int rc = bh_launch_geodesic_kernel(d_fb_1x1, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "Kerr launch returned error " << rc;

    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_1x1, 1);
    EXPECT_TRUE(is_finite(host[0])) << "Kerr horizon pixel is NaN or Inf";
    EXPECT_TRUE(is_horizon(host[0]))
        << "center Kerr ray must hit horizon; got ("
        << host[0].x << ", " << host[0].y << ", "
        << host[0].z << ", " << host[0].w << ")";
}

/* ========================================================================
 * 4. Disk intersection
 *    Camera at (0, 20, 0) (in equatorial plane, +Y axis), looking toward -Y.
 *    Accretion disk sits in the Z=0 plane between ISCO and 100*rs.
 *    The center ray crosses the Z=0 plane and must hit the disk.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, DiskIntersection) {
    BH_LaunchParams p = make_schwarzschild_params(1, 1);
    p.adisk_enabled = 1;
    p.isco          = 6.0f;  /* disk inner radius */

    /* Camera at (25, 0, 20): off-axis and ABOVE the equatorial plane (z=20).
     * Identity basis: local (0,0,-1) -> world (0,0,-1), ray falls straight down.
     * The ray starts at z=20 and crosses z=0 (equatorial plane) at approximately
     * (25, 0, 0), giving disk_r = 25, which is between isco=6 and r_out=20*rs=40.
     * The sign change in z triggers d_check_disk, producing a disk color hit. */
    p.cam_pos[0] = 25.0f;
    p.cam_pos[1] =  0.0f;
    p.cam_pos[2] = 20.0f;
    p.max_dist   = 300.0f;   /* ensure ray travels far enough */
    /* Identity basis (already set by make_schwarzschild_params, reassert clearly): */
    p.cam_basis[0] = 1.0f; p.cam_basis[1] = 0.0f; p.cam_basis[2] = 0.0f;
    p.cam_basis[3] = 0.0f; p.cam_basis[4] = 1.0f; p.cam_basis[5] = 0.0f;
    p.cam_basis[6] = 0.0f; p.cam_basis[7] = 0.0f; p.cam_basis[8] = 1.0f;

    int rc = bh_launch_geodesic_kernel(d_fb_1x1, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "disk test launch returned error " << rc;

    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_1x1, 1);
    EXPECT_TRUE(is_finite(host[0])) << "disk pixel is NaN or Inf";

    /* The disk is hit: pixel should NOT be the horizon color (black) and
     * should NOT be zero (unlit). Disk color has positive luminosity. */
    EXPECT_FALSE(is_horizon(host[0]))
        << "disk-intersection ray must not return pure horizon black";
}

/* ========================================================================
 * 5. No NaN or Inf in any pixel for a standard 8x8 scene
 *    Tests the full framebuffer with typical rendering parameters.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, NoNaNInFramebuffer) {
    BH_LaunchParams p = make_schwarzschild_params(8, 8);

    int rc = bh_launch_geodesic_kernel(d_fb_8x8, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "8x8 launch returned error " << rc;

    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_8x8, 64);
    for (int i = 0; i < 64; ++i) {
        EXPECT_TRUE(is_finite(host[static_cast<std::size_t>(i)]))
            << "pixel " << i << " has NaN or Inf: ("
            << host[static_cast<std::size_t>(i)].x << ", "
            << host[static_cast<std::size_t>(i)].y << ", "
            << host[static_cast<std::size_t>(i)].z << ", "
            << host[static_cast<std::size_t>(i)].w << ")";
    }
}

/* ========================================================================
 * 6. Alpha channel is always 1.0
 *    d_shade_hit always sets w=1.0 for all outcomes.
 * ======================================================================== */

TEST_F(CudaDevicePhysicsTest, AlphaAlwaysOne) {
    BH_LaunchParams p = make_schwarzschild_params(8, 8);

    int rc = bh_launch_geodesic_kernel(d_fb_8x8, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    ASSERT_EQ(rc, 0) << "alpha test launch returned error " << rc;

    cudaDeviceSynchronize();

    auto host = copy_framebuffer(d_fb_8x8, 64);
    for (int i = 0; i < 64; ++i) {
        EXPECT_FLOAT_EQ(host[static_cast<std::size_t>(i)].w, 1.0f)
            << "pixel " << i << " alpha is not 1.0";
    }
}
