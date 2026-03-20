/*
 * cuda_variants_test.cu
 * Validates consistency across all 4 CUDA kernel variants.
 *
 * WHY: The kernel registry (kernel_registry.h) selects the best variant for
 *      the current device. All variants must produce equivalent output for the
 *      same scene, within precision bounds dictated by their storage types.
 *      FP16 variants trade some precision for reduced register pressure;
 *      this test ensures the precision loss is bounded and not catastrophic.
 *
 * WHAT: 64x64 scene (4096 pixels) rendered by all 4 variants:
 *   BH_KERNEL_FP32_BASELINE  (1 ray/thread, FP32)
 *   BH_KERNEL_FP32_COARSENED (2 rays/thread, FP32)  -- must match baseline to 1e-4 RMSE
 *   BH_KERNEL_FP16_STORAGE   (FP16 ray state)        -- must match baseline to 0.05 RMSE
 *   BH_KERNEL_FP16_H2_ILP    (2 rays/thread, FP16)   -- must match baseline to 0.10 RMSE
 *
 *   Additionally: every variant must produce no NaN/Inf and launch without error.
 *
 * HOW: Allocate one float4 device buffer per variant, run all 4 in sequence,
 *      copy to host, compute per-channel RMSE between baseline and each other.
 *      Tests skip gracefully if no CUDA device is present.
 *      Variants requiring higher SM than the device are skipped individually.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>
#include <string>

#include "cuda/kernel_launch.h"
#include "cuda/kernel_registry.h"

/* ========================================================================
 * Constants and helpers
 * ======================================================================== */

static constexpr int kW = 64;
static constexpr int kH = 64;
static constexpr int kN = kW * kH;  /* 4096 pixels */

static BH_LaunchParams make_variants_params() {
    BH_LaunchParams p = {};

    p.rs            = 2.0f;
    p.spin          = 0.6f;     /* moderate spin to exercise Kerr path */
    p.isco          = 4.5f;
    p.step_size     = 0.08f;
    p.fov_scale     = 1.2f;
    p.max_dist      = 150.0f;
    p.max_steps     = 500;
    p.width         = kW;
    p.height        = kH;
    p.adisk_enabled    = 1;     /* enable disk for variety in pixel outcomes */
    p.redshift_enabled = 1;
    p.kerr_enabled     = 1;
    p.use_luts         = 0;

    /* Camera at (0, 0, 15): oblique to equatorial plane for mixed outcomes */
    p.cam_pos[0] = 0.0f;
    p.cam_pos[1] = 3.0f;
    p.cam_pos[2] = 15.0f;

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

    p.time_sec             = 0.0f;
    p.doppler_strength     = 1.0f;
    p.background_intensity = 0.0f;  /* disable background so we focus on BH */
    p.background_enabled   = 0;

    return p;
}

/* Returns the SM version of device 0 as an integer (e.g. SM8.9 = 89). */
static int device_sm() {
    int major = 0, minor = 0;
    cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0);
    cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0);
    return major * 10 + minor;
}

/* Root-mean-square error across all RGBA channels of all pixels. */
static double compute_rmse(const std::vector<float4>& a, const std::vector<float4>& b) {
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

static bool all_finite(const std::vector<float4>& v) {
    for (const auto& px : v) {
        if (!std::isfinite(px.x) || !std::isfinite(px.y)
         || !std::isfinite(px.z) || !std::isfinite(px.w)) {
            return false;
        }
    }
    return true;
}

/* ========================================================================
 * Test fixture: owns one device buffer per variant and the baseline.
 * ======================================================================== */

class CudaVariantsTest : public ::testing::Test {
protected:
    void SetUp() override {
        int dev_count = 0;
        cudaGetDeviceCount(&dev_count);
        if (dev_count == 0) {
            GTEST_SKIP() << "No CUDA device available";
        }

        for (int v = 0; v < BH_KERNEL_COUNT; ++v) {
            cudaError_t err = cudaMalloc(&d_bufs[v],
                                         static_cast<std::size_t>(kN) * sizeof(float4));
            ASSERT_EQ(err, cudaSuccess)
                << "cudaMalloc for variant " << v << " failed: "
                << cudaGetErrorString(err);
        }
    }

    void TearDown() override {
        for (int v = 0; v < BH_KERNEL_COUNT; ++v) {
            if (d_bufs[v]) {
                cudaFree(d_bufs[v]);
                d_bufs[v] = nullptr;
            }
        }
    }

    /* Launch one variant and copy the result to host. */
    std::vector<float4> render(int variant, const BH_LaunchParams& p) {
        int rc = bh_launch_geodesic_kernel(d_bufs[variant], &p, variant, nullptr);
        if (rc != 0) {
            ADD_FAILURE() << "bh_launch_geodesic_kernel(variant=" << variant
                          << ") returned " << rc;
            return {};
        }
        cudaDeviceSynchronize();

        std::vector<float4> host(static_cast<std::size_t>(kN));
        cudaMemcpy(host.data(), d_bufs[variant],
                   static_cast<std::size_t>(kN) * sizeof(float4),
                   cudaMemcpyDeviceToHost);
        return host;
    }

    float4* d_bufs[BH_KERNEL_COUNT] = {};
};

/* ========================================================================
 * 1. Every variant launches without error and produces no NaN/Inf.
 * ======================================================================== */

TEST_F(CudaVariantsTest, AllVariantsLaunchClean) {
    BH_LaunchParams p = make_variants_params();
    int sm = device_sm();

    for (int v = 0; v < BH_KERNEL_COUNT; ++v) {
        const RtKernelInfo* info = registry_get_info(v);
        ASSERT_NE(info, nullptr);

        if (sm < info->min_sm) {
            /* Variant requires a higher SM than the current device. */
            GTEST_LOG_(INFO) << "Skipping variant " << info->name
                             << " (needs SM" << info->min_sm
                             << ", have SM" << sm << ")";
            continue;
        }

        auto host = render(v, p);
        ASSERT_FALSE(host.empty()) << "variant " << info->name << " render failed";

        EXPECT_TRUE(all_finite(host))
            << "variant " << info->name << " produced NaN or Inf pixels";
    }
}

/* ========================================================================
 * 2. FP32 coarsened matches FP32 baseline (same math, only thread mapping differs).
 *    Both process two rays per thread using independent FP32 computation chains,
 *    so results must be bit-exact (or within floating-point rounding of 1e-4 RMSE).
 * ======================================================================== */

TEST_F(CudaVariantsTest, FP32CoarsenedMatchesBaseline) {
    int sm = device_sm();
    const RtKernelInfo* baseline_info  = registry_get_info(BH_KERNEL_FP32_BASELINE);
    const RtKernelInfo* coarsened_info = registry_get_info(BH_KERNEL_FP32_COARSENED);

    if (sm < baseline_info->min_sm || sm < coarsened_info->min_sm) {
        GTEST_SKIP() << "Device SM" << sm << " does not meet minimum for one of these variants";
    }

    BH_LaunchParams p = make_variants_params();
    auto baseline  = render(BH_KERNEL_FP32_BASELINE,  p);
    auto coarsened = render(BH_KERNEL_FP32_COARSENED, p);

    ASSERT_EQ(baseline.size(),  static_cast<std::size_t>(kN));
    ASSERT_EQ(coarsened.size(), static_cast<std::size_t>(kN));

    EXPECT_TRUE(all_finite(baseline))  << "FP32 baseline has NaN/Inf";
    EXPECT_TRUE(all_finite(coarsened)) << "FP32 coarsened has NaN/Inf";

    double rmse = compute_rmse(baseline, coarsened);
    EXPECT_LT(rmse, 1e-4)
        << "FP32 coarsened vs baseline RMSE=" << rmse
        << " exceeds 1e-4; variants must produce identical FP32 math";
}

/* ========================================================================
 * 3. FP16 storage variant is within 0.05 RMSE of FP32 baseline.
 *    FP16 has ~3 decimal digits of precision. Integrated over many RK4 steps,
 *    small per-step errors accumulate, but the bound must hold for the disk/BH
 *    scene tested here (moderate step count, step_size=0.08).
 * ======================================================================== */

TEST_F(CudaVariantsTest, FP16StorageWithinToleranceOfBaseline) {
    int sm = device_sm();
    const RtKernelInfo* baseline_info = registry_get_info(BH_KERNEL_FP32_BASELINE);
    const RtKernelInfo* fp16_info     = registry_get_info(BH_KERNEL_FP16_STORAGE);

    if (sm < baseline_info->min_sm || sm < fp16_info->min_sm) {
        GTEST_SKIP() << "Device SM" << sm << " does not meet minimum for FP16 storage variant";
    }

    BH_LaunchParams p = make_variants_params();
    auto baseline = render(BH_KERNEL_FP32_BASELINE, p);
    auto fp16     = render(BH_KERNEL_FP16_STORAGE,  p);

    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));
    ASSERT_EQ(fp16.size(),     static_cast<std::size_t>(kN));

    EXPECT_TRUE(all_finite(baseline)) << "FP32 baseline has NaN/Inf";
    EXPECT_TRUE(all_finite(fp16))     << "FP16 storage has NaN/Inf";

    double rmse = compute_rmse(baseline, fp16);
    EXPECT_LT(rmse, 0.05)
        << "FP16 storage vs FP32 baseline RMSE=" << rmse
        << " exceeds 0.05; FP16 precision degradation is too large";
}

/* ========================================================================
 * 4. FP16 H2 ILP variant is within 0.10 RMSE of FP32 baseline.
 *    H2 interleaves two rays per thread using __half2 in parts of the pipeline.
 *    The wider tolerance (0.10) accounts for dual-issue ordering differences
 *    and potential intermediate __half2 rounding.
 * ======================================================================== */

TEST_F(CudaVariantsTest, FP16H2ILPWithinToleranceOfBaseline) {
    int sm = device_sm();
    const RtKernelInfo* baseline_info = registry_get_info(BH_KERNEL_FP32_BASELINE);
    const RtKernelInfo* h2_info       = registry_get_info(BH_KERNEL_FP16_H2_ILP);

    if (sm < baseline_info->min_sm || sm < h2_info->min_sm) {
        GTEST_SKIP() << "Device SM" << sm << " does not meet minimum for FP16 H2 ILP variant"
                     << " (needs SM" << h2_info->min_sm << ", have SM" << sm << ")";
    }

    BH_LaunchParams p = make_variants_params();
    auto baseline = render(BH_KERNEL_FP32_BASELINE, p);
    auto h2       = render(BH_KERNEL_FP16_H2_ILP,   p);

    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));
    ASSERT_EQ(h2.size(),       static_cast<std::size_t>(kN));

    EXPECT_TRUE(all_finite(baseline)) << "FP32 baseline has NaN/Inf";
    EXPECT_TRUE(all_finite(h2))       << "FP16 H2 ILP has NaN/Inf";

    double rmse = compute_rmse(baseline, h2);
    EXPECT_LT(rmse, 0.10)
        << "FP16 H2 ILP vs FP32 baseline RMSE=" << rmse
        << " exceeds 0.10; H2 ILP precision degradation is too large";
}

/* ========================================================================
 * 5. Horizon pixels are consistent across variants.
 *    Pixels that FP32 baseline identifies as pure black (horizon hit)
 *    should also be black in all other variants (both paths take the same
 *    early-exit when r <= r_horizon before any precision-sensitive math).
 * ======================================================================== */

TEST_F(CudaVariantsTest, HorizonPixelsConsistentAcrossVariants) {
    int sm = device_sm();

    /* Use a simpler Schwarzschild scene where horizon pixels are well-defined */
    BH_LaunchParams p = make_variants_params();
    p.spin         = 0.0f;
    p.kerr_enabled = 0;
    p.isco         = 6.0f;

    auto baseline = render(BH_KERNEL_FP32_BASELINE, p);
    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));

    for (int v = BH_KERNEL_FP32_COARSENED; v < BH_KERNEL_COUNT; ++v) {
        const RtKernelInfo* info = registry_get_info(v);
        ASSERT_NE(info, nullptr);

        if (sm < info->min_sm) {
            GTEST_LOG_(INFO) << "Skipping variant " << info->name
                             << " horizon consistency check (SM" << info->min_sm
                             << " required, have SM" << sm << ")";
            continue;
        }

        auto variant_out = render(v, p);
        ASSERT_EQ(variant_out.size(), static_cast<std::size_t>(kN));

        int mismatches = 0;
        for (int i = 0; i < kN; ++i) {
            const float4& bl = baseline[static_cast<std::size_t>(i)];
            const float4& vp = variant_out[static_cast<std::size_t>(i)];
            bool bl_horizon = (bl.x == 0.0f && bl.y == 0.0f && bl.z == 0.0f);
            bool vp_horizon = (vp.x == 0.0f && vp.y == 0.0f && vp.z == 0.0f);
            if (bl_horizon != vp_horizon) {
                ++mismatches;
            }
        }
        EXPECT_EQ(mismatches, 0)
            << info->name << " disagrees with baseline on " << mismatches
            << " horizon/non-horizon pixel classifications";
    }
}

/* ========================================================================
 * 6. Auto-selected variant is consistent with FP32 baseline.
 *    bh_select_kernel_variant() picks the best variant for this device.
 *    Its output must be within the tolerance of whichever variant was chosen.
 * ======================================================================== */

TEST_F(CudaVariantsTest, AutoSelectedVariantConsistent) {
    BH_LaunchParams p = make_variants_params();

    int selected = bh_select_kernel_variant();
    ASSERT_GE(selected, 0);
    ASSERT_LT(selected, BH_KERNEL_COUNT);

    const RtKernelInfo* info = registry_get_info(selected);
    ASSERT_NE(info, nullptr);

    auto baseline = render(BH_KERNEL_FP32_BASELINE, p);
    auto autosel  = render(selected,                 p);

    ASSERT_EQ(baseline.size(), static_cast<std::size_t>(kN));
    ASSERT_EQ(autosel.size(),  static_cast<std::size_t>(kN));

    EXPECT_TRUE(all_finite(baseline)) << "FP32 baseline has NaN/Inf";
    EXPECT_TRUE(all_finite(autosel))  << "Auto-selected variant has NaN/Inf";

    /* Use the widest tolerance (H2 ILP bound = 0.10) since any variant
     * could be auto-selected on high-end devices. */
    double rmse = compute_rmse(baseline, autosel);
    EXPECT_LT(rmse, 0.10)
        << "Auto-selected variant '" << info->name << "' RMSE=" << rmse
        << " vs FP32 baseline exceeds 0.10";
}
