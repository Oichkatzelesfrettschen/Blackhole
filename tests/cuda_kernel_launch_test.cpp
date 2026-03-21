/*
 * cuda_kernel_launch_test.cpp
 * Validates the POD-only C-compatible interface in kernel_launch.h.
 *
 * WHY: The C++23/C++17 firewall depends on BH_LaunchParams being a plain C
 *      struct. If a C++23-side developer accidentally adds a non-POD field,
 *      the CUDA build breaks with cryptic nvcc errors. This test catches that
 *      at the C++ side: struct size, field offsets, and enum values are stable
 *      and match what the device side expects.
 *
 * WHAT: sizeof/offsetof assertions on BH_LaunchParams; enum value checks;
 *       registry metadata table sanity; bh_select_kernel_variant() returns
 *       a value in [0, BH_KERNEL_COUNT).
 *
 * HOW: Compiled as C++23, linked against blackhole_cuda_rt + CUDA::cudart.
 *      No OpenGL context required. No CUDA device required for layout tests.
 *      GTEST_SKIP() guards runtime calls that need a device.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>   // NOLINT(misc-include-cleaner) -- umbrella header
#include <cstddef>

/* POD-only firewall header -- must not pull in any C++23 types */
#include "cuda/kernel_launch.h"
#include "cuda/kernel_registry.h"

/* ========================================================================
 * 1. Struct layout
 * ======================================================================== */

TEST(CudaKernelLaunch, LaunchParamsSize) {
    /* 6 floats (rs..max_dist=24) + cam_pos[3](12) + cam_basis[9](36) = 72
     * + 3 ints (max_steps, width, height = 12) = 84
     * + 4 ints (adisk..use_luts = 16) = 100
     * + 6 floats (lut bounds = 24) = 124
     * + 3 floats (time_sec, doppler, bg_intensity = 12) = 136
     * + 1 int (background_enabled = 4) = 140
     * + 1 int (wiregrid_enabled = 4) = 144
     * + 2 floats (wiregrid_show_ergo, wiregrid_grid_scale = 8) = 152
     * + 2 floats (grmhd_r_min, grmhd_r_max = 8) = 160
     * + 1 int (rte_enabled = 4) = 164
     * + 1 float (rte_opacity_scale = 4) = 168
     * + 1 float (grmhd_alpha = 4) = 172   [C1d]
     * All fields 4-byte, naturally aligned => no padding expected.
     */
    EXPECT_EQ(sizeof(BH_LaunchParams), static_cast<std::size_t>(172))
        << "BH_LaunchParams size changed -- verify device_physics.cuh offsets"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
}

TEST(CudaKernelLaunch, LaunchParamsFieldOffsets) {
    /* Scalars before arrays */
    EXPECT_EQ(offsetof(BH_LaunchParams, rs),              static_cast<std::size_t>(0));
    EXPECT_EQ(offsetof(BH_LaunchParams, spin),            static_cast<std::size_t>(4));
    EXPECT_EQ(offsetof(BH_LaunchParams, isco),            static_cast<std::size_t>(8));
    EXPECT_EQ(offsetof(BH_LaunchParams, step_size),       static_cast<std::size_t>(12));
    EXPECT_EQ(offsetof(BH_LaunchParams, fov_scale),       static_cast<std::size_t>(16));
    EXPECT_EQ(offsetof(BH_LaunchParams, max_dist),        static_cast<std::size_t>(20));

    /* Arrays */
    EXPECT_EQ(offsetof(BH_LaunchParams, cam_pos),         static_cast<std::size_t>(24));
    EXPECT_EQ(offsetof(BH_LaunchParams, cam_basis),       static_cast<std::size_t>(36));

    /* Int flags */
    EXPECT_EQ(offsetof(BH_LaunchParams, max_steps),       static_cast<std::size_t>(72));
    EXPECT_EQ(offsetof(BH_LaunchParams, width),           static_cast<std::size_t>(76));
    EXPECT_EQ(offsetof(BH_LaunchParams, height),          static_cast<std::size_t>(80));
    EXPECT_EQ(offsetof(BH_LaunchParams, adisk_enabled),   static_cast<std::size_t>(84));
    EXPECT_EQ(offsetof(BH_LaunchParams, redshift_enabled),static_cast<std::size_t>(88));
    EXPECT_EQ(offsetof(BH_LaunchParams, kerr_enabled),    static_cast<std::size_t>(92));
    EXPECT_EQ(offsetof(BH_LaunchParams, use_luts),        static_cast<std::size_t>(96));

    /* LUT domain bounds */
    EXPECT_EQ(offsetof(BH_LaunchParams, lut_radius_min),       static_cast<std::size_t>(100));
    EXPECT_EQ(offsetof(BH_LaunchParams, lut_radius_max),       static_cast<std::size_t>(104));
    EXPECT_EQ(offsetof(BH_LaunchParams, redshift_radius_min),  static_cast<std::size_t>(108));
    EXPECT_EQ(offsetof(BH_LaunchParams, redshift_radius_max),  static_cast<std::size_t>(112));
    EXPECT_EQ(offsetof(BH_LaunchParams, spectral_radius_min),  static_cast<std::size_t>(116));
    EXPECT_EQ(offsetof(BH_LaunchParams, spectral_radius_max),  static_cast<std::size_t>(120));

    /* Physics misc */
    EXPECT_EQ(offsetof(BH_LaunchParams, time_sec),             static_cast<std::size_t>(124));
    EXPECT_EQ(offsetof(BH_LaunchParams, doppler_strength),     static_cast<std::size_t>(128));
    EXPECT_EQ(offsetof(BH_LaunchParams, background_intensity), static_cast<std::size_t>(132));
    EXPECT_EQ(offsetof(BH_LaunchParams, background_enabled),   static_cast<std::size_t>(136));

    /* C1d: GRMHD temporal interpolation */
    EXPECT_EQ(offsetof(BH_LaunchParams, grmhd_alpha),          static_cast<std::size_t>(168)); // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
}

/* ========================================================================
 * 2. Enum values
 * ======================================================================== */

TEST(CudaKernelLaunch, KernelVariantEnumValues) {
    EXPECT_EQ(BH_KERNEL_FP32_BASELINE,  0);
    EXPECT_EQ(BH_KERNEL_FP32_COARSENED, 1);
    EXPECT_EQ(BH_KERNEL_FP16_STORAGE,   2);
    EXPECT_EQ(BH_KERNEL_FP16_H2_ILP,    3);
    EXPECT_EQ(BH_KERNEL_COUNT,          4);
}

/* ========================================================================
 * 3. Registry metadata table
 * ======================================================================== */

TEST(CudaKernelLaunch, RegistryAllVariantsHaveNames) {
    for (int v = 0; v < BH_KERNEL_COUNT; ++v) {
        const RtKernelInfo* info = registry_get_info(v);
        ASSERT_NE(info, nullptr) << "registry_get_info(" << v << ") returned null"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
        EXPECT_NE(info->name, nullptr) << "variant " << v << " has null name"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
        EXPECT_GT(info->min_sm, 0) << "variant " << v << " min_sm <= 0"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
        EXPECT_GT(info->tpb, 0) << "variant " << v << " tpb <= 0"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
        EXPECT_GT(info->estimated_registers, 0) << "variant " << v << " regs <= 0"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
    }
}

TEST(CudaKernelLaunch, RegistryOutOfBoundsReturnsNull) {
    EXPECT_EQ(registry_get_info(-1),            nullptr);
    EXPECT_EQ(registry_get_info(BH_KERNEL_COUNT), nullptr);
    EXPECT_EQ(registry_get_info(100),           nullptr);
}

TEST(CudaKernelLaunch, RegistryVariantOrdering) {
    /* Variants are ordered by capability: baseline has lowest min_sm */
    const RtKernelInfo* baseline  = registry_get_info(BH_KERNEL_FP32_BASELINE);
    const RtKernelInfo* coarsened = registry_get_info(BH_KERNEL_FP32_COARSENED);
    const RtKernelInfo* fp16      = registry_get_info(BH_KERNEL_FP16_STORAGE);
    const RtKernelInfo* h2        = registry_get_info(BH_KERNEL_FP16_H2_ILP);

    ASSERT_NE(baseline,  nullptr);
    ASSERT_NE(coarsened, nullptr);
    ASSERT_NE(fp16,      nullptr);
    ASSERT_NE(h2,        nullptr);

    /* Baseline must run on anything (min_sm = 50 means SM5.0+) */
    EXPECT_LE(baseline->min_sm, coarsened->min_sm);
    EXPECT_LE(coarsened->min_sm, fp16->min_sm);
    EXPECT_LE(fp16->min_sm, h2->min_sm);

    /* H2 ILP variant processes 2 rays per thread */
    EXPECT_EQ(h2->rays_per_thread, 2);
    EXPECT_EQ(baseline->rays_per_thread, 1);

    /* H2 thread block is smaller to leave room for doubled register state */
    EXPECT_LE(h2->tpb, baseline->tpb);
}

/* ========================================================================
 * 4. Variant auto-selection (requires CUDA runtime, skipped without device)
 * ======================================================================== */

TEST(CudaKernelLaunch, SelectVariantReturnsValidIndex) {
    int devCount = 0;
    cudaGetDeviceCount(&devCount); // NOLINT(misc-include-cleaner)
    if (devCount == 0) {
        GTEST_SKIP() << "No CUDA device available -- skipping runtime selection test"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
    }

    const int variant = bh_select_kernel_variant();
    EXPECT_GE(variant, 0)               << "bh_select_kernel_variant() returned < 0"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
    EXPECT_LT(variant, BH_KERNEL_COUNT) << "bh_select_kernel_variant() returned >= BH_KERNEL_COUNT"; // NOLINT(readability-implicit-bool-conversion) -- GoogleTest macro expansion
}

TEST(CudaKernelLaunch, SelectVariantCallableWithoutDevice) {
    /* bh_select_kernel_variant() must not crash or abort even when there is
     * no CUDA device -- it should degrade gracefully to FP32_BASELINE. */
    int devCount = 0;
    cudaGetDeviceCount(&devCount); // NOLINT(misc-include-cleaner)

    const int variant = bh_select_kernel_variant();

    /* Whether or not a device exists, the result must be a valid variant. */
    EXPECT_GE(variant, 0);
    EXPECT_LT(variant, BH_KERNEL_COUNT);

    if (devCount == 0) {
        /* Without a device, baseline is the only safe choice */
        EXPECT_EQ(variant, BH_KERNEL_FP32_BASELINE);
    }
}
