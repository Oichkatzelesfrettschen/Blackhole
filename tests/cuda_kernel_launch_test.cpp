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
 * WHAT: host-vs-nvcc ABI agreement on BH_LaunchParams (sizeof + probed
 *       offsetof via bh_device_launch_params_abi); POD contract; enum value
 *       checks; registry metadata table sanity; bh_select_kernel_variant()
 *       returns a value in [0, BH_KERNEL_COUNT).
 *
 * HOW: Compiled as C++23, linked against blackhole_cuda_rt + CUDA::cudart.
 *      No OpenGL context required. No CUDA device required for layout tests.
 *      GTEST_SKIP() guards runtime calls that need a device.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>   // NOLINT(misc-include-cleaner) -- umbrella header
#include <cstddef>
#include <type_traits>

/* POD-only firewall header -- must not pull in any C++23 types */
#include "cuda/kernel_launch.h"
#include "cuda/kernel_registry.h"

/* ========================================================================
 * 1. Struct layout
 * ======================================================================== */

/* The hazard is host-compiler/nvcc layout divergence: BH_LaunchParams is
 * one header, but each toolchain computes its layout independently, and a
 * packing or alignment flag mismatch corrupts every kernel parameter
 * silently. bh_device_launch_params_abi() reports sizeof/offsetof as nvcc
 * compiled them; comparing against the host compiler's own values tests
 * the real hazard with zero hand-maintained literals. The previous
 * literal-pinned variant rotted unseen while ENABLE_CUDA stayed OFF in CI
 * (expected 188 bytes; the struct had grown to 336). */
TEST(CudaKernelLaunch, LaunchParamsHostDeviceAbiAgreement) {
    const BH_LaunchParamsAbi deviceAbi = bh_device_launch_params_abi();

    EXPECT_EQ(deviceAbi.size, sizeof(BH_LaunchParams))
        << "host compiler and nvcc disagree on sizeof(BH_LaunchParams)";

    std::size_t index = 0;
#define BH_ABI_CHECK(field)                                                  \
    EXPECT_EQ(deviceAbi.offsets[index++], offsetof(BH_LaunchParams, field))  \
        << "host/nvcc offsetof divergence at field: " #field;
    BH_LAUNCH_PARAMS_ABI_FIELDS(BH_ABI_CHECK)
#undef BH_ABI_CHECK
    EXPECT_EQ(index, sizeof(deviceAbi.offsets) / sizeof(deviceAbi.offsets[0]))
        << "ABI field list length drifted from BH_LaunchParamsAbi.offsets";
}

TEST(CudaKernelLaunch, LaunchParamsPodContract) {
    /* The C firewall requires a standard-layout, trivially-copyable POD;
     * cudaMemcpyToSymbol of the whole struct depends on it. */
    EXPECT_TRUE(std::is_standard_layout_v<BH_LaunchParams>);
    EXPECT_TRUE(std::is_trivially_copyable_v<BH_LaunchParams>);
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
