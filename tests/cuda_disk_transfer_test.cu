/**
 * @file cuda_disk_transfer_test.cu
 * @brief src/cuda/device_disk_transfer.cuh against the double-precision C++.
 *
 * A kernel evaluates d_dt_page_thorne_shape, d_dt_disk_transfer_g and
 * d_dt_blackbody_chroma over the same grid as
 * tests/disk_transfer_shader_test.cpp (five spins including a retrograde
 * disk, radii 1.1 to 20 r_isco, lambda of 0 and +-0.8 r, three
 * temperatures). Each device value must match physics::pageThorneFluxShape,
 * physics::diskTransferG and physics::blackbodyChromaLinearSrgb evaluated at
 * the device's own float radius.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>

#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include "cuda/device_disk_transfer.cuh"
#include "physics/disk_transfer.h"
#include "physics/page_thorne.h"

namespace {

constexpr int K_CASES = 60; // 5 spins x 4 radii x 3 lambdas
constexpr int K_STRIDE = 6;

__global__ void k_disk_transfer_grid(float *out) {
    int const i = static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x);
    if (i >= K_CASES) {
        return;
    }
    float const spins[5] = {0.0f, 0.5f, 0.9f, 0.998f, -0.5f};
    float const ratios[4] = {1.1f, 1.6f, 4.0f, 20.0f};
    float const lambdas[3] = {0.0f, 0.8f, -0.8f};
    float const temps[3] = {3000.0f, 6500.0f, 12000.0f};
    float const a = spins[i / 12];
    float const r = ratios[(i / 3) % 4] * d_dt_isco_radius(a);
    float const lambda = lambdas[i % 3] * r;
    float3 const chroma = d_dt_blackbody_chroma(temps[i % 3]);
    out[K_STRIDE * i + 0] = r;
    out[K_STRIDE * i + 1] = d_dt_page_thorne_shape(r, a);
    out[K_STRIDE * i + 2] = d_dt_disk_transfer_g(r, a, lambda);
    out[K_STRIDE * i + 3] = chroma.x;
    out[K_STRIDE * i + 4] = chroma.y;
    out[K_STRIDE * i + 5] = chroma.z;
}

bool cudaDeviceAvailable() {
    int count = 0;
    return (cudaGetDeviceCount(&count) == cudaSuccess) && (count > 0);
}

} // namespace

TEST(CudaDiskTransfer, MatchesDoublePrecisionReference) {
    if (!cudaDeviceAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    float *d_out = nullptr;
    std::size_t const bytes = sizeof(float) * K_STRIDE * K_CASES;
    ASSERT_EQ(cudaMalloc(&d_out, bytes), cudaSuccess);
    k_disk_transfer_grid<<<1, 64>>>(d_out);
    ASSERT_EQ(cudaDeviceSynchronize(), cudaSuccess);
    std::vector<float> out(static_cast<std::size_t>(K_STRIDE * K_CASES));
    ASSERT_EQ(cudaMemcpy(out.data(), d_out, bytes, cudaMemcpyDeviceToHost), cudaSuccess);
    cudaFree(d_out);

    std::array<double, 5> const spins = {0.0, 0.5, 0.9, static_cast<double>(0.998f), -0.5};
    std::array<double, 3> const lambdas = {0.0, 0.8, -0.8};
    std::array<double, 3> const temps = {3000.0, 6500.0, 12000.0};
    for (int i = 0; i < K_CASES; ++i) {
        auto const at = [&](int k) {
            return static_cast<double>(out[static_cast<std::size_t>(K_STRIDE * i + k)]);
        };
        double const a = spins[static_cast<std::size_t>(i / 12)];
        double const r = at(0);
        double const lambda = lambdas[static_cast<std::size_t>(i % 3)] * r;

        /* Float cancellation in the logarithmic bracket grows toward the
         * zero-torque edge; 1.1 r_isco is the closest radius sampled. */
        double const shape = physics::pageThorneFluxShape(r, a);
        EXPECT_NEAR(at(1) / shape, 1.0, 2e-3) << "a=" << a << " r=" << r;

        double const g = physics::diskTransferG(r, a, lambda);
        EXPECT_NEAR(at(2) / g, 1.0, 1e-5) << "a=" << a << " r=" << r << " lambda=" << lambda;

        std::array<double, 3> const rgb =
            physics::blackbodyChromaLinearSrgb(temps[static_cast<std::size_t>(i % 3)]);
        for (int c = 0; c < 3; ++c) {
            EXPECT_NEAR(at(3 + c), rgb[static_cast<std::size_t>(c)], 1e-4) << "channel " << c;
        }
    }
}
