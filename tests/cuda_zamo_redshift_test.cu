/**
 * @file tests/cuda_zamo_redshift_test.cu
 * @brief The CUDA no-LUT redshift fallback follows the LUT's ZAMO-lapse model.
 *
 * d_zamo_redshift (src/cuda/device_zamo_redshift.cuh) runs on the device and
 * is compared with mpmath values of 1 / sqrt(Sigma Delta / A) - 1 at the
 * equator, the model of physics::kerrRedshift and the redshift LUT. r_s = 2,
 * so r = 3M is 3.0.
 */

#include <cuda_runtime.h>
#include <gtest/gtest.h>

#include <array>

#include "cuda/device_zamo_redshift.cuh"

namespace {

struct Case {
    float r;
    float a_star;
    double expected;
};

// r_s = 2 (M = 1). The last two cases lie inside r_+ = 1.436 and read the LUT
// cap; r = 0.2 is inside r_- = 0.564, where Delta is positive again.
constexpr std::array<Case, 6> K_CASES = {{
    {3.0f, 0.9f, 0.64819156443383915},
    {6.0f, 0.9f, 0.2225214295493458},
    {1.8f, 0.9f, 2.3166247903553998},  // inside the equatorial ergosphere (r = 2M)
    {6.0f, 0.0f, 0.22474487139158894},
    {1.2f, 0.9f, 10.0},
    {0.2f, 0.9f, 10.0},
}};

__global__ void kZamoRedshift(const float *radii, const float *spins, float *out, int count) {
    int const i = static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x);
    if (i < count) {
        out[i] = d_zamo_redshift(radii[i], 2.0f, spins[i]);
    }
}

} // namespace

TEST(CudaZamoRedshift, MatchesLutModel) {
    int device_count = 0;
    if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count == 0) {
        GTEST_SKIP() << "no CUDA device";
    }
    constexpr int n = static_cast<int>(K_CASES.size());
    std::array<float, n> radii{};
    std::array<float, n> spins{};
    for (int i = 0; i < n; ++i) {
        radii[static_cast<size_t>(i)] = K_CASES[static_cast<size_t>(i)].r;
        spins[static_cast<size_t>(i)] = K_CASES[static_cast<size_t>(i)].a_star;
    }
    float *d_radii = nullptr;
    float *d_spins = nullptr;
    float *d_out = nullptr;
    ASSERT_EQ(cudaMalloc(&d_radii, sizeof(float) * n), cudaSuccess);
    ASSERT_EQ(cudaMalloc(&d_spins, sizeof(float) * n), cudaSuccess);
    ASSERT_EQ(cudaMalloc(&d_out, sizeof(float) * n), cudaSuccess);
    cudaMemcpy(d_radii, radii.data(), sizeof(float) * n, cudaMemcpyHostToDevice);
    cudaMemcpy(d_spins, spins.data(), sizeof(float) * n, cudaMemcpyHostToDevice);
    kZamoRedshift<<<1, 32>>>(d_radii, d_spins, d_out, n);
    ASSERT_EQ(cudaDeviceSynchronize(), cudaSuccess);
    std::array<float, n> out{};
    cudaMemcpy(out.data(), d_out, sizeof(float) * n, cudaMemcpyDeviceToHost);
    cudaFree(d_radii);
    cudaFree(d_spins);
    cudaFree(d_out);
    for (int i = 0; i < n; ++i) {
        const Case &c = K_CASES[static_cast<size_t>(i)];
        EXPECT_NEAR(static_cast<double>(out[static_cast<size_t>(i)]), c.expected,
                    1.0e-5 * c.expected)
            << "r=" << c.r << " a*=" << c.a_star;
    }
}
