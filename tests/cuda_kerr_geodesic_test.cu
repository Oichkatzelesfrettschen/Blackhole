/*
 * cuda_kerr_geodesic_test.cu
 * Device Kerr geodesic helpers in src/cuda/device_physics.cuh.
 *
 * d_kerr_init_geodesic on the spin axis: a camera at (0, 0, 30) has no
 * Boyer-Lindquist azimuth, so the initializer takes it from the transverse
 * part of the ray direction. Rays along +x and +y then start with Lz = 0, the
 * same Carter constant, and w along their transverse direction with
 * |w| = p_theta; a start that leaves e_theta at the azimuth of atan2(0, 0)
 * zeroes w for +y and traces that ray radially. A camera 1e-4 off the axis,
 * which takes the generic branch, starts with the same state to 1e-4 of each
 * quantity's scale. Skips without a CUDA device.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>

#include <cmath>
#include <vector>

#include "cuda/kernel_launch.h"
#include "cuda/device_physics.cuh"

namespace {

constexpr double K_PI = 3.14159265358979323846; /* CUDA 17: no std::numbers */
constexpr int K_INIT_FIELDS = 6; /* Q, Lz, vr, w.x, w.y, w.z */

__global__ void kerr_init_kernel(float3 pos, const float3 *dirs, int count, float a,
                                 float *out) {
    int const i = static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x);
    if (i >= count) {
        return;
    }
    KerrConsts c;
    KerrRay ray;
    d_kerr_init_geodesic(pos, dirs[i], 2.0f, a, c, ray);
    float *o = out + K_INIT_FIELDS * i;
    o[0] = c.Q;
    o[1] = c.Lz;
    o[2] = ray.vr;
    o[3] = ray.w.x;
    o[4] = ray.w.y;
    o[5] = ray.w.z;
}

bool cudaAvailable() {
    int count = 0;
    return (cudaGetDeviceCount(&count) == cudaSuccess) && (count > 0);
}

std::vector<float> initRays(float3 pos, const std::vector<float3> &dirs, float a) {
    auto const count = static_cast<int>(dirs.size());
    float3 *dDirs = nullptr;
    float *dOut = nullptr;
    cudaMalloc(&dDirs, dirs.size() * sizeof(float3));
    cudaMalloc(&dOut, dirs.size() * K_INIT_FIELDS * sizeof(float));
    cudaMemcpy(dDirs, dirs.data(), dirs.size() * sizeof(float3), cudaMemcpyHostToDevice);
    kerr_init_kernel<<<(count + 63) / 64, 64>>>(pos, dDirs, count, a, dOut);
    cudaDeviceSynchronize();
    std::vector<float> out(dirs.size() * K_INIT_FIELDS);
    cudaMemcpy(out.data(), dOut, out.size() * sizeof(float), cudaMemcpyDeviceToHost);
    cudaFree(dDirs);
    cudaFree(dOut);
    return out;
}

constexpr int K_RAYS = 63;

/* Fan from straight down (alpha -> 0) through transverse (alpha = pi/2 at
 * i = 31) to straight up, in the xz (plane 0) or yz (plane 1) plane. */
std::vector<float3> poleFan(int plane) {
    std::vector<float3> dirs;
    for (int i = 0; i < K_RAYS; ++i) {
        double const alpha =
            K_PI * static_cast<double>(i + 1) / static_cast<double>(K_RAYS + 1);
        auto const s = static_cast<float>(std::sin(alpha));
        auto const c = static_cast<float>(std::cos(alpha));
        dirs.push_back(plane == 0 ? make_float3(s, 0.0f, -c) : make_float3(0.0f, s, -c));
    }
    return dirs;
}

} // namespace

TEST(CudaKerrGeodesic, PoleStartCarriesTransverseDirectionInW) {
    if (!cudaAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    float3 const pole = make_float3(0.0f, 0.0f, 30.0f);
    for (float const spin : {0.0f, 0.9f}) {
        float const aTrace = -spin; /* d_kerr_trace_spin(0.5 * spin * r_s), r_s = 2 */
        std::vector<float> const xs = initRays(pole, poleFan(0), aTrace);
        std::vector<float> const ys = initRays(pole, poleFan(1), aTrace);
        for (int i = 0; i < K_RAYS; ++i) {
            auto const k = static_cast<std::size_t>(K_INIT_FIELDS * i);
            double const transverse =
                30.0 * std::sin(K_PI * (i + 1) / (K_RAYS + 1));
            EXPECT_EQ(xs[k + 1], 0.0f) << "spin=" << spin << " ray " << i;
            EXPECT_EQ(ys[k + 1], 0.0f) << "spin=" << spin << " ray " << i;
            EXPECT_NEAR(ys[k], xs[k], 1e-5f * std::fmax(1.0f, std::fabs(xs[k])))
                << "spin=" << spin << " ray " << i;
            EXPECT_NEAR(ys[k + 2], xs[k + 2], 1e-5f * std::fmax(1.0f, std::fabs(xs[k + 2])))
                << "spin=" << spin << " ray " << i;
            /* x fan: w along +x; y fan: the same w rotated by 90 degrees about z. */
            EXPECT_GT(xs[k + 3], 0.9 * transverse) << "spin=" << spin << " ray " << i;
            EXPECT_NEAR(ys[k + 3], -xs[k + 4], 1e-4f * 30.0f) << "spin=" << spin << " ray " << i;
            EXPECT_NEAR(ys[k + 4], xs[k + 3], 1e-4f * 30.0f) << "spin=" << spin << " ray " << i;
            EXPECT_NEAR(ys[k + 5], xs[k + 5], 1e-4f * 30.0f) << "spin=" << spin << " ray " << i;
        }
    }
}

TEST(CudaKerrGeodesic, PoleStartIsContinuousWithOffAxisStart) {
    if (!cudaAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    /* The 1e-4 offset tilts e_r by 1e-4 / r: vr and Q (scale r^2) move by
     * about 1e-4 r and w (scale r) by about 1e-4. */
    constexpr float K_R = 30.0f;
    constexpr float K_TOL = 1e-4f;
    for (float const spin : {0.0f, 0.9f}) {
        for (int const plane : {0, 1}) {
            std::vector<float> const axis =
                initRays(make_float3(0.0f, 0.0f, K_R), poleFan(plane), -spin);
            for (float3 const off : {make_float3(1e-4f, 0.0f, K_R), make_float3(0.0f, 1e-4f, K_R)}) {
                std::vector<float> const o = initRays(off, poleFan(plane), -spin);
                for (int i = 0; i < K_RAYS; ++i) {
                    auto const k = static_cast<std::size_t>(K_INIT_FIELDS * i);
                    EXPECT_NEAR(o[k], axis[k], K_TOL * K_R * K_R) << "spin=" << spin << " ray " << i;
                    EXPECT_NEAR(o[k + 1], 0.0f, K_TOL * K_R) << "spin=" << spin << " ray " << i;
                    EXPECT_NEAR(o[k + 2], axis[k + 2], K_TOL * K_R * K_R)
                        << "spin=" << spin << " ray " << i;
                    for (int j = 3; j < 6; ++j) {
                        EXPECT_NEAR(o[k + j], axis[k + j], K_TOL * K_R)
                            << "spin=" << spin << " ray " << i << " w" << j - 3;
                    }
                }
            }
        }
    }
}
