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
 * quantity's scale.
 *
 * Radiative transfer through a uniform shell far from the hole, stepped with
 * d_adaptive_step and d_kerr_step, must integrate over the affine path length
 * d_kerr_affine_step returns: it matches the analytic slab solution at two
 * step sizes, where the Mino-time increment would give I ~ 5e-6.
 *
 * On the equatorial stationary limit r = 2M the null condition is linear in
 * k^t: a co-rotating coordinate direction starts on shell, a counter-rotating
 * one (no finite future root) is marked captured, and 1e-4 outside every
 * direction starts on shell.
 *
 * d_disk_segment integrates the Gaussian disk layer along each step's chord:
 * a ray crossing it at radius 30 reproduces the analytic emission column for
 * chords from 0.1 h to 100 h.
 * Skips without a CUDA device.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>

#include <cmath>
#include <vector>

#include "cuda/kernel_launch.h"
#include "cuda/device_physics.cuh"

namespace {

constexpr double K_PI = 3.14159265358979323846; /* CUDA 17: no std::numbers */
constexpr int K_INIT_FIELDS = 7; /* Q, Lz, vr, w.x, w.y, w.z, r */

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
    o[6] = ray.r;
}

/* Uniform shell r_near <= r <= r_far, source function 1, absorption alpha,
 * traced inward from pos along dir (spin a = 0.9 M, r_s = 2). out = (I, T). */
__global__ void kerr_slab_kernel(float3 pos, float3 dir, float step_size, float r_near,
                                 float r_far, float alpha, float *out) {
    float const rs = 2.0f;
    float const a = 0.9f;
    float const r_h = d_kerr_outer_horizon(rs, a);
    float const a_trace = d_kerr_trace_spin(a);
    KerrConsts c;
    KerrRay kr;
    d_kerr_init_geodesic(pos, dir, rs, a_trace, c, kr);
    float transmit = 1.0f;
    float3 accum = make_float3(0.0f, 0.0f, 0.0f);
    for (int step = 0; step < 1000000; ++step) {
        if (kr.r < 0.5f * r_near || kr.r <= r_h) {
            break;
        }
        KerrRay const before = kr;
        float const dlam = d_adaptive_step(kr.r, rs, r_h, step_size);
        d_kerr_step(kr, rs, a_trace, c, dlam);
        if (kr.r >= r_near && kr.r <= r_far) {
            float const ds = d_kerr_affine_step(before, kr, a_trace, dlam);
            accum = d_add(accum, d_rte_step(make_float3(1.0f, 1.0f, 1.0f), alpha, alpha, ds,
                                            transmit));
        }
    }
    out[0] = accum.x;
    out[1] = transmit;
}

/* Ray at inclination incl crossing the disk midplane at (30, 0, 0) from
 * z = 3 to z = -3, cut into chords of seg_length (offset 0.37), each passed
 * to d_disk_segment (r_in = 6, r_s = 2, h = 0.2). out[0] = sum(j_eff * len). */
__global__ void disk_slab_kernel(float seg_length, float incl, float *out) {
    float3 const dir = make_f3(sinf(incl), 0.0f, -cosf(incl));
    float const total = 6.0f / cosf(incl);
    float3 const start = d_sub(make_f3(30.0f, 0.0f, 0.0f), d_scale(dir, 0.5f * total));
    float column = 0.0f;
    float s0 = 0.0f;
    float s1 = fminf(0.37f * seg_length, total);
    for (int k = 0; k < 100000 && s0 < total; ++k) {
        float3 emit_color;
        float j_eff;
        float rho;
        if (d_disk_segment(d_add(start, d_scale(dir, s0)), d_add(start, d_scale(dir, s1)), 6.0f,
                           200.0f, 0.2f, 2.0f, emit_color, j_eff, rho)) {
            column += j_eff * (s1 - s0);
        }
        s0 = s1;
        s1 = fminf(s1 + seg_length, total);
    }
    out[0] = column;
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

TEST(CudaKerrGeodesic, RadiativeTransferIntegratesAffinePathLength) {
    if (!cudaAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    /* Shell 300 <= r <= 700, alpha = 1/400: along the axis the affine length
     * is Delta r = 400 exactly, so I = 1 - e^-1 and T = e^-1. End-point
     * sampling misplaces at most one step (0.5 step_size r ~ 3.5) per
     * boundary, hence the 2% tolerance. */
    double const intensity = 1.0 - std::exp(-1.0);
    double const transmit = std::exp(-1.0);
    float *dOut = nullptr;
    cudaMalloc(&dOut, 2 * sizeof(float));
    for (float const stepSize : {0.01f, 0.0025f}) {
        kerr_slab_kernel<<<1, 1>>>(make_float3(0.0f, 0.0f, 1000.0f), make_float3(0.0f, 0.0f, -1.0f),
                                   stepSize, 300.0f, 700.0f, 1.0f / 400.0f, dOut);
        cudaDeviceSynchronize();
        float out[2] = {0.0f, 0.0f};
        cudaMemcpy(out, dOut, sizeof(out), cudaMemcpyDeviceToHost);
        EXPECT_NEAR(out[0], intensity, 0.02 * intensity) << "stepSize=" << stepSize;
        EXPECT_NEAR(out[1], transmit, 0.02 * transmit) << "stepSize=" << stepSize;
    }
    cudaFree(dOut);
}

TEST(CudaKerrGeodesic, StationaryLimitStartIsOnShell) {
    if (!cudaAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    float const a = 0.6f;
    std::vector<float3> dirs;
    for (int i = 0; i < 128; ++i) {
        double const beta = 2.0 * K_PI * (i + 0.5) / 128.0;
        dirs.push_back(make_float3(static_cast<float>(std::cos(beta)),
                                   static_cast<float>(std::sin(beta)), 0.0f));
    }
    for (float const r0 : {2.0f, 2.0f * (1.0f + 1e-4f)}) {
        std::vector<float> const out = initRays(make_float3(r0, 0.0f, 0.0f), dirs, a);
        int accepted = 0;
        for (int i = 0; i < 128; ++i) {
            auto const k = static_cast<std::size_t>(K_INIT_FIELDS * i);
            double const sinBeta = std::sin(2.0 * K_PI * (i + 0.5) / 128.0);
            bool const captured = !(out[k + 6] > 0.0f);
            if (r0 == 2.0f && std::fabs(sinBeta) > 0.05) {
                EXPECT_EQ(captured, sinBeta < 0.0) << "r=" << r0 << " ray " << i;
            }
            if (r0 > 2.0f) {
                EXPECT_FALSE(captured) << "r=" << r0 << " ray " << i;
            }
            if (captured) {
                continue;
            }
            ++accepted;
            /* R(r0) = vr^2 (E = 1) and |w|^2 = Q + Lz^2 on the equator. */
            double const q = out[k], lz = out[k + 1], vr = out[k + 2];
            double const p = (static_cast<double>(r0) * r0 + a * a) - a * lz;
            double const delta = static_cast<double>(r0) * r0 - 2.0 * r0 + a * a;
            double const rPot = p * p - delta * (q + (lz - a) * (lz - a));
            EXPECT_LT(std::fabs(rPot - vr * vr) / std::fmax(p * p, 1.0), 1e-4)
                << "r=" << r0 << " ray " << i;
            double const w2 = static_cast<double>(out[k + 3]) * out[k + 3] +
                              static_cast<double>(out[k + 4]) * out[k + 4] +
                              static_cast<double>(out[k + 5]) * out[k + 5];
            EXPECT_LT(std::fabs(w2 - (q + lz * lz)) / std::fmax(std::fabs(q) + lz * lz + a * a, 1.0),
                      1e-4)
                << "r=" << r0 << " ray " << i;
        }
        EXPECT_GT(accepted, 50) << "r=" << r0;
    }
}

TEST(CudaKerrGeodesic, DiskSegmentIntegratesTheGaussianColumn) {
    if (!cudaAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    /* Column flux g^3 sqrt(2 pi) h / cos(i) at r = 30 (x = 0.2, phi = 0);
     * 0.5% covers the radial flux variation the inclined ray sweeps. */
    double const x = 0.2;
    double const flux = x * x * x * (1.0 - std::sqrt(x));
    double const g = 1.0 + 0.3 * std::sqrt(1.0 / 30.0);
    float *dOut = nullptr;
    cudaMalloc(&dOut, sizeof(float));
    for (double const incl : {0.0, K_PI / 3.0}) {
        double const column = flux * g * g * g * std::sqrt(2.0 * K_PI) * 0.2 / std::cos(incl);
        for (float const seg : {0.02f, 0.2f, 2.0f, 20.0f}) {
            disk_slab_kernel<<<1, 1>>>(seg, static_cast<float>(incl), dOut);
            cudaDeviceSynchronize();
            float out = 0.0f;
            cudaMemcpy(&out, dOut, sizeof(float), cudaMemcpyDeviceToHost);
            EXPECT_NEAR(out, column, 5e-3 * column) << "incl=" << incl << " seg=" << seg;
        }
    }
    cudaFree(dOut);
}
