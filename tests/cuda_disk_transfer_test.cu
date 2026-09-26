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
 *
 * The traced-ray cases render a mirror pair of camera rays that land on the
 * approaching and receding sides of the disk through bh_launch_geodesic_kernel
 * (every kernel variant the device supports, and the baseline kernel's RTE
 * and Stokes paths) and hold each pixel to the double-precision reference
 * trace in tests/support/kerr_disk_reference.h.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>

#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include "cuda/device_disk_transfer.cuh"
#include "cuda/kernel_launch.h"
#include "cuda/kernel_registry.h"
#include "physics/disk_transfer.h"
#include "physics/page_thorne.h"
#include "support/kerr_disk_reference.h"

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

namespace {

/* Camera at (40, 0, 10) M in the physics frame, the two pixels of a 2x1
 * framebuffer tilted by atan(0.36) off the hole (u = -+fov_scale in
 * d_ray_dir): pixel 0 lands near r = 13 M on the approaching (-y) side,
 * pixel 1 on the receding side. In the two-ray kernels pixel 0 is hit0 and
 * pixel 1 is hit1. */
constexpr double K_CAMERA_DISTANCE_M = 40.0;
constexpr double K_CAMERA_HEIGHT_M = 10.0;
constexpr double K_FOV_SCALE = 0.36;

struct TraceCase {
    float spin;
    float rs;
};

/* Physics (spin along +z) to world (y up): the inverse of d_world_to_physics. */
std::array<float, 3> physicsToWorld(bhtest::Vec3d const& v) {
    return {static_cast<float>(v[0]), static_cast<float>(v[2]), static_cast<float>(-v[1])};
}

BH_LaunchParams mirrorLaunchParams(bhtest::MirrorPair const& pair, TraceCase c, int transferMode) {
    BH_LaunchParams p = {};
    p.rs = c.rs;
    p.spin = c.spin;
    p.isco = 0.5f * d_dt_isco_radius(c.spin) * c.rs;
    p.step_size = 0.02f;
    p.fov_scale = static_cast<float>(K_FOV_SCALE);
    p.max_dist = 100.0f * c.rs;
    p.max_steps = 20000;
    p.width = 2;
    p.height = 1;
    p.adisk_enabled = 1;
    p.kerr_enabled = 1;
    p.disk_peak_temperature = 10000.0f;
    p.disk_brightness = 1.0f;
    p.disk_flux_peak = static_cast<float>(physics::pageThorneFluxPeak(static_cast<double>(c.spin)));
    p.disk_transfer_mode = transferMode;

    std::array<float, 3> const cam = physicsToWorld(pair.cam);
    /* col0 = right = physics +y, col2 = forward; v = 0 for a one-row
     * framebuffer, so col1 only completes the frame. */
    std::array<float, 3> const right = physicsToWorld({0.0, 1.0, 0.0});
    std::array<float, 3> const fwd = physicsToWorld(pair.forward);
    std::array<float, 3> const up = {fwd[1] * right[2] - fwd[2] * right[1],
                                     fwd[2] * right[0] - fwd[0] * right[2],
                                     fwd[0] * right[1] - fwd[1] * right[0]};
    for (int k = 0; k < 3; ++k) {
        p.cam_pos[k] = cam[static_cast<std::size_t>(k)];
        p.cam_basis[k] = right[static_cast<std::size_t>(k)];
        p.cam_basis[3 + k] = up[static_cast<std::size_t>(k)];
        p.cam_basis[6 + k] = fwd[static_cast<std::size_t>(k)];
    }
    return p;
}

std::array<float4, 2> renderPair(BH_LaunchParams const& p, int variant) {
    std::array<float4, 2> host{};
    float4* d_fb = nullptr;
    if (cudaMalloc(&d_fb, sizeof(float4) * 2) != cudaSuccess) {
        ADD_FAILURE() << "cudaMalloc failed";
        return host;
    }
    int const rc = bh_launch_geodesic_kernel(d_fb, &p, variant, nullptr);
    EXPECT_EQ(rc, 0) << "variant " << variant;
    EXPECT_EQ(cudaDeviceSynchronize(), cudaSuccess);
    EXPECT_EQ(cudaMemcpy(host.data(), d_fb, sizeof(float4) * 2, cudaMemcpyDeviceToHost),
              cudaSuccess);
    cudaFree(d_fb);
    return host;
}

double luminance(float4 c) {
    return 0.2126729 * static_cast<double>(c.x) + 0.7151522 * static_cast<double>(c.y) +
           0.0721750 * static_cast<double>(c.z);
}

int deviceSm() {
    int major = 0;
    int minor = 0;
    cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0);
    cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0);
    return major * 10 + minor;
}

} // namespace

/* Each pixel's g, recovered as (Y_physical / Y_interstellar)^(1/4) from the
 * shipped kernel (the chroma has unit luminance and the trace is identical in
 * both modes), must equal physics::diskTransferG(r / M, a, lambda / M) with r
 * and lambda from the double-precision reference trace of the same camera
 * ray; the approaching pixel must have g > 1.05 and the receding one
 * g < 0.95. The Interstellar luminance must equal the Page-Thorne flux
 * F(r / M) / F_peak alone. The nonunit r_s cases scale the geometry with M,
 * so an M = 1 evaluation of the flux shape or of g misses by a factor of M in
 * r and lambda. Tolerances, about five times the deviations measured on
 * SM 8.9: g 5e-5 and flux 2e-4 for the FP32 kernels; 3e-3 and 2e-2 for the
 * FP16-storage kernels, whose half-precision ray state moves the crossing
 * (the flux falls as r^-3, tripling a radius error). A flipped lambda sign
 * moves g from about 1.23 to 0.68. */
TEST(CudaDiskTransfer, TracedDiskRaysCarryTheOrbitingEmitterShift) {
    if (!cudaDeviceAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    int const sm = deviceSm();
    for (TraceCase const c : {TraceCase{0.0f, 2.0f}, TraceCase{0.9f, 2.0f}, TraceCase{0.9f, 6.0f},
                              TraceCase{-0.6f, 1.0f}}) {
        double const spin = static_cast<double>(c.spin);
        double const rs = static_cast<double>(c.rs);
        double const m = 0.5 * rs;
        bhtest::MirrorPair const pair =
            bhtest::makeMirrorPair(rs, K_CAMERA_DISTANCE_M, K_CAMERA_HEIGHT_M, K_FOV_SCALE);
        double const peak = physics::pageThorneFluxPeak(spin);
        double const rIn = 0.5 * static_cast<double>(d_dt_isco_radius(c.spin)) * rs;
        std::array<bhtest::DiskHitReference, 2> refs{};
        for (std::size_t side = 0; side < 2; ++side) {
            refs[side] = bhtest::traceDiskHitReference(pair.cam, pair.dir[side], rs, spin, rIn,
                                                       100.0 * rs);
            ASSERT_TRUE(refs[side].hitDisk) << "a=" << spin << " rs=" << rs << " side " << side;
        }

        for (int variant = 0; variant < BH_KERNEL_COUNT; ++variant) {
            RtKernelInfo const* info = registry_get_info(variant);
            ASSERT_NE(info, nullptr);
            if (sm < info->min_sm) {
                continue;
            }
            bool const fp16 =
                variant == BH_KERNEL_FP16_STORAGE || variant == BH_KERNEL_FP16_H2_ILP;
            double const tolG = fp16 ? 3e-3 : 5e-5;
            double const tolFlux = fp16 ? 2e-2 : 2e-4;
            std::array<float4, 2> const physical =
                renderPair(mirrorLaunchParams(pair, c, 0), variant);
            std::array<float4, 2> const film = renderPair(mirrorLaunchParams(pair, c, 1), variant);
            for (std::size_t side = 0; side < 2; ++side) {
                bhtest::DiskHitReference const& ref = refs[side];
                float4 const px = physical[side];
                EXPECT_GT(px.x, 0.0f) << info->name << " side " << side;
                EXPECT_GT(px.y, 0.0f) << info->name << " side " << side;
                EXPECT_GT(px.z, 0.0f) << info->name << " side " << side;

                double const fluxNorm = physics::pageThorneFluxShape(ref.radius / m, spin) / peak;
                EXPECT_NEAR(luminance(film[side]) / fluxNorm, 1.0, tolFlux)
                    << info->name << " a=" << spin << " rs=" << rs << " side " << side;

                double const g = std::pow(luminance(px) / luminance(film[side]), 0.25);
                double const gRef = physics::diskTransferG(ref.radius / m, spin, ref.lambda / m);
                EXPECT_NEAR(g / gRef, 1.0, tolG)
                    << info->name << " a=" << spin << " rs=" << rs << " side " << side
                    << " g=" << g;
                if (side == 0) {
                    EXPECT_GT(g, 1.05) << info->name << " approaching, a=" << spin << " rs=" << rs;
                } else {
                    EXPECT_LT(g, 0.95) << info->name << " receding, a=" << spin << " rs=" << rs;
                }
            }
        }
    }
}

/* The baseline kernel's volumetric RTE and Stokes paths shade each disk step
 * with the photon's own lambda. At a = 0 the pair is exactly mirror
 * symmetric: with g = 1 both pixels match, and the physical shift makes the
 * approaching pixel brighter by more than 1.5x and bluer (larger B/R).
 * Optically thin (rte_opacity_scale 0), Faraday rotation off. */
TEST(CudaDiskTransfer, VolumetricTracesBrightenTheApproachingSide) {
    if (!cudaDeviceAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    TraceCase const c{0.0f, 2.0f};
    bhtest::MirrorPair const pair =
        bhtest::makeMirrorPair(2.0, K_CAMERA_DISTANCE_M, K_CAMERA_HEIGHT_M, K_FOV_SCALE);
    for (int path = 0; path < 2; ++path) {
        char const* const name = path == 0 ? "RTE" : "Stokes";
        BH_LaunchParams physical = mirrorLaunchParams(pair, c, 0);
        BH_LaunchParams film = mirrorLaunchParams(pair, c, 1);
        for (BH_LaunchParams* p : {&physical, &film}) {
            p->rte_enabled = path == 0 ? 1 : 0;
            p->stokes_enabled = path == 1 ? 1 : 0;
            p->rte_opacity_scale = 0.0f;
        }
        std::array<float4, 2> const ph = renderPair(physical, BH_KERNEL_FP32_BASELINE);
        std::array<float4, 2> const fm = renderPair(film, BH_KERNEL_FP32_BASELINE);
        ASSERT_GT(luminance(fm[0]), 0.0) << name;
        EXPECT_NEAR(luminance(fm[0]) / luminance(fm[1]), 1.0, 1e-5) << name;
        EXPECT_GT(luminance(ph[0]), 1.5 * luminance(ph[1])) << name;
        EXPECT_GT(static_cast<double>(ph[0].z / ph[0].x), static_cast<double>(ph[1].z / ph[1].x))
            << name;
    }
}

/* A camera in the disk plane (physics z = 0) at r = 15 inside the annulus,
 * both pixels leaving the plane away from the hole: no ray ever crosses the
 * plane, so every kernel variant must return the empty (black) sky rather
 * than the disk at the camera's own radius (d_check_disk counts a step that
 * starts on the plane as no crossing). */
TEST(CudaDiskTransfer, InPlaneCameraDoesNotHitTheDiskAtItsOwnPosition) {
    if (!cudaDeviceAvailable()) {
        GTEST_SKIP() << "No CUDA device";
    }
    int const sm = deviceSm();
    double const inv = 1.0 / std::sqrt(2.0);
    bhtest::MirrorPair pair;
    pair.cam = {15.0, 0.0, 0.0};
    pair.forward = {inv, 0.0, inv};
    for (int variant = 0; variant < BH_KERNEL_COUNT; ++variant) {
        RtKernelInfo const* info = registry_get_info(variant);
        ASSERT_NE(info, nullptr);
        if (sm < info->min_sm) {
            continue;
        }
        std::array<float4, 2> const px =
            renderPair(mirrorLaunchParams(pair, TraceCase{0.0f, 2.0f}, 0), variant);
        for (std::size_t side = 0; side < 2; ++side) {
            EXPECT_EQ(luminance(px[side]), 0.0) << info->name << " pixel " << side;
        }
    }
}
