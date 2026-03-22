/*
 * cuda_stokes_test.cu
 * Validates the CUDA polarized Stokes IQUV transport path (D4).
 *
 * WHY: d_stokes_step() implements an exact analytic solution for the simplified
 *      Mueller K matrix (alpha_I + rho_V) and d_trace_geodesic_stokes() wires it
 *      into the Kerr geodesic loop.  Incorrect rotation signs, branch cutoffs, or
 *      wrong FMA operand ordering are silent errors that violate the polarization
 *      invariant (I^2 >= Q^2 + U^2 + V^2) or produce wrong EVPA rotation.
 *
 * WHAT: Six tests:
 *   1. PureRotation:        no absorption, rho_V != 0 -> I preserved, EVPA rotates by rho_V*ds.
 *   2. PureAbsorption:      rho_V = 0 -> all IQUV decay exponentially toward equilibrium.
 *   3. PolBound:            I^2 >= Q^2 + U^2 + V^2 after many heterogeneous steps.
 *   4. RoundTrip:           +phi/2 then -phi/2 Faraday rotation restores original Q,U.
 *   5. ZeroInput:           state=0, emission=0 -> output=0 (pure identity).
 *   6. StokesKernelNoNaN:   launch baseline kernel with stokes_enabled=1; all pixels finite.
 *
 * HOW: Tests 1-5 call d_stokes_step() on device via a thin __global__ wrapper that
 *      writes results to a device buffer, then copies to host for assertion.
 *      Test 6 reuses the bh_launch_geodesic_kernel() C API with stokes_enabled=1.
 *      All tests skip gracefully when no CUDA device is present.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

#include "cuda/kernel_launch.h"
#include "cuda/device_physics.cuh"

/* ========================================================================
 * Device-side kernel wrapper for calling d_stokes_step from host tests
 * ======================================================================== */

/**
 * @brief Thin kernel: calls d_stokes_step() once and writes (i,q,u,v) to out[0..3].
 *
 * WHY: d_stokes_step() is __device__ __forceinline__; it cannot be called directly
 *      from host code.  A minimal __global__ wrapper lets host tests validate the
 *      exact device arithmetic through the CUDA API.
 */
__global__ void stokes_step_kernel(
    float si, float sq, float su, float sv,   /* input state */
    float jI, float jQ, float jU, float jV,   /* emission */
    float alphaI, float rhoV, float ds,        /* propagation */
    float *out)                                /* output: [i,q,u,v] */
{
    DStokes const s  = {si, sq, su, sv};
    DStokes const r  = d_stokes_step(s, jI, jQ, jU, jV, alphaI, rhoV, ds);
    out[0] = r.i;
    out[1] = r.q;
    out[2] = r.u;
    out[3] = r.v;
}

/** @brief Run one d_stokes_step on device and return result as host float[4]. */
static std::array<float, 4> run_stokes_step(
    float si, float sq, float su, float sv,
    float jI, float jQ, float jU, float jV,
    float alphaI, float rhoV, float ds)
{
    float *d_out = nullptr;
    cudaMalloc(&d_out, 4 * sizeof(float));

    stokes_step_kernel<<<1, 1>>>(si, sq, su, sv, jI, jQ, jU, jV, alphaI, rhoV, ds, d_out);
    cudaDeviceSynchronize();

    std::array<float, 4> h_out{};
    cudaMemcpy(h_out.data(), d_out, 4 * sizeof(float), cudaMemcpyDeviceToHost);
    cudaFree(d_out);
    return h_out;
}

/* ========================================================================
 * Helpers for the kernel-launch test
 * ======================================================================== */

static bool cuda_available() {
    int count = 0;
    return (cudaGetDeviceCount(&count) == cudaSuccess) && (count > 0);
}

static BH_LaunchParams make_stokes_params(int w, int h, int stokes_on,
                                           float b_angle = 0.0f,
                                           float ne_scale = 0.1f) {
    BH_LaunchParams p = {};
    p.rs             = 2.0f;
    p.spin           = 0.9f;
    p.isco           = 2.0f;
    p.step_size      = 0.05f;
    p.fov_scale      = 1.0f;
    p.max_dist       = 200.0f;
    p.max_steps      = 1000;
    p.width          = w;
    p.height         = h;
    p.adisk_enabled    = 1;
    p.redshift_enabled = 0;
    p.kerr_enabled     = 1;
    p.use_luts         = 0;
    p.cam_pos[0] = 0.0f; p.cam_pos[1] = 0.0f; p.cam_pos[2] = 20.0f;
    /* col2=(0,0,-1): center ray goes from z=20 toward BH at origin */
    p.cam_basis[0] = 1.0f; p.cam_basis[4] = 1.0f; p.cam_basis[8] = -1.0f;
    p.lut_radius_min       = p.isco;
    p.lut_radius_max       = 100.0f;
    p.redshift_radius_min  = p.isco;
    p.redshift_radius_max  = 100.0f;
    p.spectral_radius_min  = p.isco;
    p.spectral_radius_max  = 100.0f;
    p.doppler_strength     = 1.0f;
    p.background_intensity = 0.0f;
    p.background_enabled   = 0;
    p.wiregrid_enabled     = 0;
    p.wiregrid_show_ergo   = 0.0f;
    p.wiregrid_grid_scale  = 1.0f;
    p.grmhd_r_min          = 0.0f;
    p.grmhd_r_max          = 0.0f;
    p.rte_enabled          = 0;
    p.rte_opacity_scale    = 0.5f;
    p.grmhd_alpha          = 0.0f;
    p.stokes_enabled       = stokes_on;
    p.stokes_b_field_angle = b_angle;
    p.stokes_ne_scale      = ne_scale;
    return p;
}

static std::vector<float4> run_kernel(BH_LaunchParams p, int w, int h) {
    int const n = w * h;
    float4 *d_fb = nullptr;
    cudaMalloc(&d_fb, static_cast<std::size_t>(n) * sizeof(float4));
    bh_launch_geodesic_kernel(d_fb, &p, BH_KERNEL_FP32_BASELINE, nullptr);
    cudaDeviceSynchronize();
    std::vector<float4> host(static_cast<std::size_t>(n));
    cudaMemcpy(host.data(), d_fb,
               static_cast<std::size_t>(n) * sizeof(float4),
               cudaMemcpyDeviceToHost);
    cudaFree(d_fb);
    return host;
}

static bool all_finite(const std::vector<float4>& px) {
    for (auto const& p : px) {
        if (!std::isfinite(p.x) || !std::isfinite(p.y) ||
            !std::isfinite(p.z) || !std::isfinite(p.w)) {
            return false;
        }
    }
    return true;
}

/* ========================================================================
 * Test fixture
 * ======================================================================== */

class CudaStokesTest : public ::testing::Test {
protected:
    void SetUp() override {
        if (!cuda_available()) {
            GTEST_SKIP() << "No CUDA device available";
        }
    }
};

/* ========================================================================
 * Test 1: PureRotation
 *
 * With alphaI=0 and rhoV != 0, the I and V channels are unchanged (pure
 * emission = 0 case here), and (Q,U) rotate by angle phi = rhoV * ds in
 * the Q-U plane.
 *
 * Initial state: (I=1, Q=1, U=0, V=0), emission=0, alphaI=0, rhoV=pi/4, ds=1.
 * Expected:
 *   phi = pi/4
 *   Q_new = cos(pi/4) = 1/sqrt(2) ~ 0.70711
 *   U_new = sin(pi/4) = 1/sqrt(2) ~ 0.70711
 *   I_new = 1.0  (unchanged)
 *   V_new = 0.0  (unchanged)
 * ======================================================================== */
TEST_F(CudaStokesTest, PureRotation) {
    float const rhoV = static_cast<float>(M_PI) / 4.0f;
    float const ds   = 1.0f;
    auto r = run_stokes_step(1.0f, 1.0f, 0.0f, 0.0f,  /* state */
                              0.0f, 0.0f, 0.0f, 0.0f,  /* emission */
                              0.0f, rhoV, ds);           /* alpha=0 */

    float const phi     = rhoV * ds;
    float const q_exp   = cosf(phi);
    float const u_exp   = sinf(phi);
    float const tol     = 1.0e-5f;

    EXPECT_NEAR(r[0], 1.0f,  tol) << "I should be unchanged under pure rotation";
    EXPECT_NEAR(r[1], q_exp, tol) << "Q should rotate by rhoV*ds";
    EXPECT_NEAR(r[2], u_exp, tol) << "U should rotate by rhoV*ds";
    EXPECT_NEAR(r[3], 0.0f,  tol) << "V should be unchanged under pure rotation";
}

/* ========================================================================
 * Test 2: PureAbsorption
 *
 * With rhoV=0 and emission=0, all Stokes components decay exponentially:
 *   X_new = X * exp(-alphaI * ds)
 *
 * Initial state: (I=1, Q=0.6, U=0.3, V=0.1)
 * alphaI=2.0, ds=0.5 -> tau=1.0, factor=exp(-1)=0.36788
 * ======================================================================== */
TEST_F(CudaStokesTest, PureAbsorption) {
    float const alphaI = 2.0f;
    float const ds     = 0.5f;
    float const tau    = alphaI * ds;
    float const factor = expf(-tau);

    auto r = run_stokes_step(1.0f, 0.6f, 0.3f, 0.1f,  /* state */
                              0.0f, 0.0f, 0.0f, 0.0f,  /* emission */
                              alphaI, 0.0f, ds);

    float const tol = 1.0e-5f;
    EXPECT_NEAR(r[0], 1.0f * factor, tol) << "I decays by exp(-alphaI*ds)";
    EXPECT_NEAR(r[1], 0.6f * factor, tol) << "Q decays by exp(-alphaI*ds)";
    EXPECT_NEAR(r[2], 0.3f * factor, tol) << "U decays by exp(-alphaI*ds)";
    EXPECT_NEAR(r[3], 0.1f * factor, tol) << "V decays by exp(-alphaI*ds)";
}

/* ========================================================================
 * Test 3: PolBound
 *
 * After a sequence of steps (absorption + rotation + emission), the
 * polarization invariant I^2 >= Q^2 + U^2 + V^2 must hold.
 *
 * We run 20 steps with non-trivial emission and Faraday rotation, then
 * check that the final state satisfies the bound.
 * ======================================================================== */
TEST_F(CudaStokesTest, PolBound) {
    /* 20 sequential step() calls with moderate emission and rotation */
    float const alphaI = 0.3f;
    float const rhoV   = 0.8f;
    float const ds     = 0.1f;
    float const jI     = 1.0f;
    float const jQ     = -0.5f;   /* 50% linear polarization toward Q */
    float const jU     = 0.0f;
    float const jV     = 0.0f;

    /* Build a multi-step kernel via a simple loop on device */
    struct StokesMultiStepParams {
        float si, sq, su, sv;
        float jI, jQ, jU, jV;
        float alphaI, rhoV, ds;
        int steps;
    };

    auto state = run_stokes_step(0.0f, 0.0f, 0.0f, 0.0f,
                                  jI, jQ, jU, jV, alphaI, rhoV, ds);
    for (int k = 1; k < 20; ++k) {
        state = run_stokes_step(state[0], state[1], state[2], state[3],
                                 jI, jQ, jU, jV, alphaI, rhoV, ds);
    }

    float const I = state[0];
    float const Q = state[1];
    float const U = state[2];
    float const V = state[3];

    EXPECT_GE(I, 0.0f) << "I must be non-negative";
    EXPECT_GE(I * I + 1.0e-6f, Q * Q + U * U + V * V)
        << "Polarization bound I^2 >= Q^2 + U^2 + V^2 violated after 20 steps";
}

/* ========================================================================
 * Test 4: RoundTrip
 *
 * Rotating by +phi and then -phi should restore the original Q and U
 * (up to floating-point rounding).
 *
 * Using state (I=1, Q=1, U=0, V=0), phi = pi/6.
 * After forward rotation: Q ~ cos(pi/6), U ~ sin(pi/6).
 * After backward rotation: Q ~ 1, U ~ 0.
 * ======================================================================== */
TEST_F(CudaStokesTest, RoundTrip) {
    float const phi = static_cast<float>(M_PI) / 6.0f;
    float const ds  = 1.0f;

    auto forward = run_stokes_step(1.0f, 1.0f, 0.0f, 0.0f,
                                    0.0f, 0.0f, 0.0f, 0.0f,
                                    0.0f, +phi, ds);
    auto roundtrip = run_stokes_step(forward[0], forward[1], forward[2], forward[3],
                                      0.0f, 0.0f, 0.0f, 0.0f,
                                      0.0f, -phi, ds);

    float const tol = 1.0e-5f;
    EXPECT_NEAR(roundtrip[0], 1.0f, tol) << "I unchanged after +phi then -phi rotation";
    EXPECT_NEAR(roundtrip[1], 1.0f, tol) << "Q restored after round-trip rotation";
    EXPECT_NEAR(roundtrip[2], 0.0f, tol) << "U restored after round-trip rotation";
    EXPECT_NEAR(roundtrip[3], 0.0f, tol) << "V unchanged after +phi then -phi rotation";
}

/* ========================================================================
 * Test 5: ZeroInput
 *
 * With state=0 and emission=0, the output must be exactly (0,0,0,0)
 * regardless of alphaI and rhoV.  This verifies there are no spurious
 * additive constants in the propagation formula.
 * ======================================================================== */
TEST_F(CudaStokesTest, ZeroInput) {
    auto r = run_stokes_step(0.0f, 0.0f, 0.0f, 0.0f,
                              0.0f, 0.0f, 0.0f, 0.0f,
                              1.5f, 2.3f, 0.4f);

    float const tol = 1.0e-7f;
    EXPECT_NEAR(r[0], 0.0f, tol) << "I should be 0 when state and emission are both 0";
    EXPECT_NEAR(r[1], 0.0f, tol) << "Q should be 0 when state and emission are both 0";
    EXPECT_NEAR(r[2], 0.0f, tol) << "U should be 0 when state and emission are both 0";
    EXPECT_NEAR(r[3], 0.0f, tol) << "V should be 0 when state and emission are both 0";
}

/* ========================================================================
 * Test 6: StokesKernelNoNaN
 *
 * Launch the FP32 baseline kernel with stokes_enabled=1.  All pixels in
 * the 32x32 framebuffer must be finite (no NaN, no Inf).
 *
 * WHY: The stokes path calls sinf/cosf/sqrtf/atan2f on accumulated Stokes
 *      components; NaN-propagation from a division-by-zero or an out-of-range
 *      acosf would otherwise be invisible without a pixel sweep.
 * ======================================================================== */
TEST_F(CudaStokesTest, StokesKernelNoNaN) {
    int const W = 32, H = 32;
    BH_LaunchParams p = make_stokes_params(W, H, /*stokes_on=*/1,
                                            /*b_angle=*/0.3f, /*ne_scale=*/0.1f);
    auto pixels = run_kernel(p, W, H);

    EXPECT_TRUE(all_finite(pixels))
        << "Stokes kernel produced NaN or Inf in at least one pixel";

    /* At least some pixels must be non-black (disk emitting) */
    int nonzero = 0;
    for (auto const& px : pixels) {
        if (px.x > 1.0e-4f || px.y > 1.0e-4f || px.z > 1.0e-4f) {
            ++nonzero;
        }
    }
    EXPECT_GT(nonzero, 0) << "Stokes kernel with disk enabled must produce some non-black pixels";
}
