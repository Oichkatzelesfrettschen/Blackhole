/*
 * cuda_analytic_kerr_test.cu
 *
 * WHY: device_analytic_kerr.cuh implements the Jacobi elliptic functions,
 *      quartic root finder, and analytic radial geodesic solution used for
 *      O(1) ray tracing of high-order photon rings.  These tests validate
 *      the AGM algorithm, Ferrari root finding, and the r(lambda) formula
 *      against analytically known values before the code is used in production
 *      kernels.
 *
 * WHAT: Tests launch minimal device kernels that call __device__ functions
 *       from device_analytic_kerr.cuh and write results to device buffers.
 *       The host then checks values against reference solutions.
 *
 *   1. EllpjAtZero          -- sn(0,m)=0, cn(0,m)=1, dn(0,m)=1 for m=0.25
 *   2. EllpjSmallModulus    -- m=1e-4: sn/cn/dn converge to sin/cos/1
 *   3. EllpjQuarterPeriod   -- sn(K(k), m=k^2) = 1, cn = 0 for k=0.5
 *   4. EllintKPiOver2       -- K(0) = pi/2 = 1.5707963...
 *   5. ProgradePhotonOrbit  -- a=0 gives r_ph=3; a=0.9 gives r_ph~1.565
 *   6. AnalyticRadialRound  -- r(0)=r3 and r(T/2)=r1 for a transit orbit
 *
 * HOW: Each test allocates a small device float buffer, launches a 1-thread
 *      kernel, copies to host, and asserts with EXPECT_NEAR.
 *      All tests skip gracefully if no CUDA device is available.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

/* Include device headers directly -- safe because device_analytic_kerr.cuh
 * defines only __device__ functions and no __constant__ symbols. */
#include "cuda/device_analytic_kerr.cuh"

/* ============================================================================
 * Helper: skip test if no CUDA device
 * ============================================================================ */

static bool cuda_device_available()
{
    int count = 0;
    return (cudaGetDeviceCount(&count) == cudaSuccess) && (count > 0);
}

#define SKIP_IF_NO_CUDA() \
    do { if (!cuda_device_available()) GTEST_SKIP() << "No CUDA device"; } while (0)

/* ============================================================================
 * Test kernels
 * ============================================================================ */

/* Kernel 1: d_ellpj at u=0 */
__global__ void k_ellpj_at_zero(float m, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    float sn, cn, dn;
    d_ellpj(0.0f, m, &sn, &cn, &dn);
    out[0] = sn; out[1] = cn; out[2] = dn;
}

/* Kernel 2: d_ellpj at general u, m */
__global__ void k_ellpj(float u, float m, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    float sn, cn, dn;
    d_ellpj(u, m, &sn, &cn, &dn);
    out[0] = sn; out[1] = cn; out[2] = dn;
}

/* Kernel 3: d_ellint_K */
__global__ void k_ellint_K(float k, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    out[0] = d_ellint_K(k);
}

/* Kernel 4: d_prograde_photon_orbit */
__global__ void k_prograde_photon_orbit(float a, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    out[0] = d_prograde_photon_orbit(a);
}

/* Kernel 5: d_kerr_r_analytic at lambda=0 and lambda=half_period */
__global__ void k_analytic_radial(
        float r1, float r2, float r3, float r4,
        float lambda0, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    /* r(lambda0) should equal r3 (inner turning point) */
    out[0] = d_kerr_r_analytic(lambda0, r1, r2, r3, r4, lambda0);
    /* r(lambda0 + half_period) should equal r1 (outer turning point) */
    float half_T = d_kerr_radial_half_period(r1, r2, r3, r4);
    out[1] = d_kerr_r_analytic(lambda0 + half_T, r1, r2, r3, r4, lambda0);
    out[2] = half_T;
}

/* Kernel 6: d_quartic_real_roots -- write nreal + up to 4 roots */
__global__ void k_quartic_roots(float c2, float c1, float c0, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;
    float roots[4] = {0.0f, 0.0f, 0.0f, 0.0f};
    int nreal = d_quartic_real_roots(c2, c1, c0, roots);
    out[0] = (float)nreal;
    out[1] = roots[0]; out[2] = roots[1];
    out[3] = roots[2]; out[4] = roots[3];
}

/* ============================================================================
 * Test fixture
 * ============================================================================ */

class AnalyticKerrTest : public ::testing::Test {
protected:
    void SetUp() override { SKIP_IF_NO_CUDA(); }

    /* Allocate device buffer, run kernel, copy back, free. */
    template<int N, typename KernelLaunch>
    void run_kernel(KernelLaunch&& launch, float (&out)[N]) {
        float* d_out = nullptr;
        ASSERT_EQ(cudaMalloc(&d_out, N * sizeof(float)), cudaSuccess);
        ASSERT_EQ(cudaMemset(d_out, 0, N * sizeof(float)), cudaSuccess);
        launch(d_out);
        ASSERT_EQ(cudaDeviceSynchronize(), cudaSuccess);
        ASSERT_EQ(cudaMemcpy(out, d_out, N * sizeof(float),
                             cudaMemcpyDeviceToHost), cudaSuccess);
        cudaFree(d_out);
    }
};

/* ============================================================================
 * Test 1: sn(0|m) = 0, cn(0|m) = 1, dn(0|m) = 1
 * ============================================================================ */

TEST_F(AnalyticKerrTest, EllpjAtZero)
{
    float out[3];
    run_kernel<3>([](float* d) { k_ellpj_at_zero<<<1,1>>>(0.25f, d); }, out);

    EXPECT_NEAR(out[0], 0.0f, 1.0e-6f); /* sn(0|m) = 0 */
    EXPECT_NEAR(out[1], 1.0f, 1.0e-6f); /* cn(0|m) = 1 */
    EXPECT_NEAR(out[2], 1.0f, 1.0e-6f); /* dn(0|m) = 1 */
}

/* ============================================================================
 * Test 2: small-modulus limit: sn -> sin, cn -> cos, dn -> 1
 * ============================================================================ */

TEST_F(AnalyticKerrTest, EllpjSmallModulus)
{
    /* m = 1e-4, u = 1.0: sn(1, 0.01) ~ sin(1), cn(1, 0.01) ~ cos(1) */
    float out[3];
    float u = 1.0f;
    float m = 1.0e-4f;
    run_kernel<3>([u, m](float* d) { k_ellpj<<<1,1>>>(u, m, d); }, out);

    EXPECT_NEAR(out[0], sinf(u),  2.0e-4f); /* sn */
    EXPECT_NEAR(out[1], cosf(u),  2.0e-4f); /* cn */
    EXPECT_NEAR(out[2], 1.0f,     2.0e-4f); /* dn */
}

/* ============================================================================
 * Test 3: sn(K(k), m=k^2) = 1, cn(K(k), m=k^2) = 0  (quarter period)
 * ============================================================================ */

TEST_F(AnalyticKerrTest, EllpjQuarterPeriod)
{
    /* k = 0.5, m = k^2 = 0.25, K(0.5) ~ 1.6858 */
    float k_out[1];
    run_kernel<1>([](float* d) { k_ellint_K<<<1,1>>>(0.5f, d); }, k_out);
    float K = k_out[0];

    /* sn(K, m=0.25) should equal 1.0 */
    float out[3];
    float m = 0.25f;
    run_kernel<3>([K, m](float* d) { k_ellpj<<<1,1>>>(K, m, d); }, out);

    EXPECT_NEAR(out[0], 1.0f, 1.0e-4f);  /* sn = 1 at quarter period */
    EXPECT_NEAR(out[1], 0.0f, 1.0e-4f);  /* cn = 0 at quarter period */
    /* dn(K, k) = sqrt(1-k^2) = sqrt(0.75) ~ 0.866 */
    EXPECT_NEAR(out[2], sqrtf(0.75f), 1.0e-4f);
}

/* ============================================================================
 * Test 4: K(0) = pi/2
 * ============================================================================ */

TEST_F(AnalyticKerrTest, EllintKPiOver2)
{
    float out[1];
    run_kernel<1>([](float* d) { k_ellint_K<<<1,1>>>(0.0f, d); }, out);

    EXPECT_NEAR(out[0], 1.5707963268f, 1.0e-6f);
}

/* ============================================================================
 * Test 5: prograde photon orbit radii
 * ============================================================================ */

TEST_F(AnalyticKerrTest, ProgradePhotonOrbit)
{
    /* Schwarzschild: a=0 => r_ph = 3 */
    float out_sch[1];
    run_kernel<1>([](float* d) { k_prograde_photon_orbit<<<1,1>>>(0.0f, d); }, out_sch);
    EXPECT_NEAR(out_sch[0], 3.0f, 1.0e-5f);

    /* Kerr a=1 extremal prograde: r_ph = 1 */
    float out_ext[1];
    run_kernel<1>([](float* d) { k_prograde_photon_orbit<<<1,1>>>(1.0f, d); }, out_ext);
    EXPECT_NEAR(out_ext[0], 1.0f, 1.0e-4f);

    /* Kerr a=0.9: r_ph = 2*(1+cos(2/3*acos(-0.9))) */
    float ref = 2.0f * (1.0f + cosf((2.0f / 3.0f) * acosf(-0.9f)));
    float out_k09[1];
    run_kernel<1>([](float* d) { k_prograde_photon_orbit<<<1,1>>>(0.9f, d); }, out_k09);
    EXPECT_NEAR(out_k09[0], ref, 1.0e-5f);
}

/* ============================================================================
 * Test 6: r(lambda=0) = r3, r(lambda=T/2) = r1 for a transit orbit
 * ============================================================================ */

TEST_F(AnalyticKerrTest, AnalyticRadialRoundTrip)
{
    /* Construct a depressed quartic with analytically known roots.
     *
     * For r^4 + c2*r^2 + c1*r + c0 = (r-r1)(r-r2)(r-r3)(r-r4) the
     * coefficient of r^3 must be 0, i.e. r1+r2+r3+r4 = 0.
     *
     * Choose: r1=4, r2=2, r3=1, r4=-7  (sum = 0)
     *   c2 = sum of products of pairs = 8+4-28+2-14-7 = -35
     *   c1 = -(sum of triple products) = -(8-56-28-14) = 90
     *   c0 = r1*r2*r3*r4 = 4*2*1*(-7) = -56
     *
     * Verified: R(4)=R(2)=R(1)=R(-7)=0 algebraically.
     */
    float c2 = -35.0f, c1 = 90.0f, c0 = -56.0f;

    float roots_out[5];
    run_kernel<5>([c2, c1, c0](float* d) {
        k_quartic_roots<<<1,1>>>(c2, c1, c0, d);
    }, roots_out);

    int nreal = (int)(roots_out[0] + 0.5f); /* round float->int */
    ASSERT_EQ(nreal, 4) << "Expected 4 real roots for constructed quartic";

    float r1 = roots_out[1], r2 = roots_out[2];
    float r3 = roots_out[3], r4 = roots_out[4];

    /* Verify the recovered roots match the known values (loose tol for FP32) */
    EXPECT_NEAR(r1,  4.0f, 1.0e-3f);
    EXPECT_NEAR(r2,  2.0f, 1.0e-3f);
    EXPECT_NEAR(r3,  1.0f, 1.0e-3f);
    EXPECT_NEAR(r4, -7.0f, 5.0e-3f);

    /* r(lambda0)     = r3 (inner turning point, sn=0) */
    /* r(lambda0+T/2) = r1 (outer turning point, sn=1) */
    float rad_out[3];
    run_kernel<3>([r1, r2, r3, r4](float* d) {
        k_analytic_radial<<<1,1>>>(r1, r2, r3, r4, 0.0f, d);
    }, rad_out);

    EXPECT_NEAR(rad_out[0], r3, 1.0e-3f); /* r(lambda0) = r3 */
    EXPECT_NEAR(rad_out[1], r1, 1.0e-3f); /* r(lambda0 + T/2) = r1 */
    EXPECT_GT(rad_out[2], 0.0f);          /* half_period > 0 */
}
