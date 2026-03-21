/*
 * cuda_geodesic_orbit_test.cu
 *
 * WHY: G4 -- validate that d_kerr_r_analytic produces orbits that satisfy the
 *      radial constraint R(r) >= 0 at all affine parameters, and that the
 *      analytic solution agrees with direct RK4 integration of the geodesic
 *      ODE (dr/dlambda)^2 = R(r).
 *
 * WHY the seeding strategy: The ODE dr/dlambda = +sqrt(R(r)) has a square-root
 *      branch point at the turning points r3 and r2 where R=0.  RK4 started
 *      exactly at r3 is permanently stuck (all k_i = sqrt(R(r3)) = 0, so the
 *      orbit never leaves the turning point).  We therefore seed the RK4 from
 *      the analytic formula at lambda_start = 0.1*half_T (10% into the orbit,
 *      well away from both turning points) and integrate forward over
 *      [0.1, 0.9]*half_T.  This tests RK4 consistency with the analytic ODE.
 *
 * WHAT: Five orbit configurations with analytically known roots (sum = 0):
 *   Type 1: r1=4, r2=2, r3=1, r4=-7   m_DA ~ 0.59  (baseline)
 *   Type 2: r1=4, r2=3, r3=1, r4=-8   m_DA ~ 0.27  (outer orbit tighter)
 *   Type 3: r1=5, r2=2, r3=1, r4=-8   m_DA ~ 0.68  (wide outer gap)
 *   Type 4: r1=3, r2=2, r3=1, r4=-6   m_DA ~ 0.44  (compact)
 *   Type 5: r1=4, r2=3, r3=2, r4=-9   m_DA ~ 0.46  (tight inner orbit)
 *
 * Per-orbit checks:
 *   1. d_quartic_real_roots recovers all 4 roots within 5e-3.
 *   2. 30 sample points on the analytic orbit satisfy R(r) >= -1e-3.
 *   3. r(lambda0 + half_T) = r2 (outer turning point) to 5e-3.
 *   4. RK4 seeded at 10% of half_T, integrated over 80%, RMSE < 2e-3.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>

#include "cuda/device_analytic_kerr.cuh"

/* ============================================================================
 * CUDA availability helper
 * ============================================================================ */

static bool cuda_device_available()
{
    int count = 0;
    return (cudaGetDeviceCount(&count) == cudaSuccess) && (count > 0);
}

#define SKIP_IF_NO_CUDA() \
    do { if (!cuda_device_available()) GTEST_SKIP() << "No CUDA device"; } while (0)

/* ============================================================================
 * Device helpers
 * ============================================================================ */

/* Radial potential from explicit roots: R(r) = (r-r1)(r-r2)(r-r3)(r-r4). */
__device__ __forceinline__ float d_R_from_roots(float r,
        float r1, float r2, float r3, float r4)
{
    return (r - r1) * (r - r2) * (r - r3) * (r - r4);
}

/* One RK4 step for dr/dlambda = +sqrt(max(0, R(r))). */
__device__ __forceinline__ float d_rk4_step(float r, float h,
        float r1, float r2, float r3, float r4)
{
    float k1 = sqrtf(fmaxf(0.0f, d_R_from_roots(r,              r1,r2,r3,r4)));
    float k2 = sqrtf(fmaxf(0.0f, d_R_from_roots(r+0.5f*h*k1,   r1,r2,r3,r4)));
    float k3 = sqrtf(fmaxf(0.0f, d_R_from_roots(r+0.5f*h*k2,   r1,r2,r3,r4)));
    float k4 = sqrtf(fmaxf(0.0f, d_R_from_roots(r+h*k3,         r1,r2,r3,r4)));
    return r + (h / 6.0f) * (k1 + 2.0f*k2 + 2.0f*k3 + k4);
}

/* ============================================================================
 * Orbit parity kernel
 *
 * Output layout (9 floats):
 *   [0]   nreal (float)
 *   [1..4] roots r1, r2, r3, r4
 *   [5]   half_T
 *   [6]   RMSE(analytic, RK4) over [0.1, 0.9]*half_T (N_RK4=500 steps)
 *   [7]   max R-constraint violation: max(-R(r_a)) over 30 sample points
 *   [8]   r_analytic(lambda0 + half_T)  -- should equal r2
 * ============================================================================ */

static const int N_RK4    = 500;
static const int N_SAMPLE = 30;

__global__ void k_orbit_parity(float c2, float c1, float c0, float* out)
{
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    /* Root finding */
    float roots[4] = {0,0,0,0};
    int nreal = d_quartic_real_roots(c2, c1, c0, roots);
    out[0] = (float)nreal;
    out[1] = roots[0]; out[2] = roots[1];
    out[3] = roots[2]; out[4] = roots[3];

    if (nreal != 4) {
        out[5] = out[6] = out[7] = out[8] = -1.0f;
        return;
    }

    float r1 = roots[0], r2 = roots[1], r3 = roots[2], r4 = roots[3];
    const float lambda0 = 0.0f;

    float half_T = d_kerr_radial_half_period(r1, r2, r3, r4);
    out[5] = half_T;

    /* r(half_T) = r2 boundary condition */
    out[8] = d_kerr_r_analytic(lambda0 + half_T, r1, r2, r3, r4, lambda0);

    if (half_T <= 0.0f) {
        out[6] = out[7] = -1.0f;
        return;
    }

    /* --- Constraint check: R(r_analytic) >= 0 at N_SAMPLE points --- */
    float max_viol = 0.0f;
    for (int i = 0; i <= N_SAMPLE; i++) {
        float lam = lambda0 + (float)i / (float)N_SAMPLE * half_T;
        float r_a = d_kerr_r_analytic(lam, r1, r2, r3, r4, lambda0);
        float R   = d_R_from_roots(r_a, r1, r2, r3, r4);
        if (R < 0.0f)
            max_viol = fmaxf(max_viol, -R);
    }
    out[7] = max_viol;

    /* --- RK4 parity over interior [0.1, 0.9] * half_T ---
     *
     * WHY skip turning points: R(r3)=R(r2)=0 makes dr/dlambda=0 there.
     * RK4 started exactly at a turning point is permanently stuck since
     * all four RK4 slopes k_i = sqrt(R(r)) = 0 and the state never evolves.
     * Starting at 10% into the orbit avoids both singularities while still
     * covering the physically important interior of the bound orbit.
     */
    float lam_start = 0.1f * half_T;
    float lam_end   = 0.9f * half_T;
    float dt        = (lam_end - lam_start) / (float)N_RK4;

    /* Seed RK4 from analytic at lam_start -- tests ODE consistency */
    float r_num = d_kerr_r_analytic(lam_start, r1, r2, r3, r4, lambda0);
    float lambda = lam_start;

    float sum_sq = 0.0f;
    int   n_cmp  = 0;
    int   chk_interval = N_RK4 / N_SAMPLE; /* ~16 steps/checkpoint */

    for (int step = 0; step < N_RK4; step++) {
        if (step % chk_interval == 0) {
            float r_a  = d_kerr_r_analytic(lambda, r1, r2, r3, r4, lambda0);
            float diff = r_num - r_a;
            sum_sq += diff * diff;
            n_cmp++;
        }
        r_num   = d_rk4_step(r_num, dt, r1, r2, r3, r4);
        lambda += dt;
    }

    out[6] = (n_cmp > 0) ? sqrtf(sum_sq / (float)n_cmp) : -1.0f;
}

/* ============================================================================
 * Test fixture
 * ============================================================================ */

class GeodeticOrbitTest : public ::testing::Test {
protected:
    void SetUp() override { SKIP_IF_NO_CUDA(); }

    void run_orbit(float c2, float c1, float c0, float (&out)[9]) {
        float* d_out = nullptr;
        ASSERT_EQ(cudaMalloc(&d_out, 9 * sizeof(float)), cudaSuccess);
        ASSERT_EQ(cudaMemset(d_out, 0, 9 * sizeof(float)), cudaSuccess);
        k_orbit_parity<<<1,1>>>(c2, c1, c0, d_out);
        ASSERT_EQ(cudaDeviceSynchronize(), cudaSuccess);
        ASSERT_EQ(cudaMemcpy(out, d_out, 9 * sizeof(float),
                             cudaMemcpyDeviceToHost), cudaSuccess);
        cudaFree(d_out);
    }

    void check_orbit(const char* label,
                     float c2, float c1, float c0,
                     float exp_r1, float exp_r2,
                     float exp_r3, float exp_r4)
    {
        float out[9];
        run_orbit(c2, c1, c0, out);

        int nreal = (int)(out[0] + 0.5f);
        ASSERT_EQ(nreal, 4) << label << ": expected 4 real roots";

        EXPECT_NEAR(out[1], exp_r1, 5.0e-3f) << label << " r1";
        EXPECT_NEAR(out[2], exp_r2, 5.0e-3f) << label << " r2";
        EXPECT_NEAR(out[3], exp_r3, 5.0e-3f) << label << " r3";
        EXPECT_NEAR(out[4], exp_r4, 1.0e-2f) << label << " r4";

        float half_T = out[5];
        EXPECT_GT(half_T, 0.0f) << label << ": half_T > 0";

        /* R(r) >= 0 at all sample points */
        EXPECT_LE(out[7], 1.0e-3f) << label << ": R(r) >= -1e-3 (orbit in allowed region)";

        /* r(lambda0 + half_T) = r2 (outer turning point) */
        EXPECT_NEAR(out[8], exp_r2, 5.0e-3f) << label << ": r(T/2) = r2";

        /* RK4 vs analytic RMSE over interior 80% of orbit */
        float rmse = out[6];
        EXPECT_GE(rmse, 0.0f)    << label << ": valid RMSE";
        EXPECT_LE(rmse, 2.0e-3f) << label << ": RMSE analytic vs RK4 (interior 80%)";
    }
};

/* ============================================================================
 * Test 1: baseline -- r1=4, r2=2, r3=1, r4=-7
 *   c2=-35, c1=90, c0=-56   m_DA=16/27~0.593
 * ============================================================================ */

TEST_F(GeodeticOrbitTest, OrbitType1_Baseline)
{
    check_orbit("Type1_Baseline", -35.0f, 90.0f, -56.0f,
                4.0f, 2.0f, 1.0f, -7.0f);
}

/* ============================================================================
 * Test 2: outer orbit tighter -- r1=4, r2=3, r3=1, r4=-8
 *   c2=-45, c1=140, c0=-96   m_DA=9/33~0.273
 * ============================================================================ */

TEST_F(GeodeticOrbitTest, OrbitType2_OuterTighter)
{
    check_orbit("Type2_OuterTighter", -45.0f, 140.0f, -96.0f,
                4.0f, 3.0f, 1.0f, -8.0f);
}

/* ============================================================================
 * Test 3: wide outer gap -- r1=5, r2=2, r3=1, r4=-8
 *   c2=-47, c1=126, c0=-80   m_DA=27/40=0.675
 * ============================================================================ */

TEST_F(GeodeticOrbitTest, OrbitType3_WideOuterGap)
{
    check_orbit("Type3_WideOuterGap", -47.0f, 126.0f, -80.0f,
                5.0f, 2.0f, 1.0f, -8.0f);
}

/* ============================================================================
 * Test 4: compact -- r1=3, r2=2, r3=1, r4=-6
 *   c2=-25, c1=60, c0=-36   m_DA=7/16=0.4375
 * ============================================================================ */

TEST_F(GeodeticOrbitTest, OrbitType4_Compact)
{
    check_orbit("Type4_Compact", -25.0f, 60.0f, -36.0f,
                3.0f, 2.0f, 1.0f, -6.0f);
}

/* ============================================================================
 * Test 5: tight inner -- r1=4, r2=3, r3=2, r4=-9
 *   c2=-55, c1=210, c0=-216   m_DA=11/24~0.458
 * ============================================================================ */

TEST_F(GeodeticOrbitTest, OrbitType5_TightInner)
{
    check_orbit("Type5_TightInner", -55.0f, 210.0f, -216.0f,
                4.0f, 3.0f, 2.0f, -9.0f);
}
