/**
 * @file device_analytic_kerr.cuh
 * @brief CUDA device functions for analytic Kerr null geodesics.
 *
 * WHY: Numerical RK4 integration is O(N) per ray with N~1000 steps for
 *      photon-sphere orbits. Analytic solutions via Jacobi elliptic functions
 *      evaluate r(lambda) in O(1) -- approximately 1000x faster for
 *      high-order photon ring rays (n >= 1).
 *
 * WHAT: Port of src/physics/analytic_kerr_geodesic.h to CUDA __device__ code.
 *       The Boost.Math dependency (jacobi_sn, ellint_1) is replaced with a
 *       self-contained AGM-based implementation following the Cephes library
 *       algorithm (Moshier 1989, ellpj.c) adapted for FP32 device code.
 *
 * HOW: All functions are __device__ __forceinline__ or __device__ only.
 *      No __constant__ symbols are defined here (safe to include from
 *      multiple .cu translation units). No STL, no Boost, no complex<>.
 *
 * References:
 *   - Dyson (2023), arXiv:2302.03704 -- plunging Kerr geodesics
 *   - Gralla & Lupsasca (2020), PRD 101 -- null geodesic classification
 *   - Moshier (1989), Cephes Math Library -- ellpj.c (AGM algorithm)
 *   - Abramowitz & Stegun (1964), Chapter 16-17
 */

#ifndef DEVICE_ANALYTIC_KERR_CUH
#define DEVICE_ANALYTIC_KERR_CUH

#include <cuda_runtime.h>
#include <math.h>

/* ============================================================================
 * Jacobi Elliptic Functions via AGM -- Cephes algorithm (FP32)
 * ============================================================================ */

/**
 * @brief Compute Jacobi elliptic functions sn(u|m), cn(u|m), dn(u|m).
 *
 * Uses the descending Landen / arithmetic-geometric mean algorithm from
 * the Cephes library (ellpj.c, Moshier 1989), adapted for single precision.
 *
 * Convergence: quadratic; ~8 iterations for FP32 (MACHEP = 1.19e-7).
 *
 * @param u   Argument (real, any range)
 * @param m   Parameter m = k^2, the elliptic modulus squared (0 <= m <= 1)
 * @param sn  Output: sn(u|m)
 * @param cn  Output: cn(u|m)
 * @param dn  Output: dn(u|m)
 */
__device__ void d_ellpj(float u, float m, float* sn, float* cn, float* dn)
{
    /* Special case: m ~ 0 => trigonometric limit */
    if (m < 1.0e-8f) {
        float s, c;
        sincosf(u, &s, &c);
        *sn = s;
        *cn = c;
        *dn = 1.0f;
        return;
    }
    /* Special case: m ~ 1 => hyperbolic limit */
    if (m >= 1.0f - 1.0e-8f) {
        float th = tanhf(u);
        float sech = 1.0f / coshf(u);
        *sn = th;
        *cn = sech;
        *dn = sech;
        return;
    }

    /* --- Forward AGM pass: build sequences a[i], c[i] --- */
    /* a[0] = 1, b = sqrt(1-m) = k', c[0] = sqrt(m) = k  */
    /* a[n+1] = (a[n]+b)/2,  b = sqrt(a[n]*b),  c[n+1] = (a[n]-b)/2 */

    const int NMAX = 12;
    float a[NMAX + 1];
    float c[NMAX + 1];

    a[0] = 1.0f;
    float b = sqrtf(1.0f - m);
    c[0] = sqrtf(m);
    float twon = 1.0f;

    int i = 0;
    /* Loop while |c[i]| > MACHEP * a[i] (single precision MACHEP ~ 1.19e-7) */
    while (i < NMAX && fabsf(c[i]) > 1.19e-7f * a[i]) {
        float ai = a[i];
        c[i + 1] = 0.5f * (ai - b);
        a[i + 1] = 0.5f * (ai + b);
        b        = sqrtf(ai * b);
        twon    *= 2.0f;
        i++;
    }

    /* --- Backward substitution: compute amplitude phi --- */
    /* Starting amplitude at converged level */
    float phi = twon * a[i] * u;

    while (i > 0) {
        float t = c[i] * sinf(phi) / a[i];
        /* Clamp to [-1, 1] for numerical safety at large u */
        t = fminf(fmaxf(t, -1.0f), 1.0f);
        phi = 0.5f * (asinf(t) + phi);
        i--;
    }

    *sn = sinf(phi);
    *cn = cosf(phi);
    *dn = sqrtf(fmaxf(0.0f, 1.0f - m * (*sn) * (*sn)));
}

/* ============================================================================
 * Complete Elliptic Integral K(k) via AGM
 * ============================================================================ */

/**
 * @brief Complete elliptic integral of the first kind K(k).
 *
 * K(k) = pi / (2 * AGM(1, sqrt(1-k^2)))
 *
 * @param k  Modulus (0 <= k < 1)
 * @return   K(k) in radians
 */
__device__ __forceinline__ float d_ellint_K(float k)
{
    if (k < 1.0e-6f) return 1.5707963268f; /* pi/2 */
    float a = 1.0f;
    float b = sqrtf(1.0f - k * k);
    for (int i = 0; i < 14; i++) {
        float a1 = 0.5f * (a + b);
        float b1 = sqrtf(a * b);
        a = a1;
        b = b1;
    }
    return 1.5707963268f / a; /* pi/2 / AGM(1, k') */
}

/* ============================================================================
 * Radial Quartic Coefficients
 * ============================================================================ */

/**
 * @brief Coefficients of the Kerr radial potential quartic.
 *
 * R(r) = r^4 + c2*r^2 + c1*r + c0  (with M=1, no cubic term)
 *
 * Derived from R(r) = (r^2+a^2-a*xi)^2 - Delta*(eta+(xi-a)^2)
 * where Delta = r^2 - 2r + a^2.
 *
 * @param a   Spin parameter
 * @param xi  Impact parameter xi = L/E
 * @param eta Impact parameter eta = Q/E^2
 * @param c2  Output: quadratic coefficient
 * @param c1  Output: linear coefficient
 * @param c0  Output: constant coefficient
 */
__device__ __forceinline__ void d_radial_quartic_coeffs(
        float a, float xi, float eta,
        float* c2, float* c1, float* c0)
{
    float a2   = a * a;
    float xiA  = xi - a;
    float xiA2 = xiA * xiA;
    float aXi  = a2 - a * xi;

    *c2 = 2.0f * aXi - eta - xiA2;
    *c1 = 2.0f * (eta + xiA2);
    *c0 = aXi * aXi - a2 * (eta + xiA2);
}

/* ============================================================================
 * Depressed Quartic Root Finder (Ferrari's method, real roots only)
 * ============================================================================ */

/**
 * @brief Find real roots of the depressed quartic r^4 + c2*r^2 + c1*r + c0 = 0.
 *
 * Uses Ferrari's method. The factorization into two quadratics
 *   (r^2 + alpha*r + beta)(r^2 - alpha*r + gamma) = 0
 * requires finding alpha^2 = w via the resolvent cubic:
 *   w^3 + 2*c2*w^2 + (c2^2 - 4*c0)*w - c1^2 = 0
 *
 * This resolvent is depressed by w = t - 2*c2/3, then solved via Cardano
 * (1 real root) or the trigonometric formula (3 real roots).
 *
 * Once alpha^2 = w is found:
 *   beta  = (c2 + w)/2 - c1/(2*alpha)
 *   gamma = (c2 + w)/2 + c1/(2*alpha)
 *
 * Returns real roots in descending order.
 *
 * @param c2   Quadratic coefficient
 * @param c1   Linear coefficient
 * @param c0   Constant coefficient
 * @param r    Output: real roots, r[0] >= r[1] >= r[2] >= r[3]
 * @return     Number of real roots (0, 2, or 4)
 */
__device__ int d_quartic_real_roots(float c2, float c1, float c0, float r[4])
{
    /* Resolvent cubic depressed form: t^3 + p*t + q = 0
     * w = alpha^2 = t - 2*c2/3
     *
     * Derivation: resolvent is w^3 + 2*c2*w^2 + (c2^2-4*c0)*w - c1^2 = 0.
     * Substituting w = t - 2*c2/3 to eliminate w^2 term gives:
     *   p = (c2^2 - 4*c0) - (2*c2)^2/3 = -c2^2/3 - 4*c0
     *   q = -2*c2^3/27 + (8/3)*c2*c0 - c1^2
     * Note: q uses 8/3, NOT 4/3 (common mistake in derived Ferrari formulae).
     */
    float p     = -(c2 * c2) * (1.0f / 3.0f) - 4.0f * c0;
    float q     = (-2.0f / 27.0f) * c2 * c2 * c2
                  + (8.0f / 3.0f) * c2 * c0
                  - c1 * c1;
    float shift = (2.0f / 3.0f) * c2; /* w = t - shift */

    float disc = 0.25f * q * q + (1.0f / 27.0f) * p * p * p;

    float alpha = 0.0f;
    bool  found = false;

    if (disc >= 0.0f) {
        /* Cardano: single real root */
        float sq = sqrtf(disc);
        float u3 = -0.5f * q + sq;
        float v3 = -0.5f * q - sq;
        float u  = (u3 >= 0.0f) ? cbrtf(u3) : -cbrtf(-u3);
        float v  = (v3 >= 0.0f) ? cbrtf(v3) : -cbrtf(-v3);
        float w  = (u + v) - shift;
        if (w >= 0.0f) {
            alpha = sqrtf(w);
            found = true;
        }
    } else {
        /* Three real roots; iterate over all three trig solutions to find w >= 0.
         * For a quartic with 4 real roots all three resolvent roots are positive,
         * so k=0 (largest root) always succeeds. */
        float rVal    = sqrtf(-(p * p * p) * (1.0f / 27.0f));
        float base_phi = acosf(fminf(fmaxf(-0.5f * q / rVal, -1.0f), 1.0f));
        float cbrt_r  = cbrtf(rVal);
        const float TWO_PI = 6.28318530718f;
        for (int k = 0; k < 3 && !found; k++) {
            float phi_k = (base_phi + TWO_PI * (float)k) * (1.0f / 3.0f);
            float w     = 2.0f * cbrt_r * cosf(phi_k) - shift;
            if (w >= 1.0e-10f) {
                alpha = sqrtf(w);
                found = true;
            }
        }
    }

    if (!found) return 0;

    /* Compute beta and gamma from the factorization constraint.
     * From (r^2+alpha*r+beta)(r^2-alpha*r+gamma) matching c2,c1,c0:
     *   beta  = (c2 + alpha^2)/2 - c1/(2*alpha)
     *   gamma = (c2 + alpha^2)/2 + c1/(2*alpha)
     */
    float w       = alpha * alpha; /* = resolved alpha^2 */
    float half_cw = 0.5f * (c2 + w);
    float half_c1a = (alpha > 1.0e-8f) ? (0.5f * c1 / alpha) : 0.0f;
    float beta  = half_cw - half_c1a;
    float gamma = half_cw + half_c1a;

    float d1 = w - 4.0f * beta;
    float d2 = w - 4.0f * gamma;

    /* Collect real roots */
    float roots[4];
    int nreal = 0;

    if (d1 >= 0.0f) {
        float sq1      = sqrtf(d1);
        roots[nreal++] = 0.5f * (-alpha + sq1);
        roots[nreal++] = 0.5f * (-alpha - sq1);
    }
    if (d2 >= 0.0f) {
        float sq2      = sqrtf(d2);
        roots[nreal++] = 0.5f * (alpha + sq2);
        roots[nreal++] = 0.5f * (alpha - sq2);
    }

    /* Bubble sort: descending order */
    for (int ii = 0; ii < nreal - 1; ii++) {
        for (int jj = ii + 1; jj < nreal; jj++) {
            if (roots[jj] > roots[ii]) {
                float tmp  = roots[ii];
                roots[ii]  = roots[jj];
                roots[jj]  = tmp;
            }
        }
    }

    for (int ii = 0; ii < nreal; ii++) r[ii] = roots[ii];
    return nreal;
}

/* ============================================================================
 * Analytic Radial Solution r(lambda)
 * ============================================================================ */

/**
 * @brief Compute r(lambda) analytically for a Kerr bound orbit.
 *
 * For a bound orbit with four real roots r1 >= r2 >= r3 >= r4, the photon
 * oscillates in the allowed region [r3, r2] where R(r) >= 0.
 *
 * Uses the bilinear (Mobius) substitution (Fujita & Hikida 2009):
 *
 *   r(u) = [r3*(r2-r4) - r4*(r2-r3)*sn^2(u|m)] /
 *           [(r2-r4)       -     (r2-r3)*sn^2(u|m)]
 *
 * where:
 *   m     = (r2-r3)*(r1-r4) / [(r1-r3)*(r2-r4)]   (standard Jacobi modulus)
 *   scale = sqrt(|(r1-r3)*(r2-r4)|) / 2
 *   u     = scale * (lambda - lambda0)
 *
 * WHY the Mobius form (not the simpler r3+(r2-r3)*sn^2):
 *   The substitution r = r3+(r2-r3)*sn^2 produces a sn^4 residual in the
 *   ODE identity (dr/dlambda)^2 = R(r) that does not cancel.  The Mobius
 *   form satisfies the quartic ODE exactly: after substituting and using
 *   dn^2 = 1-m*sn^2, the (sn^4)-degree terms cancel and one gets
 *   (dr/du)^2 = scale^2 * R(r) as a polynomial identity.
 *
 * WHY r2 in the anchor terms (not r1 as in the CPU source):
 *   Using r1 gives the correct modulus but targets the WRONG endpoint (r1),
 *   crossing the forbidden region [r2, r1] where R(r) < 0.  Using r2 ensures
 *   the Mobius transform maps sn^2 in [0,1] monotonically to r in [r3, r2].
 *
 * At lambda = lambda0: sn=0 => r = r3 (inner turning point).
 * At u = K(k):          sn=1 => r = r2 (outer turning point).
 *
 * References:
 *   Fujita & Hikida (2009) arXiv:0906.1420, eq.(22)
 *   Byrd & Friedman (1971) Handbook of Elliptic Integrals, form 361.00
 *
 * @param lambda   Affine parameter value
 * @param r1..r4   Roots in descending order (r1 >= r2 >= r3 >= r4)
 * @param lambda0  Reference affine parameter (ray starts at r3)
 * @return r at the given lambda, or r3 if degenerate
 */
__device__ float d_kerr_r_analytic(
        float lambda,
        float r1, float r2, float r3, float r4,
        float lambda0)
{
    /* m = (r2-r3)*(r1-r4) / [(r1-r3)*(r2-r4)]  (Fujita & Hikida modulus) */
    float num_m = (r2 - r3) * (r1 - r4);
    float den_m = (r1 - r3) * (r2 - r4);

    if (fabsf(den_m) < 1.0e-20f) return r3;

    float m = num_m / den_m;
    m = fminf(fmaxf(m, 0.0f), 1.0f); /* clamp to valid range */

    float scale = 0.5f * sqrtf(fabsf((r1 - r3) * (r2 - r4)));
    float u     = scale * (lambda - lambda0);

    float sn, cn, dn;
    d_ellpj(u, m, &sn, &cn, &dn);

    /* Mobius formula: r = [r3*(r2-r4) - r4*(r2-r3)*sn^2] / [(r2-r4) - (r2-r3)*sn^2] */
    float sn2    = sn * sn;
    float r24    = r2 - r4; /* r2 - r4 */
    float r23    = r2 - r3; /* r2 - r3 */
    float a_coef = r3 * r24 - r4 * r23 * sn2;
    float b_coef = r24 - r23 * sn2;

    if (fabsf(b_coef) < 1.0e-20f) return r2; /* at outer turning point */
    return a_coef / b_coef;
}

/**
 * @brief Half-period of radial oscillation in affine parameter.
 *
 * T_r/2 = K(k) / scale
 *
 * where k = sqrt(m), m = (r2-r3)*(r1-r4)/[(r1-r3)*(r2-r4)] (Fujita & Hikida),
 * and scale = sqrt(|(r1-r3)*(r2-r4)|) / 2.
 *
 * Modulus matches d_kerr_r_analytic; K is the quarter-period of sn(u,k).
 * Returns 0 if the orbit is degenerate.
 *
 * @param r1..r4  Sorted radial roots (r1 >= r2 >= r3 >= r4)
 * @return Half-period in affine parameter units
 */
__device__ __forceinline__ float d_kerr_radial_half_period(
        float r1, float r2, float r3, float r4)
{
    /* Fujita & Hikida modulus: m = (r2-r3)*(r1-r4)/[(r1-r3)*(r2-r4)] */
    float num_m = (r2 - r3) * (r1 - r4);
    float den_m = (r1 - r3) * (r2 - r4);

    if (fabsf(den_m) < 1.0e-20f) return 0.0f;

    float m = fminf(fmaxf(num_m / den_m, 0.0f), 1.0f);
    float k = sqrtf(m);

    float scale = 0.5f * sqrtf(fabsf((r1 - r3) * (r2 - r4)));
    if (scale < 1.0e-20f) return 0.0f;

    return d_ellint_K(k) / scale;
}

/* ============================================================================
 * Photon Sphere Critical Curves
 * ============================================================================ */

/**
 * @brief Critical impact parameters (xi_c, eta_c) for the Kerr photon sphere.
 *
 * xi_c(r_ph) = (r^2 + a^2)/a - 2*r*Delta/(a*Delta')
 * eta_c(r_ph) = r^2 * [4*Delta - r*(r-1)^2] / (a^2*(r-1)^2)   [M=1]
 *
 * @param rph  Photon orbit radius [geometric units, M=1]
 * @param a    Spin parameter
 * @param xi   Output: xi_c
 * @param eta  Output: eta_c
 */
__device__ __forceinline__ void d_critical_impact_params(
        float rph, float a, float* xi, float* eta)
{
    float r2    = rph * rph;
    float a2    = a * a;
    float delta = r2 - 2.0f * rph + a2;
    float dp    = 2.0f * rph - 2.0f; /* Delta'(r) = 2r - 2 for M=1 */

    if (fabsf(a) < 1.0e-8f) {
        /* Schwarzschild: xi=0 by symmetry; eta=27 at r_ph=3 */
        *xi  = 0.0f;
        *eta = 27.0f;
        return;
    }

    if (fabsf(dp) < 1.0e-8f) {
        *xi  = 0.0f;
        *eta = 0.0f;
        return;
    }

    *xi = (r2 + a2) / a - 2.0f * rph * delta / (a * dp);

    float rm1 = rph - 1.0f;
    if (fabsf(rm1) > 1.0e-8f) {
        *eta = r2 * (4.0f * delta - rph * rm1 * rm1) / (a2 * rm1 * rm1);
    } else {
        /* r_ph = 1 (near-extremal): use dp-based formula */
        float eta_num = r2 * (8.0f * delta - dp * dp * rph);
        *eta = eta_num / (a2 * dp * dp);
    }
}

/**
 * @brief Prograde photon orbit radius in Kerr.
 *
 * r_ph = 2 * (1 + cos(2/3 * arccos(-|a|)))  [M=1]
 *
 * Range: 3 (Schwarzschild) down to 1 (extremal Kerr prograde).
 *
 * @param a  Spin parameter (|a| <= 1)
 * @return   Prograde photon orbit radius
 */
__device__ __forceinline__ float d_prograde_photon_orbit(float a)
{
    return 2.0f * (1.0f + cosf((2.0f / 3.0f) * acosf(-fabsf(a))));
}

/**
 * @brief Retrograde photon orbit radius in Kerr.
 *
 * r_ph = 2 * (1 + cos(2/3 * arccos(|a|)))  [M=1]
 *
 * Range: 3 (Schwarzschild) up to 4 (extremal Kerr retrograde).
 *
 * @param a  Spin parameter
 * @return   Retrograde photon orbit radius
 */
__device__ __forceinline__ float d_retrograde_photon_orbit(float a)
{
    return 2.0f * (1.0f + cosf((2.0f / 3.0f) * acosf(fabsf(a))));
}

#endif /* DEVICE_ANALYTIC_KERR_CUH */
