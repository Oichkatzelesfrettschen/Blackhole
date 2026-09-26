/**
 * kerr_de_sitter.glsl
 *
 * GLSL twin of src/physics/verified/kerr_de_sitter.hpp (Carter 1968 form).
 * The C++ header is the reference; tests/kerr_de_sitter_test.cpp checks it
 * against mpmath horizons and R_mu_nu = Lambda g_mu_nu. This file mirrors it
 * in float32, so horizons for Lambda below ~1e-6 M^-2 lose the cosmological
 * root to rounding; no shader entry point includes it.
 *
 *   Sigma       = r^2 + a^2 cos^2 theta
 *   Delta_r     = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r
 *   Delta_theta = 1 + Lambda a^2 cos^2 theta / 3
 *   Xi          = 1 + Lambda a^2 / 3
 */

#ifndef SHADER_VERIFIED_KERR_DE_SITTER_HPP
#define SHADER_VERIFIED_KERR_DE_SITTER_HPP

/**
 * Sigma = r^2 + a^2 cos^2(theta)
 *
 * Rocq Derivation: Derived from Rocq:Definition kds_Sigma (r theta a : R) : R :=...
 */
float kds_Sigma(float r, float theta, float a) {
    float cos_theta = cos(theta);
    return r * r + a * a * cos_theta * cos_theta;
}

/**
 * Radial function Delta_r = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r
 *
 * Rocq Derivation: Derived from Rocq:Definition kds_Delta (r M a Lambda : R) : R :=...
 */
float kds_Delta(float r, float M, float a, float Lambda) {
    return (r * r + a * a) * (1.0 - Lambda * r * r / 3.0) - 2.0 * M * r;
}

/**
 * Polar function Delta_theta = 1 + Lambda a^2 cos^2(theta) / 3
 *
 * Rocq Derivation: Derived from Rocq:Definition kds_Delta_theta (theta a Lambda : R) : R :=...
 */
float kds_Delta_theta(float theta, float a, float Lambda) {
    float cos_theta = cos(theta);
    return 1.0 + Lambda * a * a * cos_theta * cos_theta / 3.0;
}

/**
 * Xi = 1 + Lambda a^2 / 3
 *
 * Rocq Derivation: Derived from Rocq:Definition kds_Xi (a Lambda : R) : R :=...
 */
float kds_Xi(float a, float Lambda) {
    return 1.0 + Lambda * a * a / 3.0;
}

/**
 * A = Delta_theta (r^2 + a^2)^2 - Delta_r a^2 sin^2(theta)
 *
 * Rocq Derivation: Derived from Rocq:Definition kds_A (r theta M a Lambda : R) : R :=...
 *
 * Depends on: kds_Delta, kds_Delta_theta
 */
float kds_A(float r, float theta, float M, float a, float Lambda) {
    float r2_plus_a2 = r * r + a * a;
    float sin_theta = sin(theta);
    return kds_Delta_theta(theta, a, Lambda) * r2_plus_a2 * r2_plus_a2
        - kds_Delta(r, M, a, Lambda) * a * a * sin_theta * sin_theta;
}

/**
 * g_tt = (-Delta_r + Delta_theta a^2 sin^2 theta) / (Xi^2 Sigma)
 *
 * Depends on: kds_Delta, kds_Delta_theta, kds_Sigma, kds_Xi
 */
float kds_g_tt(float r, float theta, float M, float a, float Lambda) {
    float sin_theta = sin(theta);
    float Xi = kds_Xi(a, Lambda);
    return (-kds_Delta(r, M, a, Lambda)
            + kds_Delta_theta(theta, a, Lambda) * a * a * sin_theta * sin_theta)
        / (Xi * Xi * kds_Sigma(r, theta, a));
}

/**
 * g_rr = Sigma / Delta_r
 *
 * Depends on: kds_Delta, kds_Sigma
 */
float kds_g_rr(float r, float theta, float M, float a, float Lambda) {
    return kds_Sigma(r, theta, a) / kds_Delta(r, M, a, Lambda);
}

/**
 * g_thth = Sigma / Delta_theta
 *
 * Depends on: kds_Delta_theta, kds_Sigma
 */
float kds_g_thth(float r, float theta, float a, float Lambda) {
    return kds_Sigma(r, theta, a) / kds_Delta_theta(theta, a, Lambda);
}

/**
 * g_phph = sin^2 theta A / (Xi^2 Sigma)
 *
 * Depends on: kds_A, kds_Sigma, kds_Xi
 */
float kds_g_phph(float r, float theta, float M, float a, float Lambda) {
    float sin_theta = sin(theta);
    float Xi = kds_Xi(a, Lambda);
    return sin_theta * sin_theta * kds_A(r, theta, M, a, Lambda) / (Xi * Xi * kds_Sigma(r, theta, a));
}

/**
 * g_tph = a sin^2 theta (Delta_r - Delta_theta (r^2 + a^2)) / (Xi^2 Sigma)
 *
 * Depends on: kds_Delta, kds_Delta_theta, kds_Sigma, kds_Xi
 */
float kds_g_tph(float r, float theta, float M, float a, float Lambda) {
    float sin_theta = sin(theta);
    float Xi = kds_Xi(a, Lambda);
    return a * sin_theta * sin_theta
        * (kds_Delta(r, M, a, Lambda) - kds_Delta_theta(theta, a, Lambda) * (r * r + a * a))
        / (Xi * Xi * kds_Sigma(r, theta, a));
}

/**
 * Positive stationary point of Delta_r (upper: local maximum r_b; else local
 * minimum r_a), from the trigonometric roots of the depressed cubic. NaN when
 * Delta_r has no local maximum at r > 0.
 */
float kds_delta_stationary_radius(float M, float a, float Lambda, bool upper) {
    float zero = 0.0;
    float b = 1.0 - Lambda * a * a / 3.0;
    if (!(Lambda > 0.0) || !(M > 0.0) || !(b > 0.0)) {
        return zero / zero;
    }
    float p = -3.0 * b / (2.0 * Lambda);
    float q = 3.0 * M / (2.0 * Lambda);
    float cos_arg = (3.0 * q / (2.0 * p)) * sqrt(-3.0 / p);
    if (!(cos_arg > -1.0)) {
        return zero / zero;
    }
    float phi = acos(cos_arg) / 3.0;
    float amplitude = 2.0 * sqrt(-p / 3.0);
    float shift = upper ? 0.0 : 2.0 * 3.14159265358979 / 3.0;
    return amplitude * cos(phi - shift);
}

/**
 * Bisect a sign change of Delta_r - offset on [lo, hi].
 *
 * Depends on: kds_Delta
 */
float kds_bisect_delta(float lo, float hi, float M, float a, float Lambda, float offset) {
    bool lo_positive = kds_Delta(lo, M, a, Lambda) - offset > 0.0;
    for (int iteration = 0; iteration < 64; ++iteration) {
        float mid = 0.5 * (lo + hi);
        if (!(mid > lo && mid < hi)) {
            break;
        }
        if ((kds_Delta(mid, M, a, Lambda) - offset > 0.0) == lo_positive) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    return 0.5 * (lo + hi);
}

/**
 * Inner (Cauchy) horizon: smallest positive root of Delta_r; 0 at a = 0.
 *
 * Depends on: kds_bisect_delta, kds_delta_stationary_radius, kds_Delta
 */
float kds_inner_horizon(float M, float a, float Lambda) {
    float zero = 0.0;
    if (Lambda == 0.0) {
        float disc = M * M - a * a;
        return (M > 0.0 && disc >= 0.0) ? M - sqrt(disc) : zero / zero;
    }
    float r_min = kds_delta_stationary_radius(M, a, Lambda, false);
    if (!(kds_Delta(r_min, M, a, Lambda) < 0.0)) {
        return zero / zero;
    }
    if (a == 0.0) {
        return 0.0;
    }
    return kds_bisect_delta(0.0, r_min, M, a, Lambda, 0.0);
}

/**
 * Event horizon: root of Delta_r between its local minimum and maximum.
 *
 * Depends on: kds_bisect_delta, kds_delta_stationary_radius, kds_Delta
 */
float kds_event_horizon(float M, float a, float Lambda) {
    float zero = 0.0;
    if (Lambda == 0.0) {
        float disc = M * M - a * a;
        return (M > 0.0 && disc >= 0.0) ? M + sqrt(disc) : zero / zero;
    }
    float r_min = kds_delta_stationary_radius(M, a, Lambda, false);
    float r_max = kds_delta_stationary_radius(M, a, Lambda, true);
    if (!(kds_Delta(r_min, M, a, Lambda) < 0.0) || !(kds_Delta(r_max, M, a, Lambda) > 0.0)) {
        return zero / zero;
    }
    return kds_bisect_delta(r_min, r_max, M, a, Lambda, 0.0);
}

/**
 * Cosmological horizon: largest root of Delta_r; +infinity at Lambda = 0.
 *
 * Depends on: kds_bisect_delta, kds_delta_stationary_radius, kds_Delta
 */
float kds_cosmological_horizon(float M, float a, float Lambda) {
    float zero = 0.0;
    if (Lambda == 0.0) {
        return 1.0 / zero;
    }
    float r_min = kds_delta_stationary_radius(M, a, Lambda, false);
    float r_max = kds_delta_stationary_radius(M, a, Lambda, true);
    if (!(kds_Delta(r_min, M, a, Lambda) < 0.0) || !(kds_Delta(r_max, M, a, Lambda) > 0.0)) {
        return zero / zero;
    }
    float r_high = max(r_max, sqrt(3.0 / Lambda));
    for (int doubling = 0; doubling < 64 && !(kds_Delta(r_high, M, a, Lambda) < 0.0); ++doubling) {
        r_high *= 2.0;
    }
    return kds_bisect_delta(r_max, r_high, M, a, Lambda, 0.0);
}

/**
 * Black-hole ergosurface: root of g_tt = 0 between r_+ and the Delta_r maximum.
 *
 * Depends on: kds_bisect_delta, kds_delta_stationary_radius, kds_Delta,
 * kds_Delta_theta, kds_event_horizon
 */
float kds_ergosphere_radius(float theta, float M, float a, float Lambda) {
    float zero = 0.0;
    float sin_theta = sin(theta);
    float target = kds_Delta_theta(theta, a, Lambda) * a * a * sin_theta * sin_theta;
    float r_plus = kds_event_horizon(M, a, Lambda);
    if (isnan(r_plus) || target == 0.0) {
        return r_plus;
    }
    float r_max = (Lambda == 0.0) ? 4.0 * M : kds_delta_stationary_radius(M, a, Lambda, true);
    if (!(kds_Delta(r_max, M, a, Lambda) > target)) {
        return zero / zero;
    }
    return kds_bisect_delta(r_plus, r_max, M, a, Lambda, target);
}

/**
 * Frame dragging angular velocity: omega = -g_tph / g_phph
 *
 * Depends on: kds_g_phph, kds_g_tph
 */
float kds_frame_dragging_omega(float r, float theta, float M, float a, float Lambda) {
    return -kds_g_tph(r, theta, M, a, Lambda) / kds_g_phph(r, theta, M, a, Lambda);
}

/**
 * M > 0, Lambda > 0, and ordered horizons r_- <= r_+ < r_c.
 *
 * Depends on: kds_cosmological_horizon, kds_event_horizon, kds_inner_horizon
 */
bool is_physical_kds_black_hole(float M, float a, float Lambda) {
    if (!(M > 0.0) || !(Lambda > 0.0)) {
        return false;
    }
    float r_minus = kds_inner_horizon(M, a, Lambda);
    float r_plus = kds_event_horizon(M, a, Lambda);
    float r_cosmo = kds_cosmological_horizon(M, a, Lambda);
    return r_minus <= r_plus && r_plus < r_cosmo;
}

/**
 * Position between the event and cosmological horizons.
 *
 * Depends on: kds_cosmological_horizon, kds_event_horizon
 */
bool is_exterior_region(float r, float M, float a, float Lambda) {
    return r > kds_event_horizon(M, a, Lambda) && r < kds_cosmological_horizon(M, a, Lambda);
}

/**
 * d/dt spacelike (g_tt > 0): black-hole ergoregion or beyond the cosmological
 * ergosurface.
 *
 * Depends on: kds_g_tt
 */
bool is_in_ergosphere(float r, float theta, float M, float a, float Lambda) {
    return kds_g_tt(r, theta, M, a, Lambda) > 0.0;
}

/**
 * Horizon ordering r_- <= r_+ < r_c.
 *
 * Depends on: is_physical_kds_black_hole
 */
bool verify_horizon_ordering(float M, float a, float Lambda) {
    return is_physical_kds_black_hole(M, a, Lambda);
}

/**
 * Kerr limit (Lambda ~ 0)
 */
bool is_kerr_limit(float Lambda, float tolerance) {
    return abs(Lambda) < tolerance;
}

/**
 * de Sitter limit (M ~ 0, a ~ 0)
 */
bool is_de_sitter_limit(float M, float a, float tolerance) {
    return abs(M) < tolerance && abs(a) < tolerance;
}

/**
 * Cosmological constant in m^-2; the identity under c = G = 1.
 */
float lambda_si_to_geometric(float Lambda_SI) {
    return Lambda_SI;
}

/**
 * Observed cosmological constant, 1.1e-52 m^-2 (Planck 2018). The value lies
 * below the float32 normal range; shader callers work in units of M.
 */
float observed_lambda() {
    return 1.1e-52;
}

#endif // SHADER_VERIFIED_KERR_DE_SITTER_HPP
