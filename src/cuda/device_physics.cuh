/**
 * @file device_physics.cuh
 * @brief CUDA __device__ implementations of Kerr metric geodesic tracing and shading.
 *
 * Ported from shader/include/kerr.glsl and shader/include/interop_trace.glsl.
 *
 * FIREWALL: This file includes ONLY <cuda_runtime.h> and <math.h>.
 * No standard library headers beyond C99. No headers from src/physics/.
 */

#ifndef BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH
#define BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH

#include <cuda_runtime.h>
#include <math.h>

/* ========================================================================
 * Constants (mirrors physics_constants.glsl)
 * ======================================================================== */

#define D_PI            3.14159265358979323846f /**< @brief Pi. */
#define D_TWO_PI        6.28318530717958647692f /**< @brief 2*pi. */
#define D_HALF_PI       1.57079632679489661923f /**< @brief pi/2. */
#define D_INV_PI        0.31830988618379067154f /**< @brief 1/pi. */
#define D_INV_TWO_PI    0.15915494309189533577f /**< @brief 1/(2*pi). */
#define D_EPSILON       1.0e-6f                 /**< @brief Small guard value for division and comparisons. */
#define D_PHOTON_SPHERE 1.5f                    /**< @brief Photon sphere radius in units of rs (= 3M/2M = 1.5). */
#define D_ISCO_RATIO    3.0f                    /**< @brief ISCO radius ratio (Schwarzschild: r_ISCO = 3*rs). */

/* ========================================================================
 * Constant memory (filled by host before kernel launch)
 * ======================================================================== */

/* extern __constant__: defined ONCE in kernel_launch.cu.
 * With CUDA separable compilation, constants must not be defined in headers
 * included by multiple TUs -- nvlink would see duplicate symbols. */
extern __constant__ float d_rs;
extern __constant__ float d_spin;
extern __constant__ float d_isco;
extern __constant__ float d_step_size;
extern __constant__ float d_fov_scale;
extern __constant__ float d_max_dist;
extern __constant__ float d_cam_pos[3];
extern __constant__ float d_cam_basis[9];
extern __constant__ float d_frame_shift_x;
extern __constant__ float d_frame_shift_y;
extern __constant__ int   d_max_steps;
extern __constant__ int   d_width;
extern __constant__ int   d_height;
extern __constant__ int   d_adisk_enabled;
extern __constant__ int   d_redshift_enabled;
extern __constant__ int   d_kerr_enabled;
extern __constant__ int   d_use_luts;
extern __constant__ float d_lut_radius_min;
extern __constant__ float d_lut_radius_max;
extern __constant__ float d_redshift_radius_min;
extern __constant__ float d_redshift_radius_max;
extern __constant__ float d_spectral_radius_min;
extern __constant__ float d_spectral_radius_max;
extern __constant__ float d_time_sec;
/* LUT texture objects (cudaTextureObject_t = unsigned long long).
 * Zero means the slot is not registered; all device sampling sites guard on 0.
 * Matches BhLutSlot order: emissivity=0, redshift=1, spectral=2, grb=3, galaxy=4,
 * grmhd=5, synch_g=6, grmhd_right=7. */
extern __constant__ unsigned long long d_tex_emissivity;   /**< @brief Slot 0: accretion emissivity. */
extern __constant__ unsigned long long d_tex_redshift;     /**< @brief Slot 1: gravitational redshift. */
extern __constant__ unsigned long long d_tex_spectral;     /**< @brief Slot 2: spectral modulation. */
extern __constant__ unsigned long long d_tex_grb;          /**< @brief Slot 3: GRB overlay LUT. */
extern __constant__ unsigned long long d_tex_galaxy;       /**< @brief Slot 4: galaxy cubemap. */
extern __constant__ unsigned long long d_tex_grmhd;        /**< @brief Slot 5: GRMHD left frame (RGBA32F 3D). */
extern __constant__ unsigned long long d_tex_synch_g;      /**< @brief Slot 6: synchrotron G(x)=x*K_{2/3}(x) LUT (R32F 2D, height=1). */
extern __constant__ unsigned long long d_tex_grmhd_right;  /**< @brief Slot 7: GRMHD right frame for time interpolation (RGBA32F 3D). */
extern __constant__ unsigned long long d_tex_background_equirect; /**< @brief Optional bridge 2D equirectangular background. */
extern __constant__ float d_grmhd_alpha;                   /**< @brief Blend factor [0,1] between left and right GRMHD frames (C1d). */
extern __constant__ float d_doppler_strength;
extern __constant__ float d_background_intensity;
extern __constant__ int   d_background_enabled;
extern __constant__ float d_photon_glow_strength;
extern __constant__ float d_background_yaw_rad;
extern __constant__ float d_background_pitch_rad;
extern __constant__ float d_background_filter_radius;
extern __constant__ float d_background_layer_params[12];
extern __constant__ float d_background_layer_lod_bias[3];
extern __constant__ int   d_wiregrid_enabled;    /**< @brief BL-coord wiregrid overlay flag. */
extern __constant__ float d_wiregrid_show_ergo;  /**< @brief Show ergosphere boundary+glow. */
extern __constant__ float d_wiregrid_grid_scale; /**< @brief Grid density multiplier. */
extern __constant__ float d_wiregrid_motion_scale; /**< @brief Frame-dragging azimuth advection strength. */
extern __constant__ float d_wiregrid_infall_scale; /**< @brief Inward radial-shell advection strength. */
extern __constant__ float d_wiregrid_strength;     /**< @brief Post-attenuation alpha multiplier. */
extern __constant__ float d_wiregrid_scene_preserve; /**< @brief 1 = yield to scene luminance. */
extern __constant__ float d_wiregrid_color[4];     /**< @brief Base RGBA for the coordinate grid overlay. */
extern __constant__ float d_grmhd_r_min;         /**< @brief Inner radial bound of GRMHD grid. */
extern __constant__ float d_grmhd_r_max;         /**< @brief Outer radial bound of GRMHD grid. */
extern __constant__ int   d_rte_enabled;          /**< @brief 1 = volumetric RTE path (D3). */
extern __constant__ float d_rte_opacity_scale;    /**< @brief alpha_nu = rte_opacity_scale * j_nu. */
extern __constant__ int   d_stokes_enabled;       /**< @brief 1 = polarized Stokes IQUV transport (D4). */
extern __constant__ float d_stokes_b_angle;       /**< @brief EVPA of projected B field on sky [rad] (D4). */
extern __constant__ float d_stokes_ne_scale;      /**< @brief Faraday rotation strength multiplier (D4). */
extern __constant__ float d_adisk_lit;            /**< @brief Disk luminosity scale (1.0 = GLSL flux*2 level). */

/* ========================================================================
 * Vector helpers (replacing GLSL vec3 operations)
 * ======================================================================== */

/** @brief Construct a float3 from three scalar components. */
__device__ __forceinline__ float3 make_f3(float x, float y, float z) {
    return make_float3(x, y, z);
}

/** @brief Dot product of two float3 vectors using FMA. */
__device__ __forceinline__ float d_dot(float3 a, float3 b) {
    return fmaf(a.x, b.x, fmaf(a.y, b.y, a.z * b.z));
}

/** @brief Euclidean length of a float3 vector. */
__device__ __forceinline__ float d_length(float3 v) {
    return sqrtf(d_dot(v, v));
}

/** @brief Normalize a float3 vector; guards against zero-length with a 1e-12 floor. */
__device__ __forceinline__ float3 d_normalize(float3 v) {
    float inv = rsqrtf(fmaxf(d_dot(v, v), 1.0e-12f));
    return make_f3(v.x * inv, v.y * inv, v.z * inv);
}

/** @brief Cross product of two float3 vectors using FMA. */
__device__ __forceinline__ float3 d_cross(float3 a, float3 b) {
    return make_f3(
        fmaf(a.y, b.z, -a.z * b.y),
        fmaf(a.z, b.x, -a.x * b.z),
        fmaf(a.x, b.y, -a.y * b.x)
    );
}

/** @brief Scale a float3 vector by a scalar. */
__device__ __forceinline__ float3 d_scale(float3 v, float s) {
    return make_f3(v.x * s, v.y * s, v.z * s);
}

/** @brief Component-wise addition of two float3 vectors. */
__device__ __forceinline__ float3 d_add(float3 a, float3 b) {
    return make_f3(a.x + b.x, a.y + b.y, a.z + b.z);
}

/** @brief Component-wise subtraction of two float3 vectors. */
__device__ __forceinline__ float3 d_sub(float3 a, float3 b) {
    return make_f3(a.x - b.x, a.y - b.y, a.z - b.z);
}

/** @brief Linear interpolation between two float3 vectors using FMA. */
__device__ __forceinline__ float3 d_lerp(float3 a, float3 b, float t) {
    return make_f3(
        fmaf(t, b.x - a.x, a.x),
        fmaf(t, b.y - a.y, a.y),
        fmaf(t, b.z - a.z, a.z)
    );
}

/**
 * @brief Multiply a column-major 3x3 matrix by a float3 vector (matches glm layout).
 *
 * @param m Pointer to 9 floats in column-major order.
 * @param v Input vector.
 * @return Transformed vector m * v.
 */
__device__ __forceinline__ float3 d_mat3_mul(const float* m, float3 v) {
    return make_f3(
        fmaf(m[0], v.x, fmaf(m[3], v.y, m[6] * v.z)),
        fmaf(m[1], v.x, fmaf(m[4], v.y, m[7] * v.z)),
        fmaf(m[2], v.x, fmaf(m[5], v.y, m[8] * v.z))
    );
}

/* ========================================================================
 * Kerr metric functions (from kerr.glsl)
 * ======================================================================== */

/**
 * @brief Conserved quantities for a Kerr geodesic.
 *
 * These constants of motion (energy, axial angular momentum, Carter constant)
 * are computed once at ray initialization and reused at every integration step.
 */
struct KerrConsts {
    float E;  /**< @brief Conserved energy per unit rest mass (set to 1 for photons). */
    float Lz; /**< @brief Conserved axial angular momentum (z-component of L x r). */
    float Q;  /**< @brief Carter constant (code convention, can be negative near poles). */
};

/**
 * @brief Mutable state of a photon ray integrating through the Kerr metric.
 *
 * Coordinates are Boyer-Lindquist (r, theta, phi, t). The sign fields track
 * the current direction of motion in the potential wells for R(r) and Theta(theta).
 */
struct KerrRay {
    float r;           /**< @brief Radial Boyer-Lindquist coordinate. */
    float theta;       /**< @brief Polar angle (0 at north pole, pi at south pole). */
    float phi;         /**< @brief Azimuthal angle; can accumulate large values near horizon. */
    float t;           /**< @brief Coordinate time; grows monotonically along the ray. */
    float sign_r;      /**< @brief Sign of dr/dlambda (+1 outgoing, -1 ingoing). */
    float sign_theta;  /**< @brief Sign of dtheta/dlambda; flips at turning points. */
};

/**
 * @brief Compute the Kerr sigma function: Sigma = r^2 + a^2 * cos^2(theta).
 *
 * @param r         Radial coordinate.
 * @param a         Spin parameter (a = J/M).
 * @param cos_theta cos(theta) precomputed by the caller.
 * @return Sigma value.
 */
__device__ __forceinline__ float d_kerr_sigma(float r, float a, float cos_theta) {
    return fmaf(r, r, a * a * cos_theta * cos_theta);
}

/**
 * @brief Compute the Kerr delta function: Delta = r^2 - rs*r + a^2.
 *
 * Delta = 0 defines the event horizons. Clamped to a minimum of 1e-6 in
 * d_kerr_step() before inversion to avoid singularity at the horizon.
 *
 * @param r  Radial coordinate.
 * @param a  Spin parameter.
 * @param rs Schwarzschild radius (= 2M).
 * @return Delta value.
 */
__device__ __forceinline__ float d_kerr_delta(float r, float a, float rs) {
    return fmaf(r, r, -rs * r + a * a);
}

/**
 * @brief Compute the outer event horizon radius: r+ = M + sqrt(M^2 - a^2).
 *
 * Falls back to rs when the discriminant is negative (over-extremal spin input).
 *
 * @param rs Schwarzschild radius (= 2M).
 * @param a  Spin parameter (physical, not dimensionless; a = J/M).
 * @return Outer horizon radius r+.
 */
__device__ __forceinline__ float d_kerr_outer_horizon(float rs, float a) {
    float M = 0.5f * rs;
    float disc = fmaf(M, M, -(a * a));
    if (disc < 0.0f) return rs;
    return M + sqrtf(disc);
}

/**
 * @brief Convert Boyer-Lindquist spherical coordinates to Cartesian.
 *
 * Uses sincosf for a single MUFU.SINCOS instruction per angle pair.
 *
 * @param r     Radial coordinate.
 * @param theta Polar angle.
 * @param phi   Azimuthal angle.
 * @return Cartesian position (x, y, z).
 */
__device__ __forceinline__ float3 d_kerr_to_cartesian(float r, float theta, float phi) {
    float sin_t, cos_t, sin_p, cos_p;
    sincosf(theta, &sin_t, &cos_t);
    sincosf(phi, &sin_p, &cos_p);
    return make_f3(r * sin_t * cos_p, r * sin_t * sin_p, r * cos_t);
}

/**
 * @brief Compute exact conserved quantities for a Kerr null geodesic.
 *
 * Projects the Cartesian direction `dir` onto Boyer-Lindquist coordinates,
 * solves the null condition g_mu_nu k^mu k^nu = 0 for k^t (future-directed
 * root), then reads off E = -k_t and Lz = k_phi from the covariant components.
 * Q is derived from the code convention:
 *   Theta = Q + a^2 cos^2(theta) - Lz^2/sin^2(theta) = (Sigma * k^theta)^2
 * Result is normalized to E = 1 to preserve existing step-size calibration.
 * Q can be negative for radial photons near the poles (e.g. Q = -a^2 at theta=0).
 *
 * WHY: the old flat-space approx (E=1, Q=|L|^2-Lz^2) gives R>0 for tangential
 * rays that have no radial component, producing incorrect geodesic paths.  The
 * exact formula yields the correct impact parameters b=Lz/E and q=Q/E^2.
 *
 * @param pos Camera position in Cartesian coordinates.
 * @param dir Normalized ray direction in Cartesian coordinates.
 * @param rs  Schwarzschild radius = 2M [geometric units].
 * @param a   Spin parameter [geometric units].
 * @return KerrConsts with E=1, Lz, and Q.
 */
__device__ __forceinline__ KerrConsts d_kerr_init_consts(float3 pos, float3 dir,
                                                          float rs, float a) {
    KerrConsts c;

    float r = d_length(pos);
    if (r < D_EPSILON) {
        c.E = 1.0f; c.Lz = 0.0f; c.Q = 0.0f;
        return c;
    }

    float inv_r = 1.0f / r;
    float cos_t = fminf(fmaxf(pos.z * inv_r, -1.0f), 1.0f);
    float sin_t = sqrtf(fmaxf(1.0f - cos_t * cos_t, 0.0f));
    float sin2  = sin_t * sin_t;
    float phi   = atan2f(pos.y, pos.x);
    float cos_p, sin_p;
    sincosf(phi, &sin_p, &cos_p);

    /* Spherical basis at pos (same orientation as d_kerr_init_ray). */
    float3 e_r     = make_f3(sin_t * cos_p,  sin_t * sin_p,  cos_t);
    float3 e_theta = make_f3(cos_t * cos_p,  cos_t * sin_p, -sin_t);
    float3 e_phi   = make_f3(-sin_p,          cos_p,          0.0f);

    /* BL contravariant spatial components of the null direction. */
    float kr     = d_dot(dir, e_r);
    float ktheta = d_dot(dir, e_theta) * inv_r;
    float kphi   = (sin_t > D_EPSILON) ? (d_dot(dir, e_phi) / (r * sin_t)) : 0.0f;

    /* Kerr metric at (r, theta); rs = 2M convention. */
    float sigma  = fmaf(r, r, a * a * cos_t * cos_t);
    float delta  = fmaf(r, r, fmaf(-rs, r, a * a));
    float f      = (sigma > D_EPSILON) ? (rs * r / sigma) : 0.0f;
    float gtt    = -(1.0f - f);
    float gtphi  = -f * a * sin2;
    float grr    = sigma / fmaxf(fabsf(delta), D_EPSILON);
    float gthth  = sigma;
    float gphph  = fmaf(r * r + a * a, 1.0f, f * a * a * sin2) * sin2;

    /* Solve null condition gtt*(k^t)^2 + 2*gtphi*kphi*(k^t) + spatial = 0
     * for the future-directed root (k^t > 0). */
    float spatial = fmaf(grr, kr * kr,
                    fmaf(gthth, ktheta * ktheta, gphph * kphi * kphi));
    float hb      = gtphi * kphi;
    float disc    = fmaf(hb, hb, -gtt * spatial);
    float kt;
    if (disc >= 0.0f && fabsf(gtt) > D_EPSILON) {
        float sq_d = sqrtf(disc);
        float kt_a = (-hb + sq_d) / gtt;
        float kt_b = (-hb - sq_d) / gtt;
        kt = (kt_a > 0.0f) ? kt_a : kt_b;
        if (kt <= 0.0f) kt = fmaxf(kt_a, kt_b);  /* ergosphere: pick best root */
    } else {
        kt = 1.0f;  /* degenerate or inside ergosphere: flat-space fallback */
    }

    /* E = -(g_tt k^t + g_tphi k^phi),  Lz = g_tphi k^t + g_phph k^phi. */
    float E_raw  = fmaf(-gtt, kt, -gtphi * kphi);
    float Lz_raw = fmaf(gtphi, kt,  gphph * kphi);

    /* Normalize to E = 1 to preserve existing step-size calibration. */
    float inv_E = (E_raw > D_EPSILON) ? (1.0f / E_raw) : 1.0f;
    c.E  = 1.0f;
    c.Lz = Lz_raw * inv_E;

    /* Carter Q (code convention: Theta = Q + a^2 cos^2 - Lz^2/sin^2 = (Sigma k^theta)^2).
     * Q can be negative for radial photons near the poles (e.g. Q = -a^2 at theta=0). */
    float p_theta = sigma * ktheta * inv_E;  /* p_theta = Sigma * k^theta (E-normalized) */
    if (sin_t > D_EPSILON) {
        c.Q = fmaf(p_theta, p_theta,
              fmaf(-a * a, cos_t * cos_t, c.Lz * c.Lz / sin2));
    } else {
        /* Pole: kphi = 0, Lz = 0.  Q = ptheta^2 - a^2. */
        c.Q = fmaf(p_theta, p_theta, -(a * a));
    }

    return c;
}

/**
 * @brief Initialize a KerrRay from a Cartesian position and direction.
 *
 * Converts pos to Boyer-Lindquist (r, theta, phi). sign_r and sign_theta are
 * set from the radial and polar projections of dir onto the local frame.
 *
 * @param pos Camera position in Cartesian coordinates.
 * @param dir Normalized ray direction in Cartesian coordinates.
 * @return Initialized KerrRay with t = 0.
 */
__device__ __forceinline__ KerrRay d_kerr_init_ray(float3 pos, float3 dir) {
    KerrRay ray;
    ray.r = d_length(pos);
    float inv_r = ray.r > D_EPSILON ? 1.0f / ray.r : 0.0f;
    float cos_theta = fminf(fmaxf(pos.z * inv_r, -1.0f), 1.0f);
    ray.theta = acosf(cos_theta);
    ray.phi = atan2f(pos.y, pos.x);
    ray.t = 0.0f;

    float3 e_r = d_normalize(pos);
    float sin_t, cos_t, sin_p, cos_p;
    sincosf(ray.theta, &sin_t, &cos_t);
    sincosf(ray.phi, &sin_p, &cos_p);
    float3 e_theta = d_normalize(make_f3(cos_t * cos_p, cos_t * sin_p, -sin_t));

    float dr = d_dot(dir, e_r);
    float dtheta = d_dot(dir, e_theta);
    ray.sign_r = dr >= 0.0f ? 1.0f : -1.0f;
    ray.sign_theta = dtheta >= 0.0f ? 1.0f : -1.0f;
    return ray;
}

/**
 * @brief Advance a Kerr geodesic by one affine parameter step using the Mino-time equations.
 *
 * Computes dr/dlam, dtheta/dlam, dphi/dlam, dt/dlam from the first-order Kerr
 * geodesic equations. inv_sin2 and inv_delta are precomputed once (one MUFU.RCP
 * each) to avoid duplicate reciprocal instructions. sign_r and sign_theta are
 * flipped at turning points where R(r) or Theta(theta) changes sign.
 * theta is clamped to [1e-6, pi-1e-6] to avoid pole singularities.
 *
 * WHY rationalized KS regularization (task E1):
 * In Boyer-Lindquist (BL) coordinates, dphi/dlam and dt/dlam diverge as
 * Delta -> 0 at the outer horizon.  Outgoing Kerr-Schild (KS) coordinates
 * add a (1/Delta)*dr correction whose numerator cancels Delta for ingoing
 * photons.  The rationalized form uses the algebraic identity:
 *   (A - sqrt_R) / Delta = Q_eff / (A + sqrt_R)   where Q_eff = Q + (Lz-aE)^2
 * so dphi and dt for ingoing rays can be written with no Delta in the
 * denominator at all -- exact float32 regularity at the horizon.
 * Outgoing rays (after turning points) use the standard KS form with a
 * guarded inv_delta (Delta is bounded away from 0 for outgoing rays).
 * The (r, theta) equations are identical in BL and KS; only phi/t change.
 *
 * @param ray  Ray state to advance in-place.
 * @param rs   Schwarzschild radius.
 * @param a    Spin parameter (physical units).
 * @param c    Conserved quantities (E, Lz, Q).
 * @param dlam Affine (Mino) parameter step size.
 */
__device__ __forceinline__ void d_kerr_step(KerrRay& ray, float rs, float a, const KerrConsts& c, float dlam) {
    float r = ray.r;
    float theta = ray.theta;
    float sin_t, cos_t;
    sincosf(theta, &sin_t, &cos_t);
    float sin2 = fmaxf(sin_t * sin_t, 1.0e-6f);

    float Delta = d_kerr_delta(r, a, rs);
    /* E is normalized to 1 in d_kerr_init_consts; A = (r^2+a^2)*E - a*Lz.
     * fmaf(r,r,a*a) replaces the non-fused r*r + a*a to emit FFMA not FMUL+FADD.
     * YSU-engine ncu audit: 6.6M non-fused vs 4.5M fused FP32 in this kernel;
     * explicit fmaf in hot loop body is the primary fix alongside --extra-device-vectorization. */
    float r2_a2 = fmaf(r, r, a * a);
    float A = fmaf(r2_a2, c.E, -a * c.Lz);
    float Lz_minus_aE = fmaf(-a, c.E, c.Lz);

    /* Precompute reciprocals once: MUFU.RCP = 41.55 cy on Ada (YSU-engine SASS RE).
     * inv_sin2 used in Theta AND dphi.  inv_delta used only for the outgoing
     * branch; the ingoing branch uses the rationalized form with no Delta. */
    float inv_sin2 = 1.0f / sin2;
    float Q_eff = fmaf(Lz_minus_aE, Lz_minus_aE, c.Q);

    float R = fmaf(A, A, -Delta * Q_eff);
    /* Theta = Q + a^2*E^2*cos^2 - Lz^2/sin^2.  E=1, so a^2*E^2 = a^2.
     * Use fmaf to chain Q + a^2*cos^2 - Lz^2*inv_sin2 without separate FADD. */
    float Theta = fmaf(a * a, cos_t * cos_t, fmaf(-c.Lz, c.Lz * inv_sin2, c.Q));

    if (R < 0.0f) ray.sign_r *= -1.0f;
    if (Theta < 0.0f) ray.sign_theta *= -1.0f;

    float sqrt_R = sqrtf(fmaxf(R, 0.0f));
    float sqrt_Theta = sqrtf(fmaxf(Theta, 0.0f));

    float dr_dlam     = ray.sign_r     * sqrt_R;
    float dtheta_dlam = ray.sign_theta * sqrt_Theta;

    /* Rationalized outgoing KS phi/t (task E1 upgrade -- no deltaSafe in denom).
     *
     * Ingoing ray (sign_r < 0): identity (A-sqrtR)/Delta = Q_eff/(A+sqrtR)
     * where Q_eff = c.Q + Lz_minus_aE^2.  Numerators vanish together with Delta
     * at r_+, but the ratio is finite.  No clamping required.
     * Using r^2+a^2-rs*r = Delta:
     *   [(r^2+a^2)*A - rs*r*sqrtR] / Delta = A + rs*r*Q_eff/(A+sqrtR)
     *
     * Outgoing ray (sign_r > 0): after a turning point Delta is bounded away
     * from 0 (ray moves away from horizon), so the standard KS formula with
     * inv_delta is numerically safe.  Both branches agree when sqrtR = 0. */
    float dphi_dlam, dt_dlam;
    /* dphi_dlam and dt_dlam share the term `c.Lz - a*c.E` (= Lz_minus_aE by definition).
     * Reuse it to avoid a redundant SUB instruction. */
    if (ray.sign_r < 0.0f) {
        float inv_Aps = 1.0f / fmaxf(A + sqrt_R, 1.0e-30f);
        dphi_dlam = fmaf(a, Q_eff * inv_Aps, fmaf(c.Lz, inv_sin2, -a * c.E));
        dt_dlam   = fmaf(rs * r, Q_eff * inv_Aps, A)
                    + a * fmaf(-a * c.E, sin2, c.Lz);
    } else {
        float inv_delta = 1.0f / fmaxf(Delta, 1.0e-6f);
        dphi_dlam = fmaf(a, (A + sqrt_R) * inv_delta, fmaf(c.Lz, inv_sin2, -a * c.E));
        /* r2_a2 = r^2+a^2 already computed above; reuse to save one FMUL. */
        dt_dlam   = fmaf(r2_a2, A, rs * r * sqrt_R) * inv_delta
                    + a * fmaf(-a * c.E, sin2, c.Lz);
    }

    ray.r += dlam * dr_dlam;
    ray.theta += dlam * dtheta_dlam;
    ray.phi += dlam * dphi_dlam;
    ray.t += dlam * dt_dlam;

    ray.theta = fminf(fmaxf(ray.theta, 1.0e-6f), D_PI - 1.0e-6f);
}

/* ========================================================================
 * Schwarzschild geodesic (from interop_trace.glsl)
 * ======================================================================== */

/**
 * @brief Compute the geodesic acceleration in the Schwarzschild metric.
 *
 * Uses the effective potential formula: a = -1.5 * rs * |L|^2 / r^5 * pos,
 * where L = pos x vel is the specific angular momentum.
 *
 * @param pos Current photon position.
 * @param vel Current photon velocity.
 * @param rs  Schwarzschild radius.
 * @return Acceleration 3-vector.
 */
__device__ __forceinline__ float3 d_schwarzschild_accel(float3 pos, float3 vel, float rs) {
    float r = d_length(pos);
    if (r < D_EPSILON) return make_f3(0.0f, 0.0f, 0.0f);

    float3 h = d_cross(pos, vel);
    float h2 = d_dot(h, h);
    float r5 = r * r * r * r * r;
    float coeff = -1.5f * rs * h2 / r5;
    return d_scale(pos, coeff);
}

/**
 * @brief Advance a Schwarzschild geodesic by one step using classic 4th-order Runge-Kutta.
 *
 * Updates position x and velocity v in-place using four evaluations of
 * d_schwarzschild_accel() with the standard RK4 coefficients (1/6, 1/3, 1/3, 1/6).
 *
 * @param[in,out] x  Photon position; updated by one step.
 * @param[in,out] v  Photon velocity; updated by one step.
 * @param rs         Schwarzschild radius.
 * @param dt         Step size.
 */
__device__ __forceinline__ void d_step_rk4(float3& x, float3& v, float rs, float dt) {
    float3 k1_x = v;
    float3 k1_v = d_schwarzschild_accel(x, v, rs);

    float3 x1 = d_add(x, d_scale(k1_x, 0.5f * dt));
    float3 v1 = d_add(v, d_scale(k1_v, 0.5f * dt));
    float3 k2_x = v1;
    float3 k2_v = d_schwarzschild_accel(x1, v1, rs);

    float3 x2 = d_add(x, d_scale(k2_x, 0.5f * dt));
    float3 v2 = d_add(v, d_scale(k2_v, 0.5f * dt));
    float3 k3_x = v2;
    float3 k3_v = d_schwarzschild_accel(x2, v2, rs);

    float3 x3 = d_add(x, d_scale(k3_x, dt));
    float3 v3 = d_add(v, d_scale(k3_v, dt));
    float3 k4_x = v3;
    float3 k4_v = d_schwarzschild_accel(x3, v3, rs);

    float s = dt / 6.0f;
    x = d_add(x, d_scale(d_add(d_add(k1_x, d_scale(d_add(k2_x, k3_x), 2.0f)), k4_x), s));
    v = d_add(v, d_scale(d_add(d_add(k1_v, d_scale(d_add(k2_v, k3_v), 2.0f)), k4_v), s));
}

/* ========================================================================
 * Disk intersection + redshift (from interop_trace.glsl)
 * ======================================================================== */

/**
 * @brief Test whether a ray segment crosses the equatorial accretion disk.
 *
 * Detects a sign change in z between old_pos and new_pos (equatorial plane
 * crossing), then linearly interpolates the crossing point and checks that
 * its cylindrical radius falls within [r_in, r_out].
 *
 * @param old_pos  Ray position at start of step.
 * @param new_pos  Ray position at end of step.
 * @param r_in     Inner disk radius.
 * @param r_out    Outer disk radius.
 * @param[out] hit Interpolated disk crossing point if true is returned.
 * @return true if the segment crosses the disk annulus, false otherwise.
 */
__device__ __forceinline__ bool d_check_disk(float3 old_pos, float3 new_pos,
                             float r_in, float r_out, float3& hit) {
    if (old_pos.z * new_pos.z > 0.0f) return false;
    float t = -old_pos.z / (new_pos.z - old_pos.z);
    hit = d_lerp(old_pos, new_pos, t);
    float r = sqrtf(fmaf(hit.x, hit.x, hit.y * hit.y));
    return r >= r_in && r <= r_out;
}

/**
 * @brief Compute the analytic Schwarzschild gravitational redshift factor sqrt(1 - rs/r).
 *
 * Returns 0 if r <= rs (inside or at the horizon).
 *
 * @param r  Emission radius.
 * @param rs Schwarzschild radius.
 * @return Redshift factor in [0, 1].
 */
__device__ __forceinline__ float d_redshift_factor(float r, float rs) {
    if (r <= rs) return 0.0f;
    float f = 1.0f - rs / r;
    if (f <= 0.0f) return 0.0f;
    return sqrtf(f);
}

/* ========================================================================
 * Hit result
 * ======================================================================== */

/**
 * @brief Outcome of tracing one geodesic ray through the scene.
 *
 * Exactly one of hit_disk, hit_horizon, or escaped will be true at exit.
 * min_radius records the closest approach to the black hole center, used
 * for the photon ring proximity glow in d_shade_hit().
 */

/* ========================================================================
 * BL-coordinate wiregrid overlay (mirrors shader/include/wiregrid.glsl)
 * ======================================================================== */

/**
 * @brief Compute Kerr event horizon radius r_+ = M + sqrt(M^2 - a^2), M=1.
 *
 * @param a_star Dimensionless Kerr spin parameter in [-1, 1).
 * @return Event horizon radius in geometric units (M=1).
 */
__device__ __forceinline__ float d_wg_event_horizon(float a_star) {
    float a = fmaxf(-0.9999f, fminf(a_star, 0.9999f));
    return 1.0f + sqrtf(fmaxf(1.0f - a * a, 0.0f));
}

/**
 * @brief Compute Kerr ergosphere outer boundary: r_ergo = M + sqrt(M^2 - a^2 cos^2 theta).
 *
 * @param a_star Dimensionless Kerr spin parameter.
 * @param theta  Polar angle in radians (0 = north pole, pi/2 = equator).
 * @return Ergosphere radius in geometric units (M=1).
 */
__device__ __forceinline__ float d_wg_ergosphere(float a_star, float theta) {
    float a = fmaxf(-0.9999f, fminf(a_star, 0.9999f));
    float cos_t = cosf(theta);
    return 1.0f + sqrtf(fmaxf(1.0f - a * a * cos_t * cos_t, 0.0f));
}

/**
 * @brief Kerr lapse function alpha = sqrt(1 - 2/r): proxy for spacetime curvature.
 *
 * Returns 0 inside or on the event horizon, and approaches 1 at large r.
 *
 * @param r      Radial coordinate in geometric units (M=1).
 * @param a_star Dimensionless Kerr spin parameter.
 * @return Lapse function value in [0, 1].
 */
__device__ __forceinline__ float d_wg_lapse(float r, float a_star) {
    if (r <= d_wg_event_horizon(a_star)) return 0.0f;
    return sqrtf(fmaxf(1.0f - 2.0f / r, 0.0f));
}

/**
 * @brief Frame dragging angular velocity Omega_ZAMO = 2Mar / (r^3 + a^2 r + 2a^2), M=1.
 *
 * @param r      Radial BL coordinate.
 * @param a_star Dimensionless Kerr spin parameter.
 * @return Frame-dragging frequency in geometric units.
 */
__device__ __forceinline__ float d_wg_frame_drag(float r, float a_star) {
    float a = fmaxf(-0.9999f, fminf(a_star, 0.9999f));
    float denom = r * r * r + a * a * r + 2.0f * a * a;
    return (denom < 1e-10f) ? 0.0f : (2.0f * a * r) / denom;
}

/**
 * @brief Smoothstep falloff: 1 at dist=0, 0 at dist=edge (GLSL smoothstep semantics).
 */
__device__ __forceinline__ float d_wg_smoothstep(float edge, float dist) {
    float t = fmaxf(0.0f, fminf(dist / fmaxf(edge, 1e-10f), 1.0f));
    return 1.0f - t * t * (3.0f - 2.0f * t);
}

__device__ __forceinline__ float d_wg_overlay_attenuation(float3 scene_color) {
    float const scene_luma = 0.2126f * scene_color.x +
                             0.7152f * scene_color.y +
                             0.0722f * scene_color.z;
    float const t = fmaxf(0.0f, fminf((scene_luma - 0.12f) / 0.78f, 1.0f));
    float const s = t * t * (3.0f - 2.0f * t);
    return 1.0f + s * (0.18f - 1.0f);
}

__device__ __forceinline__ float d_wg_overlay_blend_alpha(float4 wg, float3 scene_color) {
    float const preserve = fminf(fmaxf(d_wiregrid_scene_preserve, 0.0f), 1.0f);
    float const attenuation = 1.0f + (d_wg_overlay_attenuation(scene_color) - 1.0f) * preserve;
    return fminf(fmaxf(wg.w * attenuation * fmaxf(d_wiregrid_strength, 0.0f), 0.0f), 1.0f);
}

__device__ __forceinline__ float d_wg_radial_line(float r, float a_star, float spacing,
                                                  float width, float time_sec,
                                                  float infall_scale) {
    float const r_h = d_wg_event_horizon(a_star);
    float const r_local = fmaxf(r - r_h + 0.05f, 0.05f);
    float const lapse = 1.0f - d_wg_lapse(r, a_star);
    float const inward_phase = time_sec * infall_scale * (0.2f + lapse * 1.1f);
    float const radial_coord = logf(r_local) - inward_phase;
    float phase = fmodf(radial_coord, spacing);
    if (phase < 0.0f) phase += spacing;
    float const dist = fminf(phase, spacing - phase);
    return d_wg_smoothstep(width, dist);
}

/**
 * @brief Per-pixel Boyer-Lindquist coordinate wiregrid overlay (CUDA device equivalent of
 *        GLSL wiregridOverlay() in shader/include/wiregrid.glsl).
 *
 * Evaluates spherical BL coordinate grid lines (constant phi and theta) plus optional
 * ergosphere boundary and interior glow.  Designed to be called with the Cartesian
 * hit_point converted to BL spherical approximation:
 *   r     = length(hit_point)
 *   theta = acosf(hit_point.z / r)
 *   phi   = atan2f(hit_point.y, hit_point.x)
 *
 * @param r         BL radial coordinate in geometric units (M=1).
 * @param theta     Polar angle in radians.
 * @param phi       Azimuthal angle in radians.
 * @param a_star    Dimensionless Kerr spin parameter.
 * @param show_ergo Non-zero to show ergosphere boundary and interior glow.
 * @param grid_scale Grid density multiplier (1.0 = pi/6 spacing, 2.0 = pi/12, etc.).
 * @return float4 RGBA overlay: .xyz = color, .w = opacity to blend with scene.
 */
__device__ __forceinline__ float4 d_wiregrid_overlay(float r, float theta, float phi,
                                                       float a_star, int show_ergo,
                                                       float grid_scale) {
    const float k_pi6 = 0.523598776f; // pi/6
    float spacing = k_pi6 / fmaxf(grid_scale, 0.01f);
    float lw      = 0.02f / fmaxf(grid_scale, 0.01f);
    float radial_spacing = 0.34f / fmaxf(grid_scale, 0.01f);
    float drag = d_wg_frame_drag(r, a_star) * d_time_sec * d_wiregrid_motion_scale *
                 (0.25f + (1.0f - d_wg_lapse(r, a_star)) * 1.15f);

    // Phi grid line
    float phi_phase = fmodf(phi - drag, spacing);
    if (phi_phase < 0.0f) phi_phase += spacing;
    float phi_dist = fminf(phi_phase, spacing - phi_phase);
    float phi_line = d_wg_smoothstep(lw, phi_dist);

    // Theta grid line
    float theta_phase = fmodf(theta, spacing);
    float theta_dist  = fminf(theta_phase, spacing - theta_phase);
    float theta_line  = d_wg_smoothstep(lw, theta_dist);
    float radial_line = d_wg_radial_line(r, a_star, radial_spacing, lw * 1.15f,
                                         d_time_sec, d_wiregrid_infall_scale);

    float grid  = fmaxf(fmaxf(phi_line, theta_line), radial_line * 0.58f);
    float boost = 1.0f + (1.0f - d_wg_lapse(r, a_star)) * 2.0f; // 3x near horizon
    grid *= boost;

    float grid_alpha = fminf(grid * d_wiregrid_color[3], 0.72f);

    float ergo_alpha = 0.0f;
    if (show_ergo) {
        float r_ergo = d_wg_ergosphere(a_star, theta);
        float boundary = d_wg_smoothstep(0.2f, fabsf(r - r_ergo));
        float r_plus = d_wg_event_horizon(a_star);
        float interior = 0.0f;
        if (r > r_plus && r < r_ergo) {
            float omega     = d_wg_frame_drag(r, a_star);
            float omega_max = d_wg_frame_drag(r_plus + 0.01f, a_star);
            interior = (omega / fmaxf(omega_max, 1e-10f)) * 0.3f;
        }
        ergo_alpha = fmaxf(boundary * 0.58f, interior * 0.6f);
    }

    float total = grid_alpha + ergo_alpha;
    float t = ergo_alpha / fmaxf(total, 0.01f);
    float cr = d_wiregrid_color[0] + t * (1.0f - d_wiregrid_color[0]);
    float cg = d_wiregrid_color[1] + t * (0.3f - d_wiregrid_color[1]);
    float cb = d_wiregrid_color[2] + t * (0.0f - d_wiregrid_color[2]);
    float ca = fmaxf(grid_alpha, ergo_alpha);
    return make_float4(cr, cg, cb, ca);
}

struct HitResult {
    bool hit_disk;     /**< @brief Ray terminated on the accretion disk. */
    bool hit_horizon;  /**< @brief Ray crossed the event horizon. */
    bool escaped;      /**< @brief Ray escaped to infinity (r > max_dist or step budget exhausted). */
    float3 hit_point;  /**< @brief World-space position of the termination event. */
    float3 closest_approach_point; /**< @brief World-space position at minimum radius along the ray. */
    float phi;         /**< @brief Azimuthal angle at disk hit (for Doppler beaming); 0 otherwise. */
    float redshift;    /**< @brief Gravitational redshift factor at disk hit; 1 otherwise. */
    float min_radius;  /**< @brief Minimum radial distance reached along this ray. */
};

/* ========================================================================
 * Adaptive step size (D10: AMR geodesic refinement near critical surfaces)
 * ======================================================================== */

/**
 * @brief Compute an adaptive Mino-time step for the Kerr geodesic integrator.
 *
 * Reduces the base step near two critical surfaces where fixed steps accumulate
 * the most integration error:
 *
 *   1. Event horizon (r -> r_h): step scales as (r - r_h)/rs, clamped to
 *      [0.1, 1.0].  Ensures the horizon-termination check triggers before the
 *      ray can jump across it on a coarse step.
 *
 *   2. Photon sphere (r ~ r_ph ~ 1.5*rs): rays that orbit near the light ring
 *      accumulate angular error with coarse steps.  A smooth falloff centered
 *      on r_ph halves the step at the photon sphere.
 *
 *   3. Far-field overshoot prevention: in Mino time dr/dlambda = sqrt(R) ~ r^2
 *      for large r (nearly-radial photon).  With the default base_dt = 0.08
 *      and r = 350, one step moves dr ~ 350^2 * 0.08 = 9800, overshooting
 *      the BH entirely.  Zone 3 limits each step to at most 0.5 * r in radial
 *      distance by capping dlambda * sqrt(R) <= 0.5 * r.  Since sqrt(R) <= r^2
 *      (upper bound for the generic case), the required scale is 0.5 / r.
 *      This makes scale_far ~ 0.5/r for large r and converges to 1.0 at r = 0.5.
 *
 * WHY Mino time: d_kerr_step() integrates in Mino time lambda.  The adaptive
 * step is applied to the same Mino time increment dt, not to proper time.  This
 * is correct because Mino time is the affine parameter for Kerr geodesics.
 *
 * @param r       Current BL radial coordinate.
 * @param rs      Schwarzschild radius.
 * @param r_h     Outer event horizon radius (d_kerr_outer_horizon result).
 * @param base_dt Base Mino time step from __constant__ d_step_size.
 * @return        Adaptive step in (0, base_dt].
 */
__device__ __forceinline__ float d_adaptive_step(float r, float rs, float r_h,
                                                  float base_dt) {
    /* Zone 1: horizon proximity -- scale ~ (r - r_h) / rs */
    float const d_horiz = r - r_h;
    float const scale_h = fmaxf(0.1f, fminf(1.0f, d_horiz / fmaxf(rs, D_EPSILON)));

    /* Zone 2: photon-sphere proximity -- smooth falloff centered on r_ph.
     * r_ph ~ 1.5*rs (Schwarzschild limit); Kerr shifts this but 1.5*rs is a
     * conservative upper bound that still gives useful refinement. */
    float const r_ph    = 1.5f * rs;
    float const d_ph    = fabsf(r - r_ph) / fmaxf(rs, D_EPSILON);
    /* scale_ph: 0.5 at r_ph, rises to 1.0 at |r - r_ph| = 0.5*rs */
    float const scale_ph = fminf(1.0f, 0.5f + d_ph);

    /* Zone 3: far-field Mino-time step limiting.
     * sqrt(R) ~ r^2 for large r, so dr ~ r^2 * dlam per step.  Without this
     * zone, a camera at r = 350 with dlam = 0.08 would jump dr = 9800 and
     * overshoot the BH in one step, producing an all-black image.
     * scale_far = min(1, 0.5/r): at r = 350 gives scale = 0.00143 (dr ~ 14),
     * at r = 10 gives scale = 0.05 (dr ~ 0.4), at r = 2 zone 1 dominates. */
    float const scale_far = fminf(1.0f, 0.5f / fmaxf(r, D_EPSILON));

    return base_dt * fminf(scale_far, fminf(scale_h, scale_ph));
}

/* ========================================================================
 * Full geodesic trace (from bhTraceGeodesic)
 * ======================================================================== */

/**
 * @brief Trace a single geodesic ray through the Kerr or Schwarzschild spacetime.
 *
 * Dispatches to the Kerr Mino-time integrator (d_kerr_step) when d_kerr_enabled
 * is set and |a| > D_EPSILON, otherwise uses the Schwarzschild RK4 integrator
 * (d_step_rk4). Checks for horizon crossing, disk intersection, and escape at
 * each step. All scene parameters are read from __constant__ memory.
 *
 * @param cam_pos Camera position in world (Cartesian) coordinates.
 * @param ray_dir Normalized ray direction in world coordinates.
 * @return HitResult describing where and how the ray terminated.
 */
__device__ __forceinline__ HitResult d_trace_geodesic(float3 cam_pos, float3 ray_dir) {
    HitResult result;
    result.hit_disk = false;
    result.hit_horizon = false;
    result.escaped = false;
    result.hit_point = make_f3(0.0f, 0.0f, 0.0f);
    result.closest_approach_point = cam_pos;
    result.phi = 0.0f;
    result.redshift = 1.0f;
    result.min_radius = d_length(cam_pos);

    float rs = d_rs;
    float a = 0.5f * d_spin * rs;
    float dt = d_step_size;
    int max_steps = d_max_steps;
    float max_dist = d_max_dist;

    if (d_kerr_enabled && fabsf(a) > D_EPSILON) {
        /* Kerr geodesic integration */
        float r_horizon = d_kerr_outer_horizon(rs, a);
        if (r_horizon <= D_EPSILON) r_horizon = rs;
        float r_disk_in = d_isco;
        float r_disk_out = 30.0f * rs;

        KerrConsts c = d_kerr_init_consts(cam_pos, ray_dir, rs, a);
        KerrRay kr = d_kerr_init_ray(cam_pos, ray_dir);

        for (int step = 0; step < max_steps; ++step) {
            float3 old_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
            if (kr.r < result.min_radius) {
                result.min_radius = kr.r;
                result.closest_approach_point = old_pos;
            }

            if (kr.r <= r_horizon) {
                result.hit_horizon = true;
                result.hit_point = old_pos;
                return result;
            }

            /* D10: AMR step refinement near horizon and photon sphere */
            float const step_dt = d_adaptive_step(kr.r, rs, r_horizon, dt);
            d_kerr_step(kr, rs, a, c, step_dt);
            float3 new_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

            if (d_adisk_enabled) {
                float3 disk_hit;
                if (d_check_disk(old_pos, new_pos, r_disk_in, r_disk_out, disk_hit)) {
                    result.hit_disk = true;
                    result.hit_point = disk_hit;
                    result.phi = atan2f(disk_hit.y, disk_hit.x);
                    result.redshift = d_redshift_factor(d_length(disk_hit), rs);
                    return result;
                }
            }

            if (kr.r > max_dist) {
                result.escaped = true;
                result.hit_point = new_pos;
                return result;
            }
        }
        result.escaped = true;
        result.hit_point = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
    } else {
        /* Schwarzschild geodesic integration */
        float3 pos = cam_pos;
        float3 vel = ray_dir;
        float r_disk_in = d_isco;
        float r_disk_out = 30.0f * rs;

        for (int step = 0; step < max_steps; ++step) {
            float3 old_pos = pos;
            d_step_rk4(pos, vel, rs, dt);

            float r = d_length(pos);
            if (r < result.min_radius) {
                result.min_radius = r;
                result.closest_approach_point = pos;
            }

            if (r <= rs) {
                result.hit_horizon = true;
                result.hit_point = pos;
                return result;
            }

            if (d_adisk_enabled) {
                float3 disk_hit;
                if (d_check_disk(old_pos, pos, r_disk_in, r_disk_out, disk_hit)) {
                    result.hit_disk = true;
                    result.hit_point = disk_hit;
                    result.phi = atan2f(disk_hit.y, disk_hit.x);
                    result.redshift = d_redshift_factor(d_length(disk_hit), rs);
                    return result;
                }
            }

            if (r > max_dist) {
                result.escaped = true;
                result.hit_point = pos;
                return result;
            }
        }
        result.escaped = true;
        result.hit_point = pos;
    }
    return result;
}

/* ========================================================================
 * Synchrotron G(x) = x * K_{2/3}(x) -- polarized emission function
 * ======================================================================== */

/**
 * @brief Synchrotron polarization function G(x) = x * K_{2/3}(x).
 *
 * Matches synchrotron_emission.glsl::synchrotron_G().
 * Domain constants (log-spaced LUT): x in [0.001, 30].
 * Asymptotes: small-x: 1.3541*x^(1/3); large-x: sqrt(pi/(2x))*exp(-x)*x.
 *
 * Sampling: log-space u = log(x/xMin) / log(xMax/xMin), tex2D height=0.5.
 * Fallback: polynomial 1.3541*x^(1/3)*exp(-x)*(1+0.6*x^(2/3)) if LUT absent.
 *
 * @param x Dimensionless frequency (nu / nu_c).
 * @return G(x) value, 0 if x <= 0.
 */
__device__ __forceinline__ float d_synchrotron_G(float x) {
    if (x <= 0.0f) return 0.0f;

    /* Small-x asymptote: G(x) ~ 1.3541 * x^(1/3) (exact at x -> 0) */
    if (x < 0.001f) {
        return 1.3541f * cbrtf(x);
    }

    /* Large-x asymptote: G(x) ~ sqrt(pi/(2x)) * exp(-x) * x */
    if (x > 30.0f) {
        return sqrtf(1.5707963268f / x) * expf(-x) * x;
    }

    /* LUT mid-range: log-spaced texture lookup */
    if (d_tex_synch_g) {
        /* log(xMax/xMin) = log(30/0.001) = log(30000) */
        float const log_ratio = 10.30895f; /* log(30000) precomputed */
        float const u = __logf(x / 0.001f) / log_ratio;
        return tex2D<float>((cudaTextureObject_t)d_tex_synch_g, u, 0.5f);
    }

    /* Polynomial fallback (~10% error for x in [1,10]) */
    float const x13 = cbrtf(x);
    return 1.3541f * x13 * expf(-x) * (1.0f + 0.6f * x13 * x13);
}

/* ========================================================================
 * Shading (from interop_trace.glsl: bhDiskColorFromHit, bhShadeHit)
 * ======================================================================== */

/**
 * @brief Compute RGBA color for a disk hit using Novikov-Thorne flux and Doppler beaming.
 *
 * If d_use_luts and d_tex_emissivity are set, samples the emissivity LUT for
 * flux; otherwise uses the analytic Novikov-Thorne x^3*(1-sqrt(x)) formula.
 * Applies a smooth blackbody color ramp (6 segments), optional spectral LUT
 * modulation, Doppler beaming (intensity ~ doppler^3), Doppler color shift,
 * and optional gravitational redshift (LUT or analytic).
 *
 * @param hit Result of a disk-terminated geodesic trace.
 * @param rs  Schwarzschild radius.
 * @return RGBA float4 with pre-multiplied intensity.
 */
__device__ __forceinline__ float4 d_disk_color(const HitResult& hit, float3 cam_pos, float rs) {
    float r = sqrtf(fmaf(hit.hit_point.x, hit.hit_point.x,
                         hit.hit_point.y * hit.hit_point.y));
    float inner_radius = d_isco;
    float outer_radius = inner_radius * 4.0f;
    float radial01 =
        fmaxf(0.0f, fminf((r - inner_radius) / fmaxf(outer_radius - inner_radius, D_EPSILON), 1.0f));

    /* Emissivity flux: LUT or analytic Novikov-Thorne */
    float flux;
    if (d_use_luts && d_tex_emissivity) {
        float rNorm = r / fmaxf(rs, D_EPSILON);
        float denom = fmaxf(d_lut_radius_max - d_lut_radius_min, 1e-4f);
        float u = fmaxf(0.0f, fminf(1.0f, (rNorm - d_lut_radius_min) / denom));
        flux = fmaxf(0.0f, tex2D<float>((cudaTextureObject_t)d_tex_emissivity,
                                         u, 0.5f));
    } else {
        float r_in = d_isco;
        float x = r_in / fmaxf(r, D_EPSILON);
        flux = fmaxf(0.0f, x * x * x * (1.0f - sqrtf(x)));
    }

    /* x^0.25 = sqrtf(sqrtf(x)): 2x MUFU.SQRT ~16 cy vs powf LG2+EX2 ~35 cy. */
    float T_norm = sqrtf(sqrtf(flux));

    /* Smooth blackbody color ramp with 8 interpolation points.
     * Deep red -> orange -> golden -> yellow-white -> hot white. */
    float3 color;
    if (T_norm > 0.85f) {
        float t = (T_norm - 0.85f) / 0.15f;
        color = d_lerp(make_f3(1.0f, 0.90f, 0.60f), make_f3(1.0f, 0.97f, 0.90f), t);
    } else if (T_norm > 0.65f) {
        float t = (T_norm - 0.65f) / 0.20f;
        color = d_lerp(make_f3(1.0f, 0.70f, 0.20f), make_f3(1.0f, 0.90f, 0.60f), t);
    } else if (T_norm > 0.45f) {
        float t = (T_norm - 0.45f) / 0.20f;
        color = d_lerp(make_f3(1.0f, 0.45f, 0.04f), make_f3(1.0f, 0.70f, 0.20f), t);
    } else if (T_norm > 0.25f) {
        float t = (T_norm - 0.25f) / 0.20f;
        color = d_lerp(make_f3(0.90f, 0.15f, 0.00f), make_f3(1.0f, 0.45f, 0.04f), t);
    } else if (T_norm > 0.10f) {
        float t = (T_norm - 0.10f) / 0.15f;
        color = d_lerp(make_f3(0.50f, 0.03f, 0.00f), make_f3(0.90f, 0.15f, 0.00f), t);
    } else {
        float t = T_norm / 0.10f;
        color = d_lerp(make_f3(0.10f, 0.00f, 0.00f), make_f3(0.50f, 0.03f, 0.00f), t);
    }

    /* Spectral LUT modulation */
    float spectral = 1.0f;
    if (d_use_luts && d_tex_spectral) {
        float rNorm = r / fmaxf(rs, D_EPSILON);
        float denom = fmaxf(d_spectral_radius_max - d_spectral_radius_min, 1e-4f);
        float u = fmaxf(0.0f, fminf(1.0f,
                    (rNorm - d_spectral_radius_min) / denom));
        spectral = fmaxf(0.0f, tex2D<float>((cudaTextureObject_t)d_tex_spectral,
                                             u, 0.5f));
    }

    /* Give the inner disk a hotter thermal read and stronger asymmetric structure,
     * matching the GLSL desktop lane more closely than the old flat ramp. */
    float3 thermal_inner = make_f3(1.35f, 0.78f, 0.28f);
    float3 thermal_outer = make_f3(0.92f, 0.86f, 0.78f);
    float radial_sqrt = sqrtf(radial01);
    float3 thermal_tint = d_lerp(thermal_inner, thermal_outer, radial_sqrt);
    color = make_f3(color.x * thermal_tint.x, color.y * thermal_tint.y, color.z * thermal_tint.z);

    float3 ray_dir = d_normalize(d_sub(hit.hit_point, cam_pos));
    float3 view_dir = d_scale(ray_dir, -1.0f);
    float3 vel_dir = d_normalize(make_f3(-hit.hit_point.z, 0.0f, hit.hit_point.x));

    /* WHY: GLSL interop_trace.glsl uses flux*2.0 as base intensity. d_adisk_lit matches
     * the adiskLit uniform that record mode sets to 0.35 for cinematic brightness balance. */
    float intensity = flux * 2.0f * d_adisk_lit * spectral;

    /* Doppler beaming approximation */
    float v = sqrtf(0.5f * rs / fmaxf(r, D_EPSILON));
    float view_alignment = d_dot(vel_dir, d_normalize(ray_dir));
    float doppler = 1.0f + view_alignment * 0.65f * d_doppler_strength;
    intensity *= doppler * doppler * doppler;

    float spin_y = d_spin >= 0.0f ? 1.0f : -1.0f;
    float3 spin_axis = make_f3(0.0f, spin_y, 0.0f);
    float3 flow_dir = d_normalize(d_cross(spin_axis, d_normalize(hit.hit_point)));
    float spin_view = 0.5f + 0.5f * d_dot(flow_dir, view_dir);
    float spin_t = fmaxf(0.0f, fminf((fabsf(d_spin) - 0.05f) / fmaxf(0.85f - 0.05f, D_EPSILON), 1.0f));
    float spin_weight = spin_t * spin_t * (3.0f - 2.0f * spin_t);
    float anisotropic_boost = 1.0f + ((0.82f + (1.55f - 0.82f) * spin_view) - 1.0f) * spin_weight;
    color = d_scale(color, anisotropic_boost);

    /* Keep the disk energy concentrated in a narrow, approaching-side sector.
     * The GLSL/desktop still wins because it preserves dark negative space and
     * lets only a small inner crescent survive with high local contrast. */
    float inner_weight = powf(fmaxf(0.0f, 1.0f - radial01), 0.72f);
    auto smooth_range = [](float edge0, float edge1, float x) {
        float t = fmaxf(0.0f, fminf((x - edge0) / fmaxf(edge1 - edge0, D_EPSILON), 1.0f));
        return t * t * (3.0f - 2.0f * t);
    };
    float bright_sector = smooth_range(0.83f, 0.985f, spin_view);
    float rim_sector = smooth_range(0.91f, 0.997f, spin_view);
    float counter_sector = smooth_range(0.20f, 0.54f, spin_view);
    float sector_shadow =
        1.0f + (0.18f - 1.0f) * inner_weight * (1.0f - bright_sector * 0.94f);
    float sector_lift =
        1.0f + inner_weight * (0.92f * bright_sector + 0.22f * rim_sector + 0.04f * counter_sector);
    intensity *= sector_shadow * sector_lift;

    float grazing = powf(fmaxf(0.0f, fminf(1.0f - fabsf(ray_dir.y), 1.0f)), 1.5f);
    color = d_scale(color, 1.0f + (1.55f - 1.0f) * grazing);

    float normalized_v = fabsf(hit.hit_point.y) / fmaxf(0.42f, D_EPSILON);
    float midplane_boost = powf(fmaxf(0.0f, fminf(1.0f - normalized_v, 1.0f)), 0.45f);
    float crescent_boost = 1.0f + (1.8f - 1.0f) * (midplane_boost * (1.0f - radial01));
    color = d_scale(color, crescent_boost);

    float disk_luma = 0.2126f * color.x + 0.7152f * color.y + 0.0722f * color.z;
    float sector_contrast =
        inner_weight * ((-0.36f) + (0.26f - (-0.36f)) * bright_sector);
    color = d_add(
        color,
        d_scale(color, sector_contrast * fmaxf(fminf(disk_luma - 0.05f, 1.0f), 0.0f)));

    float exclusion = inner_weight * (1.0f - bright_sector) *
                      smooth_range(0.05f, 0.25f, disk_luma);
    color = d_scale(color, 1.0f - 0.22f * exclusion);

    /* Doppler color shift: approaching side -> blueshift, receding -> redshift */
    if (doppler > 1.0f) {
        /* Blueshift: shift color toward blue-white */
        float shift = fminf((doppler - 1.0f) * 1.5f, 0.6f);
        color = d_lerp(color, make_f3(0.7f, 0.85f, 1.0f), shift);
    } else {
        /* Redshift: shift color toward deep red */
        float shift = fminf((1.0f - doppler) * 2.0f, 0.7f);
        color = d_lerp(color, make_f3(0.6f, 0.05f, 0.0f), shift);
    }

    /* Gravitational redshift: LUT or analytic */
    if (d_redshift_enabled) {
        float z;
        if (d_use_luts && d_tex_redshift) {
            float rNorm = r / fmaxf(rs, D_EPSILON);
            float denom = fmaxf(d_redshift_radius_max - d_redshift_radius_min,
                                1e-4f);
            float u = fmaxf(0.0f, fminf(1.0f,
                        (rNorm - d_redshift_radius_min) / denom));
            z = tex2D<float>((cudaTextureObject_t)d_tex_redshift, u, 0.5f);
        } else {
            z = 1.0f / fmaxf(hit.redshift, D_EPSILON) - 1.0f;
        }
        float one_plus_z = 1.0f + z;
        float dimming = 1.0f / (one_plus_z * one_plus_z * one_plus_z);
        color = d_scale(color, dimming);
    }

    float inner_boost = 1.8f + (0.85f - 1.8f) * powf(radial01, 0.65f);
    intensity *= inner_boost;

    return make_float4(color.x * intensity, color.y * intensity,
                       color.z * intensity, 1.0f);
}

/**
 * @brief Integer multiply-xorshift hash for the procedural star field.
 *
 * Converts integer-valued floats (from floorf() grid coordinates) to unsigned
 * integers and mixes them with PCG-style multiply-xorshift. Maps the top 23
 * bits of the result to [0, 1), avoiding fmodf and MUFU.SIN entirely.
 *
 * @param p Grid cell coordinates as integer-valued floats.
 * @return Pseudo-random float in [0, 1).
 */
__device__ __forceinline__ float d_hash(float3 p) {
    /* Cast integer-valued floats to signed int, then to unsigned for safe mixing */
    unsigned int ix = (unsigned int)((int)p.x + 16384);
    unsigned int iy = (unsigned int)((int)p.y + 16384);
    unsigned int iz = (unsigned int)((int)p.z + 16384);
    unsigned int h = ix * 1664525u ^ iy * 22695477u ^ iz * 1013904223u;
    h ^= h >> 16;
    h *= 0x45d9f3bu;
    h ^= h >> 16;
    /* Map top 23 bits to [0, 1) -- avoids fmodf entirely */
    return (float)(h >> 9) * (1.0f / 8388608.0f);
}

/**
 * @brief Sample the galaxy cubemap background at ray direction @p dir.
 *
 * WHY: The OpenGL path samples a GL_TEXTURE_CUBE_MAP via @c texture(galaxy, dir)
 *      which the driver dispatches using hardware cubemap addressing.  The CUDA
 *      path receives the same six-face data stored in a tex2DLayered object
 *      (see lut_manager.cu::lutRegisterCubemap).  This function replicates the
 *      face selection and UV normalisation that the GL fixed function performs.
 *
 * FACE ORDERING (matches GL_TEXTURE_CUBE_MAP_POSITIVE_X sequence):
 *   layer 0 = +X (right),  layer 1 = -X (left),
 *   layer 2 = +Y (top),    layer 3 = -Y (bottom),
 *   layer 4 = +Z (front),  layer 5 = -Z (back)
 *
 * HOW (standard cubemap face selection):
 *   Find dominant axis; divide the other two components by its magnitude to
 *   get face coordinates in [-1,1]; remap to [0,1] for normalised tex coords.
 *   The sign conventions follow OpenGL spec section 8.13 (cube map face
 *   selection, Table 8.19).
 *
 * @param dir Un-normalised ray direction (length != 0).
 * @return RGB sky colour in linear light (alpha discarded).  Returns (0,0,0)
 *         if d_tex_galaxy is 0 (not registered) or if @p dir is zero.
 */
__device__ __forceinline__ float3 d_sample_galaxy_cubemap_raw(float3 dir) {
    if (!d_tex_galaxy) {
        return make_f3(0.0f, 0.0f, 0.0f);
    }

    if (fabsf(d_background_yaw_rad) > D_EPSILON) {
        float const cy = cosf(d_background_yaw_rad);
        float const sy = sinf(d_background_yaw_rad);
        dir = make_f3(
            dir.x * cy + dir.z * sy,
            dir.y,
            -dir.x * sy + dir.z * cy);
    }

    if (fabsf(d_background_pitch_rad) > D_EPSILON) {
        float const cp = cosf(d_background_pitch_rad);
        float const sp = sinf(d_background_pitch_rad);
        dir = make_f3(
            dir.x,
            dir.y * cp - dir.z * sp,
            dir.y * sp + dir.z * cp);
    }

    float ax = fabsf(dir.x);
    float ay = fabsf(dir.y);
    float az = fabsf(dir.z);

    float u, v;
    int   layer;

    if (ax >= ay && ax >= az) {
        /* Dominant X axis */
        float sc = 1.0f / fmaxf(ax, D_EPSILON);
        if (dir.x > 0.0f) {
            /* +X face: s = -z/|x|, t = -y/|x| */
            layer = 0; u = -dir.z * sc; v = -dir.y * sc;
        } else {
            /* -X face: s = +z/|x|, t = -y/|x| */
            layer = 1; u = dir.z * sc;  v = -dir.y * sc;
        }
    } else if (ay >= ax && ay >= az) {
        /* Dominant Y axis */
        float sc = 1.0f / fmaxf(ay, D_EPSILON);
        if (dir.y > 0.0f) {
            /* +Y face: s = +x/|y|, t = +z/|y| */
            layer = 2; u = dir.x * sc;  v = dir.z * sc;
        } else {
            /* -Y face: s = +x/|y|, t = -z/|y| */
            layer = 3; u = dir.x * sc;  v = -dir.z * sc;
        }
    } else {
        /* Dominant Z axis */
        float sc = 1.0f / fmaxf(az, D_EPSILON);
        if (dir.z > 0.0f) {
            /* +Z face: s = +x/|z|, t = -y/|z| */
            layer = 4; u = dir.x * sc;  v = -dir.y * sc;
        } else {
            /* -Z face: s = -x/|z|, t = -y/|z| */
            layer = 5; u = -dir.x * sc; v = -dir.y * sc;
        }
    }

    /* Remap face coordinates from [-1,1] to normalised [0,1] */
    u = 0.5f * (u + 1.0f);
    v = 0.5f * (v + 1.0f);

    float4 s = tex2DLayered<float4>((cudaTextureObject_t)d_tex_galaxy, u, v, layer);
    return make_f3(s.x, s.y, s.z);
}

__device__ __forceinline__ float d_fract(float x) {
    return x - floorf(x);
}

__device__ __forceinline__ float2 d_dir_to_uv(float3 dir) {
    float3 const n = d_normalize(dir);
    float const u = atan2f(n.z, n.x) * D_INV_TWO_PI + 0.5f;
    float const v = asinf(fmaxf(-1.0f, fminf(n.y, 1.0f))) * D_INV_PI + 0.5f;
    return make_float2(u, v);
}

__device__ __forceinline__ float3 d_rotate_background_dir(float3 dir) {
    if (fabsf(d_background_yaw_rad) > D_EPSILON) {
        float const cy = cosf(d_background_yaw_rad);
        float const sy = sinf(d_background_yaw_rad);
        dir = make_f3(
            dir.x * cy + dir.z * sy,
            dir.y,
            -dir.x * sy + dir.z * cy);
    }

    if (fabsf(d_background_pitch_rad) > D_EPSILON) {
        float const cp = cosf(d_background_pitch_rad);
        float const sp = sinf(d_background_pitch_rad);
        dir = make_f3(
            dir.x,
            dir.y * cp - dir.z * sp,
            dir.y * sp + dir.z * cp);
    }
    return dir;
}

__device__ __forceinline__ float3 d_sample_galaxy_cubemap(float3 dir) {
    float3 n = d_normalize(dir);
    float radius = fmaxf(d_background_filter_radius, 0.0f);
    if (radius <= D_EPSILON) {
        return d_sample_galaxy_cubemap_raw(d_rotate_background_dir(n));
    }

    float3 up = (fabsf(n.y) < 0.9f) ? make_f3(0.0f, 1.0f, 0.0f) : make_f3(1.0f, 0.0f, 0.0f);
    float3 tangent = d_normalize(d_cross(up, n));
    float3 bitangent = d_normalize(d_cross(n, tangent));

    float3 sum = d_sample_galaxy_cubemap_raw(d_rotate_background_dir(n));
    sum = d_add(sum, d_sample_galaxy_cubemap_raw(d_rotate_background_dir(
        d_normalize(d_add(n, d_scale(tangent, radius))))));
    sum = d_add(sum, d_sample_galaxy_cubemap_raw(d_rotate_background_dir(
        d_normalize(d_add(n, d_scale(tangent, -radius))))));
    sum = d_add(sum, d_sample_galaxy_cubemap_raw(d_rotate_background_dir(
        d_normalize(d_add(n, d_scale(bitangent, radius))))));
    sum = d_add(sum, d_sample_galaxy_cubemap_raw(d_rotate_background_dir(
        d_normalize(d_add(n, d_scale(bitangent, -radius))))));
    return d_scale(sum, 0.2f);
}

__device__ __forceinline__ float3 d_sample_background_equirect(float3 dir) {
    if (!d_tex_background_equirect) {
        return make_f3(0.0f, 0.0f, 0.0f);
    }

    float3 const n = d_rotate_background_dir(d_normalize(dir));
    float2 const uv = d_dir_to_uv(n);
    float const u = uv.x;
    float const v = uv.y;
    float4 const s = tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect, u, v, 0.0f);
    return make_f3(s.x, s.y, s.z);
}

__device__ __forceinline__ float3 d_sample_background_equirect_layered(float3 dir, float *weight_out) {
    if (weight_out != nullptr) {
        *weight_out = 0.0f;
    }
    if (!d_tex_background_equirect) {
        return make_f3(0.0f, 0.0f, 0.0f);
    }

    float3 const n = d_rotate_background_dir(d_normalize(dir));
    float2 const base_uv = d_dir_to_uv(n);
    float radius = fmaxf(d_background_filter_radius, 0.0f);
    float3 accum = make_f3(0.0f, 0.0f, 0.0f);
    float total_weight = 0.0f;

    for (int i = 0; i < 3; ++i) {
        float const offset_x = d_background_layer_params[i * 4 + 0];
        float const offset_y = d_background_layer_params[i * 4 + 1];
        float const scale = d_background_layer_params[i * 4 + 2];
        float const weight = d_background_layer_params[i * 4 + 3];
        if (weight <= 0.0f || scale <= D_EPSILON) {
            continue;
        }

        float const u = d_fract(base_uv.x * scale + offset_x);
        float const v = d_fract(base_uv.y * scale + offset_y);
        float const lod_bias = fmaxf(d_background_layer_lod_bias[i], 0.0f);
        float const base_radius = fmaxf(radius, 0.0015f);
        float const layer_radius = base_radius * (1.0f + 1.5f * lod_bias);

        float4 sample =
            tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect, u, v, lod_bias);
        if (layer_radius > D_EPSILON) {
            float const diagonal_radius = layer_radius * 0.70710678f;
            float4 sample_pos_u =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u + layer_radius), v, lod_bias);
            float4 sample_neg_u =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u - layer_radius), v, lod_bias);
            float v_pos = fminf(v + layer_radius, 1.0f);
            float v_neg = fmaxf(v - layer_radius, 0.0f);
            float4 sample_pos_v =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect, u, v_pos, lod_bias);
            float4 sample_neg_v =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect, u, v_neg, lod_bias);
            float4 sample_pp =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u + diagonal_radius), fminf(v + diagonal_radius, 1.0f), lod_bias);
            float4 sample_pn =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u + diagonal_radius), fmaxf(v - diagonal_radius, 0.0f), lod_bias);
            float4 sample_np =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u - diagonal_radius), fminf(v + diagonal_radius, 1.0f), lod_bias);
            float4 sample_nn =
                tex2DLod<float4>((cudaTextureObject_t)d_tex_background_equirect,
                                 d_fract(u - diagonal_radius), fmaxf(v - diagonal_radius, 0.0f), lod_bias);
            sample.x = (4.0f * sample.x +
                        2.0f * (sample_pos_u.x + sample_neg_u.x + sample_pos_v.x + sample_neg_v.x) +
                        sample_pp.x + sample_pn.x + sample_np.x + sample_nn.x) * (1.0f / 16.0f);
            sample.y = (4.0f * sample.y +
                        2.0f * (sample_pos_u.y + sample_neg_u.y + sample_pos_v.y + sample_neg_v.y) +
                        sample_pp.y + sample_pn.y + sample_np.y + sample_nn.y) * (1.0f / 16.0f);
            sample.z = (4.0f * sample.z +
                        2.0f * (sample_pos_u.z + sample_neg_u.z + sample_pos_v.z + sample_neg_v.z) +
                        sample_pp.z + sample_pn.z + sample_np.z + sample_nn.z) * (1.0f / 16.0f);
        }

        accum = d_add(accum, d_scale(make_f3(sample.x, sample.y, sample.z), weight));
        total_weight += weight;
    }

    if (total_weight > 0.0f) {
        accum = d_scale(accum, 1.0f / total_weight);
    }
    if (weight_out != nullptr) {
        *weight_out = total_weight;
    }
    return accum;
}

/**
 * @brief Compute the background sky color for an escaped ray direction.
 *
 * WHY: When the galaxy cubemap texture object is registered (d_tex_galaxy != 0)
 *      we sample it via d_sample_galaxy_cubemap() to match the OpenGL path
 *      (texture(galaxy, dir).rgb in interop_trace.glsl).  When not registered,
 *      falls back to the procedural star field: d_hash() on a 300-unit
 *      directional grid (threshold ~2.2% density, x^8 sharpening via 3
 *      squarings) with temperature-varied colour (blue-white / yellow-white /
 *      orange) plus a dim ambient nebula glow scaled by d_background_intensity.
 *
 * Returns black if d_background_enabled is 0.
 *
 * @param dir Escaped ray direction (normalised in d_shade_hit).
 * @return RGBA float4 sky colour.
 */
__device__ __forceinline__ float4 d_background_color(float3 dir) {
    if (!d_background_enabled) {
        return make_float4(0.0f, 0.0f, 0.0f, 1.0f);
    }
    float3 n = d_normalize(dir);

    if (d_tex_background_equirect) {
        float layer_weight = 0.0f;
        float3 sky = d_sample_background_equirect_layered(n, &layer_weight);
        if (layer_weight <= 0.0f) {
            sky = d_sample_background_equirect(n);
        }
        sky = d_scale(sky, d_background_intensity);
        return make_float4(sky.x, sky.y, sky.z, 1.0f);
    }

    /* If galaxy cubemap is registered, sample it directly (matches GL path). */
    if (d_tex_galaxy) {
        float3 sky = d_sample_galaxy_cubemap(n);
        sky = d_scale(sky, d_background_intensity);
        return make_float4(sky.x, sky.y, sky.z, 1.0f);
    }

    /* Procedural star field: hash-based point stars */
    /* 300-unit grid gives finer point stars; threshold 0.978 -> ~2.2% density */
    float3 grid = make_f3(floorf(n.x * 300.0f), floorf(n.y * 300.0f),
                          floorf(n.z * 300.0f));
    float h = d_hash(grid);
    /* x^8 via 3 squarings: ~14 cy (3x FMUL at 4.54 cy) vs powf ~35 cy (LG2+EX2).
     * YSU-engine SASS RE: MUFU.EX2 = 17.55 cy, MUFU.LG2 similar. */
    float star;
    if (h > 0.978f) {
        float sx = (h - 0.978f) * (1.0f / 0.022f);
        float sx2 = sx * sx;
        float sx4 = sx2 * sx2;
        star = sx4 * sx4;
    } else {
        star = 0.0f;
    }

    /* Star color: slight temperature variation */
    float temp = d_hash(d_add(grid, make_f3(1.0f, 2.0f, 3.0f)));
    float3 star_col;
    if (temp > 0.7f) {
        star_col = make_f3(0.8f, 0.85f, 1.0f);  /* blue-white */
    } else if (temp > 0.3f) {
        star_col = make_f3(1.0f, 0.95f, 0.85f);  /* yellow-white */
    } else {
        star_col = make_f3(1.0f, 0.7f, 0.5f);    /* orange */
    }

    /* Ambient nebula glow: ensures escaped rays are distinguishable from the
     * horizon color (0,0,0,1). Physically motivated by CMB + zodiacal light. */
    float3 ambient = d_scale(make_f3(0.002f, 0.002f, 0.008f), d_background_intensity);
    float3 sky = d_add(d_scale(star_col, star * d_background_intensity), ambient);
    return make_float4(sky.x, sky.y, sky.z, 1.0f);
}

__device__ __forceinline__ float d_luminance(float3 color) {
    return 0.2126f * color.x + 0.7152f * color.y + 0.0722f * color.z;
}

__device__ __forceinline__ float3 d_apply_simple_redshift(float3 color, float z) {
    float one_plus_z = 1.0f + z;
    float dimming = 1.0f / fmaxf(one_plus_z * one_plus_z * one_plus_z, D_EPSILON);
    return d_scale(color, dimming);
}

__device__ __forceinline__ float d_smoothstep_range(float edge0, float edge1, float x) {
    float t = fmaxf(0.0f, fminf((x - edge0) / fmaxf(edge1 - edge0, D_EPSILON), 1.0f));
    return t * t * (3.0f - 2.0f * t);
}

__device__ __forceinline__ float3 d_shape_escaped_background(float3 sky,
                                                             float min_radius,
                                                             float3 closest_pos,
                                                             float3 cam_pos,
                                                             float rs,
                                                             float spin) {
    if (d_redshift_enabled && min_radius < rs * 10.0f) {
        float z;
        if (d_use_luts && d_tex_redshift) {
            float r_norm = min_radius / fmaxf(rs, D_EPSILON);
            float denom = fmaxf(d_redshift_radius_max - d_redshift_radius_min, 0.0001f);
            float u = fmaxf(0.0f, fminf((r_norm - d_redshift_radius_min) / denom, 1.0f));
            z = tex2D<float>((cudaTextureObject_t)d_tex_redshift, u, 0.5f);
        } else {
            z = 1.0f / fmaxf(d_redshift_factor(min_radius, rs), D_EPSILON) - 1.0f;
        }
        sky = d_apply_simple_redshift(sky, z);
    }

    if (min_radius < rs * 5.0f) {
        float3 closest_n = d_normalize(closest_pos);
        float3 approach_dir = d_normalize(d_sub(cam_pos, closest_pos));
        float spin_y = spin >= 0.0f ? 1.0f : -1.0f;
        float3 spin_axis = make_f3(0.0f, spin_y, 0.0f);
        float3 flow_dir = d_normalize(d_cross(spin_axis, closest_n));
        float aligned_flow = 0.5f + 0.5f * d_dot(flow_dir, approach_dir);
        float near_hole_weight =
            powf(fmaxf(0.0f, fminf(1.0f - (min_radius - rs) / fmaxf(rs * 3.0f, D_EPSILON), 1.0f)),
                 1.55f);

        float bright_sector = d_smoothstep_range(0.83f, 0.985f, aligned_flow);
        float rim_sector = d_smoothstep_range(0.91f, 0.995f, aligned_flow);
        float counter_sector = d_smoothstep_range(0.24f, 0.48f, aligned_flow);
        float adjacent_sector =
            d_smoothstep_range(0.74f, 0.95f, aligned_flow) * (1.0f - bright_sector);
        float broad_field_sector =
            d_smoothstep_range(0.46f, 0.84f, aligned_flow) * (1.0f - adjacent_sector) *
            (1.0f - bright_sector);
        float local_shadow =
            1.0f + (0.08f - 1.0f) * near_hole_weight * (1.0f - bright_sector * 0.95f);
        float local_lift =
            1.0f + near_hole_weight *
                       (0.40f * bright_sector + 0.06f * rim_sector + 0.0f * counter_sector);
        sky = d_scale(sky, local_shadow * local_lift);

        float sky_luma = d_luminance(sky);
        float sector_contrast =
            near_hole_weight * ((-0.50f) + (0.20f - (-0.50f)) * bright_sector);
        sky = d_add(sky, d_scale(sky, sector_contrast * fmaxf(fminf(sky_luma - 0.03f, 1.0f), 0.0f)));

        float3 cool_tint = make_f3(0.84f, 0.80f, 0.96f);
        float3 warm_tint = make_f3(1.06f, 0.98f, 0.88f);
        float3 arc_tint = make_f3(cool_tint.x + (warm_tint.x - cool_tint.x) * rim_sector,
                                  cool_tint.y + (warm_tint.y - cool_tint.y) * rim_sector,
                                  cool_tint.z + (warm_tint.z - cool_tint.z) * rim_sector);
        float tint_mix = near_hole_weight * (0.012f + 0.05f * rim_sector);
        float3 tinted = make_f3(sky.x * arc_tint.x, sky.y * arc_tint.y, sky.z * arc_tint.z);
        sky = make_f3(sky.x + (tinted.x - sky.x) * tint_mix,
                      sky.y + (tinted.y - sky.y) * tint_mix,
                      sky.z + (tinted.z - sky.z) * tint_mix);

        float exclusion = near_hole_weight * (1.0f - bright_sector) *
                          d_smoothstep_range(0.025f, 0.18f, sky_luma);
        sky = d_scale(sky, 1.0f - 0.28f * exclusion);

        float negative_space =
            near_hole_weight * (1.0f - bright_sector) * d_smoothstep_range(0.01f, 0.08f, sky_luma);
        sky = d_scale(sky, 1.0f - 0.24f * negative_space);

        float field_suppression =
            near_hole_weight * (1.0f - bright_sector) * d_smoothstep_range(0.018f, 0.12f, sky_luma);
        sky = d_scale(sky, 1.0f - 0.16f * field_suppression);

        float arc_adjacent_suppression =
            near_hole_weight * adjacent_sector * d_smoothstep_range(0.016f, 0.13f, sky_luma);
        sky = d_scale(sky, 1.0f - 0.21f * arc_adjacent_suppression);

        float broad_field_suppression =
            near_hole_weight * broad_field_sector * d_smoothstep_range(0.014f, 0.10f, sky_luma);
        sky = d_scale(sky, 1.0f - 0.15f * broad_field_suppression);
    }

    return sky;
}

/* ========================================================================
 * GRMHD volume sampling
 * ======================================================================== */

/**
 * @brief Sample the GRMHD 3D texture at a Cartesian world-space position.
 *
 * Converts the Cartesian position to Boyer-Lindquist (r, theta, phi) coordinates,
 * normalizes each axis to [0, 1] using the registered GRMHD grid bounds, and
 * samples the RGBA32F 3D texture object.
 *
 * The texture was registered with address modes:
 *   S = cudaAddressModeClamp  (r axis: finite radial extent)
 *   T = cudaAddressModeMirror (theta axis: equatorial symmetry)
 *   R = cudaAddressModeWrap   (phi axis: 2*pi periodic)
 *
 * Returns make_float4(0,0,0,0) if the GRMHD texture object is not registered
 * (d_tex_grmhd == 0) or if d_grmhd_r_max <= d_grmhd_r_min (degenerate bounds).
 *
 * @param pos World-space Cartesian position (x, y, z) in geometric units.
 * @return float4 with (rho, internal_energy, v1, v2), normalized to [0, 1]
 *         by nubhlight_pack convention.
 */
__device__ __forceinline__ float4 d_sample_grmhd(float3 pos) {
    if (d_tex_grmhd == 0ULL) {
        return make_float4(0.0f, 0.0f, 0.0f, 0.0f);
    }
    float const r_range = d_grmhd_r_max - d_grmhd_r_min;
    if (r_range <= D_EPSILON) {
        return make_float4(0.0f, 0.0f, 0.0f, 0.0f);
    }

    /* Cartesian -> spherical (BL coincides with spherical in the grid frame) */
    float const r = sqrtf(pos.x * pos.x + pos.y * pos.y + pos.z * pos.z);
    /* theta in [0, pi] -- guard against division by zero at origin */
    float const theta = (r > D_EPSILON) ? acosf(pos.z / r) : 0.0f;
    /* phi in [-pi, pi] -> shift to [0, 2*pi] for uniform wrap */
    float phi = atan2f(pos.y, pos.x);
    if (phi < 0.0f) phi += D_TWO_PI;

    /* Normalize to [0, 1]:
     *   u = (r - r_min) / (r_max - r_min)  [clamped by texture address mode]
     *   v = theta / pi                      [mirrored at 1.0 = pi]
     *   w = phi / (2*pi)                    [wrapped at 1.0 = 2*pi]        */
    float const u = (r - d_grmhd_r_min) / r_range;
    float const v = theta * D_INV_PI;
    float const w = phi * D_INV_TWO_PI;

    float4 const left = tex3D<float4>((cudaTextureObject_t)d_tex_grmhd, u, v, w);

    /* C1d: temporal interpolation between adjacent GRMHD simulation frames.
     * When right texture is absent (alpha==0 or slot unregistered), return
     * the left frame directly (lerp(L, ?, 0) = L, no right sample needed). */
    if (d_tex_grmhd_right == 0ULL || d_grmhd_alpha <= D_EPSILON) {
        return left;
    }
    float4 const right = tex3D<float4>((cudaTextureObject_t)d_tex_grmhd_right, u, v, w);
    float const a = d_grmhd_alpha;
    return make_float4(
        left.x + a * (right.x - left.x),
        left.y + a * (right.y - left.y),
        left.z + a * (right.z - left.z),
        left.w + a * (right.w - left.w));
}

/**
 * @brief Dispatch shading for a completed HitResult.
 *
 * Returns black for horizon hits, calls d_disk_color() for disk hits, and
 * calls d_background_color() for escaped rays with an added photon ring
 * proximity glow (cubic falloff from the photon sphere at 1.5*rs over 2.5*rs).
 *
 * @param hit     Completed HitResult from d_trace_geodesic().
 * @param cam_pos Camera position used to reconstruct the escaped ray direction.
 * @return Final RGBA float4 pixel color.
 */
__device__ __forceinline__ float4 d_shade_hit(const HitResult& hit, float3 cam_pos) {
    if (hit.hit_horizon) {
        return make_float4(0.0f, 0.0f, 0.0f, 1.0f);
    }
    if (hit.hit_disk) {
        float4 disk_col = d_disk_color(hit, cam_pos, d_rs);
        /* GRMHD emissivity modulation: j_nu ~ rho * B^2, B^2 ~ u (plasma beta ~ 1).
         * Matches blackhole_main.frag: density *= rho * uu at disk hit point. */
        if (d_use_luts && d_tex_grmhd) {
            float4 grmhd = d_sample_grmhd(hit.hit_point);
            float rho = fmaxf(grmhd.x, 0.0f);
            float uu  = fmaxf(grmhd.y, 0.0f);
            float grmhd_scale = rho * uu;
            disk_col.x *= grmhd_scale;
            disk_col.y *= grmhd_scale;
            disk_col.z *= grmhd_scale;
        }
        return disk_col;
    }
    float3 dir = d_normalize(d_sub(hit.hit_point, cam_pos));
    float4 bg = d_background_color(dir);
    float3 shaped_bg = d_shape_escaped_background(make_f3(bg.x, bg.y, bg.z),
                                                  hit.min_radius,
                                                  hit.closest_approach_point,
                                                  cam_pos, d_rs, d_spin);
    bg = make_float4(shaped_bg.x, shaped_bg.y, shaped_bg.z, bg.w);

    /* Photon ring proximity glow: match the GLSL lane's narrower, more
     * anisotropic ring instead of a broad uniform halo. */
    float r_ph = D_PHOTON_SPHERE * d_rs;
    float photon_dist = fabsf(hit.min_radius - r_ph);
    float x = fmaxf(0.0f, 1.0f - photon_dist / fmaxf(0.5f * d_rs, D_EPSILON));
    float glow = x * x * x;
    float glow_scale = fmaxf(d_photon_glow_strength, 0.0f);
    if (glow > 0.0f) {
        float3 closest_n = d_normalize(hit.closest_approach_point);
        float3 approach_dir = d_normalize(d_sub(cam_pos, hit.closest_approach_point));
        float spin_y = d_spin >= 0.0f ? 1.0f : -1.0f;
        float3 spin_axis = make_f3(0.0f, spin_y, 0.0f);
        float3 flow_dir = d_normalize(d_cross(spin_axis, closest_n));
        float aligned_flow = 0.5f + 0.5f * d_dot(flow_dir, approach_dir);
        float spin_t = fmaxf(0.0f, fminf((fabsf(d_spin) - 0.05f) / fmaxf(0.85f - 0.05f, D_EPSILON), 1.0f));
        float spin_weight = spin_t * spin_t * (3.0f - 2.0f * spin_t);
        float anisotropic_ring =
            1.0f + ((0.72f + (1.65f - 0.72f) * aligned_flow) - 1.0f) * spin_weight;
        float glow_intensity = powf(glow * 0.22f * glow_scale, 1.08f) * anisotropic_ring;
        float rim_mix = d_smoothstep_range(0.09f * d_rs, 0.0f, photon_dist);
        float3 glow_color = make_f3(1.06f, 0.86f, 0.58f);
        float3 rim_color = make_f3(1.22f, 1.0f, 0.78f);
        float3 ring_color = d_lerp(glow_color, rim_color, rim_mix);
        bg.x = fminf(bg.x + ring_color.x * glow_intensity, 100.0f);
        bg.y = fminf(bg.y + ring_color.y * glow_intensity, 100.0f);
        bg.z = fminf(bg.z + ring_color.z * glow_intensity, 100.0f);
    }

    return bg;
}

/* ========================================================================
 * Ray generation from pixel coordinates
 * ======================================================================== */

/**
 * @brief Generate a world-space ray direction for pixel (px, py).
 *
 * Matches GLSL interop_raygen.glsl::bhRayDirFromUv() exactly:
 *   GLSL: dir = normalize(vec3(-uv.x * fovScale, uv.y * fovScale, 1.0))
 *              then cameraBasis * dir
 *   Convention: basis col2 = forward (toward BH), z=+1 = forward direction.
 *   x is negated to match GLSL image-space orientation (left=+right, right=-right).
 *   v is negated because CUDA py=0 is image-top (like D3D) while GLSL uv.y is
 *   positive at the image-top (gl_FragCoord.y=0 is bottom, so uv.y=top is +0.5).
 *
 * WHY the previous -1.0f was wrong: with z=-1 and basis[2]=forward, the center
 * ray would map to -forward (looking BACKWARD from the camera), causing the
 * entire render to show the scene behind the camera.
 *
 * @param px Pixel column index (0-based).
 * @param py Pixel row index (0-based).
 * @return Normalized world-space ray direction.
 */
__device__ __forceinline__ float3 d_ray_dir(int px, int py) {
    float u = (2.0f * (px + 0.5f) / (float)d_width - 1.0f) * d_fov_scale;
    float v = (2.0f * (py + 0.5f) / (float)d_height - 1.0f) * d_fov_scale;
    /* Correct for aspect ratio (matches GLSL uv.x *= resolution.x/resolution.y) */
    u *= (float)d_width / (float)d_height;
    u += d_frame_shift_x;
    v += d_frame_shift_y;

    /* -u: matches GLSL -uv.x (horizontal mirror to right-hand camera convention).
     * -v: py=0 is image-top in CUDA; gl_FragCoord.y=0 is image-bottom in GLSL,
     *     so GLSL uv.y is positive-at-top, CUDA v is negative-at-top.
     * +1: basis col2 = forward, so local +z maps to world forward (toward BH). */
    float3 local_dir = d_normalize(make_f3(-u, -v, 1.0f));
    return d_mat3_mul(d_cam_basis, local_dir);
}

/* ========================================================================
 * Volumetric Radiative Transfer Equation (D3)
 * Mirrors rteStepVec3() and bhTraceGeodesicRTE() from shader/include/.
 * ======================================================================== */

/**
 * @brief One front-to-back RTE segment: updates transmittance, returns contribution.
 *
 * Analytic formal solution over uniform segment of length step_size:
 *   I_new = I_old * exp(-tau) + S * (1 - exp(-tau)),  tau = alpha_nu * step_size
 * Taylor fallback for tau < 1e-5 to avoid (1-exp(-tau)) cancellation.
 *
 * @param emit_color RGB emission color (temperature-mapped, pre-Doppler).
 * @param j_eff      Effective emission coefficient (includes Doppler g^3, density).
 * @param alpha_nu   Absorption coefficient [1/step-unit].
 * @param step_size  Segment path length [same units as alpha_nu denominator].
 * @param transmit   [in/out] Current path transmittance; decremented by exp(-tau).
 * @return Segment contribution to add to accumI (= transmit_before * S * (1-exp(-tau))).
 */
__device__ __forceinline__ float3 d_rte_step(float3 emit_color, float j_eff,
                                              float alpha_nu, float step_size,
                                              float &transmit) {
    float const tau = fmaxf(alpha_nu * step_size, 0.0f);

    float one_m_exp_tau;
    float exp_tau;
    if (tau < 1.0e-5f) {
        /* Taylor: avoid (1 - exp(-tau)) cancellation for small tau */
        one_m_exp_tau = tau * (1.0f - 0.5f * tau);
        exp_tau       = 1.0f - tau;
    } else {
        exp_tau       = expf(-tau);
        one_m_exp_tau = 1.0f - exp_tau;
    }

    float3 seg_emit;
    if (alpha_nu < 1.0e-30f) {
        /* No absorption: pure emission, I += j * ds */
        seg_emit = d_scale(emit_color, j_eff * step_size);
    } else {
        seg_emit = d_scale(emit_color, (j_eff / alpha_nu) * one_m_exp_tau);
    }

    float3 const contribution = d_scale(seg_emit, transmit);
    transmit *= fmaxf(exp_tau, 0.0f);
    return contribution;
}

/**
 * @brief Trace a Kerr geodesic with front-to-back volumetric RTE compositing.
 *
 * Mirrors bhTraceGeodesicRTE() in shader/include/interop_trace.glsl.
 * For Schwarzschild (d_kerr_enabled=0 or |a| < D_EPSILON), falls back to
 * d_trace_geodesic() + d_shade_hit() (single-scatter, bit-exact parity).
 *
 * Disk emission model at each step inside [r_disk_in, r_disk_out]:
 *   - Novikov-Thorne flux: F ~ (r_in/r)^3 * (1 - sqrt(r_in/r))
 *   - Temperature color: 3-band ramp (matches GLSL bhTraceGeodesicRTE)
 *   - Doppler beaming: g = 1 + 0.3 * sqrt(rs/2r) * cos(phi),  intensity *= g^3
 *   - Gaussian vertical density: rho ~ exp(-z^2 / 2*h_disk^2),  h_disk = 0.1*rs
 *
 * Background is added at escape weighted by surviving transmittance.
 * Early exit when transmit < 0.005 (medium is effectively opaque).
 *
 * @param cam_pos Camera position in world (Cartesian) coordinates.
 * @param ray_dir Normalized ray direction in world coordinates.
 * @return Composited RGBA float4 pixel color.
 */
__device__ __forceinline__ float4 d_trace_geodesic_rte(float3 cam_pos, float3 ray_dir,
                                                       float3 *terminal_pos) {
    float const rs = d_rs;
    float const a  = 0.5f * d_spin * rs;

    if (!d_kerr_enabled || fabsf(a) < D_EPSILON) {
        /* Schwarzschild fallback: single-scatter (same as baseline kernel) */
        HitResult const hit = d_trace_geodesic(cam_pos, ray_dir);
        if (terminal_pos != nullptr) { *terminal_pos = hit.hit_point; }
        return d_shade_hit(hit, cam_pos);
    }

    float r_horizon = d_kerr_outer_horizon(rs, a);
    if (r_horizon <= D_EPSILON) { r_horizon = rs; }

    float const r_disk_in   = d_isco;
    float const r_disk_out  = 100.0f * rs;
    float const h_disk      = fmaxf(0.1f * rs, D_EPSILON);
    float const dt          = d_step_size;
    float const max_dist    = d_max_dist;
    int   const max_steps   = d_max_steps;
    float const opacity_scl = d_rte_opacity_scale;

    KerrConsts const c  = d_kerr_init_consts(cam_pos, ray_dir, rs, a);
    KerrRay          kr = d_kerr_init_ray(cam_pos, ray_dir);

    float3 accum_i  = make_f3(0.0f, 0.0f, 0.0f);
    float  transmit = 1.0f;
    float  min_r    = kr.r;
    float3 closest_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

    for (int step = 0; step < max_steps; ++step) {
        float3 const cur_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
        if (kr.r < min_r) {
            min_r = kr.r;
            closest_pos = cur_pos;
        }

        if (kr.r <= r_horizon) {
            /* Horizon absorbs everything: return accumulated emission */
            if (terminal_pos != nullptr) { *terminal_pos = cur_pos; }
            return make_float4(accum_i.x, accum_i.y, accum_i.z, 1.0f);
        }

        /* D10: AMR step refinement near horizon and photon sphere */
        float const step_dt_rte = d_adaptive_step(kr.r, rs, r_horizon, dt);
        d_kerr_step(kr, rs, a, c, step_dt_rte);
        float3 const new_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

        if (d_adisk_enabled) {
            float const r_cyl = sqrtf(fmaf(new_pos.x, new_pos.x, new_pos.y * new_pos.y));
            if (r_cyl >= r_disk_in && r_cyl <= r_disk_out) {
                /* Novikov-Thorne flux profile */
                float const x    = r_disk_in / fmaxf(r_cyl, D_EPSILON);
                float const flux = fmaxf(0.0f, x * x * x * (1.0f - sqrtf(x)));

                /* Temperature-to-color: 3-band ramp (matches bhTraceGeodesicRTE GLSL) */
                float const t_norm = sqrtf(sqrtf(fmaxf(flux, 0.0f)));
                float3 emit_color;
                if (t_norm > 0.6f) {
                    emit_color = make_f3(1.0f, 0.9f, 0.8f);
                } else if (t_norm > 0.3f) {
                    emit_color = make_f3(1.0f, 0.6f, 0.2f);
                } else {
                    emit_color = make_f3(0.8f, 0.2f, 0.1f);
                }

                /* Keplerian Doppler beaming: v ~ sqrt(rs / 2r), boost ~ (1 + 0.3*v*cos phi)^3 */
                float const v       = sqrtf(0.5f * rs / fmaxf(r_cyl, D_EPSILON));
                float const phi_ang = atan2f(new_pos.y, new_pos.x);
                float const doppler = 1.0f + 0.3f * v * cosf(phi_ang);
                float const g3      = doppler * doppler * doppler;

                /* Gaussian vertical density falloff: rho ~ exp(-z^2 / 2 h^2) */
                float const z_over_h  = new_pos.z / h_disk;
                float const rho_norm  = expf(-0.5f * z_over_h * z_over_h);

                float const j_eff   = flux * g3 * rho_norm;
                float const alpha_nu = opacity_scl * fmaxf(j_eff, 0.0f);

                float3 const contrib = d_rte_step(emit_color, j_eff, alpha_nu, step_dt_rte, transmit);
                accum_i = d_add(accum_i, contrib);

                if (transmit < 0.005f) {
                    if (terminal_pos != nullptr) { *terminal_pos = new_pos; }
                    return make_float4(accum_i.x, accum_i.y, accum_i.z, 1.0f);
                }
            }
        }

        if (kr.r > max_dist) {
            float3 const esc_dir = d_sub(new_pos, cur_pos);
            if (terminal_pos != nullptr) { *terminal_pos = new_pos; }
            if (d_dot(esc_dir, esc_dir) > D_EPSILON * D_EPSILON) {
                float4 const bg4 = d_background_color(d_normalize(esc_dir));
                float3 bg = make_f3(bg4.x, bg4.y, bg4.z);
                bg = d_shape_escaped_background(bg, min_r, closest_pos, cam_pos, rs, d_spin);
                accum_i.x += transmit * bg.x;
                accum_i.y += transmit * bg.y;
                accum_i.z += transmit * bg.z;
            }
            return make_float4(accum_i.x, accum_i.y, accum_i.z, 1.0f);
        }
    }

    /* Step budget exhausted -- treat as escaped along last known direction */
    float3 const final_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
    if (terminal_pos != nullptr) { *terminal_pos = final_pos; }
    float3 const esc_dir   = d_sub(final_pos, cam_pos);
    if (d_dot(esc_dir, esc_dir) > D_EPSILON * D_EPSILON) {
        float4 const bg4 = d_background_color(d_normalize(esc_dir));
        float3 bg = make_f3(bg4.x, bg4.y, bg4.z);
        bg = d_shape_escaped_background(bg, min_r, closest_pos, cam_pos, rs, d_spin);
        accum_i.x += transmit * bg.x;
        accum_i.y += transmit * bg.y;
        accum_i.z += transmit * bg.z;
    }
    return make_float4(accum_i.x, accum_i.y, accum_i.z, 1.0f);
}

/* ========================================================================
 * Stokes polarized radiative transfer (D4)
 * ======================================================================== */

/**
 * @brief Packed Stokes vector (I, Q, U, V) for CUDA device code.
 *
 * WHY: float4 would work but the component names (xyzw) are non-mnemonic.
 *      A named struct eliminates index errors in the step function logic.
 */
struct DStokes {
    float i;  /**< @brief Total intensity. */
    float q;  /**< @brief Linear polarization: 0/90-deg axis. */
    float u;  /**< @brief Linear polarization: 45/135-deg axis. */
    float v;  /**< @brief Circular polarization (V>0: right-circular). */
};

/**
 * @brief Exact analytic Stokes step for simplified K matrix (alpha_I + rho_V).
 *
 * Mirrors stokesStep() in src/physics/stokes_transport.h, ported to float
 * arithmetic for the CUDA device.
 *
 * Simplified K: total absorption alpha_I for all channels, plus Faraday
 * rotation rho_V coupling Q <-> U.  I and V evolve as independent scalar RTE
 * channels; (Q,U) evolve under simultaneous absorption and rotation.
 *
 * EXACT SOLUTION for (Q,U):
 *   D = A^2 + R^2   (A = alphaI, R = rhoV)
 *   Ic = [A*(1-E*C) + R*E*S] / D
 *   Is = [R*(1-E*C) - A*E*S] / D
 *   Q_new = Q_hom + jQ*Ic - jU*Is
 *   U_new = U_hom + jQ*Is + jU*Ic
 *
 * @param s       Current Stokes state.
 * @param jI,jQ,jU,jV  Emission coefficients.
 * @param alphaI  Total absorption coefficient [1/path-unit].
 * @param rhoV    Faraday rotation rate [rad/path-unit].
 * @param ds      Segment length [path-units].
 * @return Updated Stokes state.
 */
__device__ __forceinline__ DStokes d_stokes_step(DStokes s,
                                                  float jI, float jQ,
                                                  float jU, float jV,
                                                  float alphaI, float rhoV,
                                                  float ds) {
    if (ds <= 0.0f) { return s; }

    float const A    = fmaxf(alphaI, 0.0f);
    float const R    = rhoV;
    float const tauL = A * ds;
    float const E    = (tauL < 700.0f) ? expf(-tauL) : 0.0f;
    float const phi  = R * ds;
    float const Cp   = cosf(phi);
    float const Sp   = sinf(phi);

    /* I channel: standard scalar RTE */
    float iNew;
    if (A < 1.0e-30f) {
        iNew = s.i + jI * ds;
    } else if (tauL < 1.0e-4f) {
        iNew = s.i * (1.0f - tauL) + jI * ds;
    } else {
        iNew = fmaf(s.i, E, (jI / A) * (1.0f - E));
    }

    /* V channel: scalar RTE (decoupled in simplified K) */
    float vNew;
    if (A < 1.0e-30f) {
        vNew = s.v + jV * ds;
    } else if (tauL < 1.0e-4f) {
        vNew = s.v * (1.0f - tauL) + jV * ds;
    } else {
        vNew = fmaf(s.v, E, (jV / A) * (1.0f - E));
    }

    /* (Q,U) homogeneous: decay + rotation */
    float const qHom = E * fmaf(s.q, Cp, -s.u * Sp);
    float const uHom = E * fmaf(s.q, Sp,  s.u * Cp);

    float qNew, uNew;
    float const D = fmaf(A, A, R * R);

    if (D < 1.0e-60f) {
        /* Pure emission (neither absorption nor rotation) */
        qNew = s.q + jQ * ds;
        uNew = s.u + jU * ds;
    } else if (A < 1.0e-15f * fabsf(R)) {
        /* Rotation-dominated (A ~ 0) */
        float const ic  =  Sp / R;
        float const is_ = (1.0f - Cp) / R;
        qNew = fmaf(jQ, ic,  fmaf(-jU, is_, qHom));
        uNew = fmaf(jQ, is_, fmaf( jU, ic,  uHom));
    } else if (fabsf(R) < 1.0e-15f * A) {
        /* Absorption-dominated (R ~ 0) */
        float const oneME = (tauL < 1.0e-4f) ? fmaf(-0.5f * tauL, ds, ds) : (1.0f - E) / A;
        qNew = fmaf(jQ, oneME, qHom);
        uNew = fmaf(jU, oneME, uHom);
    } else {
        float const ec  = E * Cp;
        float const es  = E * Sp;
        float const oneMec = 1.0f - ec;
        float const ic  = fmaf(A, oneMec, R * es) / D;
        float const is_ = fmaf(R, oneMec, -(A * es)) / D;
        qNew = fmaf(jQ, ic,  fmaf(-jU, is_, qHom));
        uNew = fmaf(jQ, is_, fmaf( jU, ic,  uHom));
    }

    return {iNew, qNew, uNew, vNew};
}

/**
 * @brief Trace a Kerr geodesic with polarized Stokes I,Q,U,V transport.
 *
 * Extends d_trace_geodesic_rte() to track Stokes polarization state alongside
 * the color-accurate intensity accumulator.  The I channel uses the same
 * front-to-back compositing as d_trace_geodesic_rte() for color consistency.
 * Q, U, V evolve under d_stokes_step() (simplified K: alpha_I + rho_V).
 *
 * At exit, the Stokes state is mapped to a display color by tinting the
 * accumulated RGB intensity with EVPA-derived hue and linear polarization
 * fraction.
 *
 * Polarization model:
 *   PI_LIN = 0.75 (thermal synchrotron, Theta_e >> 1, Mahadevan 1996).
 *   B-field EVPA: d_stokes_b_angle [rad] (uniform field, tuned via ImGui).
 *   Faraday: rhoV = d_stokes_ne_scale * rhoNorm (density-modulated).
 *
 * @param cam_pos Camera position in world (Cartesian) coordinates.
 * @param ray_dir Normalized ray direction.
 * @return Display-ready RGBA float4 pixel.
 */
__device__ __forceinline__ float4 d_trace_geodesic_stokes(float3 cam_pos,
                                                          float3 ray_dir,
                                                          float3 *terminal_pos) {
    float const rs = d_rs;
    float const a  = 0.5f * d_spin * rs;

    if (!d_kerr_enabled || fabsf(a) < D_EPSILON) {
        HitResult const hit = d_trace_geodesic(cam_pos, ray_dir);
        if (terminal_pos != nullptr) { *terminal_pos = hit.hit_point; }
        return d_shade_hit(hit, cam_pos);
    }

    float r_horizon = d_kerr_outer_horizon(rs, a);
    if (r_horizon <= D_EPSILON) { r_horizon = rs; }

    float const r_disk_in   = d_isco;
    float const r_disk_out  = 100.0f * rs;
    float const h_disk      = fmaxf(0.1f * rs, D_EPSILON);
    float const dt          = d_step_size;
    float const max_dist    = d_max_dist;
    int   const max_steps   = d_max_steps;
    float const opacity_scl = d_rte_opacity_scale;

    /* Intrinsic thermal synchrotron linear polarization fraction ~0.75 */
    float const pi_lin = 0.75f;
    float const b_angle = d_stokes_b_angle;
    float const ne_scale = d_stokes_ne_scale;

    KerrConsts const c  = d_kerr_init_consts(cam_pos, ray_dir, rs, a);
    KerrRay          kr = d_kerr_init_ray(cam_pos, ray_dir);

    /* Color-accurate intensity accumulator (same as d_trace_geodesic_rte) */
    float3 accum_i  = make_f3(0.0f, 0.0f, 0.0f);
    float  transmit = 1.0f;
    float  min_r    = kr.r;
    float3 closest_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

    /* Stokes Q, U, V accumulators (I uses accum_i above) */
    DStokes stokes = {0.0f, 0.0f, 0.0f, 0.0f};

    for (int step = 0; step < max_steps; ++step) {
        float3 const cur_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
        if (kr.r < min_r) {
            min_r = kr.r;
            closest_pos = cur_pos;
        }

        if (kr.r <= r_horizon) {
            if (terminal_pos != nullptr) { *terminal_pos = cur_pos; }
            return make_float4(accum_i.x, accum_i.y, accum_i.z, 1.0f);
        }

        float const step_dt = d_adaptive_step(kr.r, rs, r_horizon, dt);
        d_kerr_step(kr, rs, a, c, step_dt);
        float3 const new_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

        if (d_adisk_enabled) {
            float const r_cyl = sqrtf(fmaf(new_pos.x, new_pos.x, new_pos.y * new_pos.y));
            if (r_cyl >= r_disk_in && r_cyl <= r_disk_out) {
                float const x    = r_disk_in / fmaxf(r_cyl, D_EPSILON);
                float const flux = fmaxf(0.0f, x * x * x * (1.0f - sqrtf(x)));

                float const t_norm = sqrtf(sqrtf(fmaxf(flux, 0.0f)));
                float3 emit_color;
                if (t_norm > 0.6f) {
                    emit_color = make_f3(1.0f, 0.9f, 0.8f);
                } else if (t_norm > 0.3f) {
                    emit_color = make_f3(1.0f, 0.6f, 0.2f);
                } else {
                    emit_color = make_f3(0.8f, 0.2f, 0.1f);
                }

                float const v       = sqrtf(0.5f * rs / fmaxf(r_cyl, D_EPSILON));
                float const phi_ang = atan2f(new_pos.y, new_pos.x);
                float const doppler = 1.0f + 0.3f * v * cosf(phi_ang);
                float const g3      = doppler * doppler * doppler;

                float const z_over_h  = new_pos.z / h_disk;
                float const rho_norm  = expf(-0.5f * z_over_h * z_over_h);

                float const j_eff    = flux * g3 * rho_norm;
                float const alpha_nu = opacity_scl * fmaxf(j_eff, 0.0f);

                /* Intensity path: same as d_rte_step() */
                float3 const contrib = d_rte_step(emit_color, j_eff, alpha_nu,
                                                   step_dt, transmit);
                accum_i = d_add(accum_i, contrib);

                /* Polarized emission: j_Q, j_U from B-field EVPA */
                float const cos2b = cosf(2.0f * b_angle);
                float const sin2b = sinf(2.0f * b_angle);
                float const jI_s  = j_eff * (emit_color.x + emit_color.y + emit_color.z)
                                    * 0.33333333f;
                float const jQ_s  = -jI_s * pi_lin * cos2b;
                float const jU_s  = -jI_s * pi_lin * sin2b;

                /* Faraday rotation: rhoV = ne_scale * rho_norm */
                float const rho_v = ne_scale * rho_norm;

                /* Stokes step for Q, U, V (I is handled by accum_i above) */
                stokes = d_stokes_step(stokes, 0.0f, jQ_s, jU_s, 0.0f,
                                       alpha_nu, rho_v, step_dt);

                if (transmit < 0.005f) { break; }
            }
        }

        if (kr.r > max_dist) {
            float3 const esc_dir = d_sub(new_pos, cur_pos);
            if (terminal_pos != nullptr) { *terminal_pos = new_pos; }
            if (d_dot(esc_dir, esc_dir) > D_EPSILON * D_EPSILON) {
                float4 const bg4 = d_background_color(d_normalize(esc_dir));
                float3 bg = make_f3(bg4.x, bg4.y, bg4.z);
                bg = d_shape_escaped_background(bg, min_r, closest_pos, cam_pos, rs, d_spin);
                accum_i.x += transmit * bg.x;
                accum_i.y += transmit * bg.y;
                accum_i.z += transmit * bg.z;
            }
            break;
        }
    }

    /* Map Stokes state to display color: tint intensity by EVPA and P_lin */
    if (terminal_pos != nullptr) {
        *terminal_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
    }
    float const I_lum = (accum_i.x + accum_i.y + accum_i.z) * 0.33333333f;
    float const P_lin = (I_lum > 1.0e-10f)
        ? sqrtf(fmaf(stokes.q, stokes.q, stokes.u * stokes.u)) / I_lum
        : 0.0f;
    float const p_clamped = fminf(P_lin, 1.0f);
    float const chi       = 0.5f * atan2f(stokes.u, stokes.q);
    float const v_frac    = (I_lum > 1.0e-10f)
        ? fmaxf(-0.5f, fminf(0.5f, stokes.v / I_lum)) : 0.0f;

    float const tint_r = 1.0f + p_clamped * 0.4f * cosf(2.0f * chi);
    float const tint_g = 1.0f + p_clamped * 0.4f * sinf(2.0f * chi);
    float const tint_b = 1.0f + v_frac * 0.2f;

    return make_float4(fmaxf(accum_i.x * tint_r, 0.0f),
                       fmaxf(accum_i.y * tint_g, 0.0f),
                       fmaxf(accum_i.z * tint_b, 0.0f),
                       1.0f);
}

#endif /* BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH */
