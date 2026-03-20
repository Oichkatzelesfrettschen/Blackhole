/*
 * device_physics.cuh
 * CUDA __device__ implementations of Kerr metric geodesic tracing and shading.
 *
 * Ported from shader/include/kerr.glsl and shader/include/interop_trace.glsl.
 *
 * FIREWALL: This file includes ONLY <cuda_runtime.h>, <math.h>, <float.h>.
 * NO standard library headers beyond C99. NO headers from src/physics/.
 */

#ifndef BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH
#define BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH

#include <cuda_runtime.h>
#include <math.h>

/* ========================================================================
 * Constants (mirrors physics_constants.glsl)
 * ======================================================================== */

#define D_PI            3.14159265358979323846f
#define D_TWO_PI        6.28318530717958647692f
#define D_HALF_PI       1.57079632679489661923f
#define D_INV_PI        0.31830988618379067154f
#define D_EPSILON       1.0e-6f
#define D_PHOTON_SPHERE 1.5f
#define D_ISCO_RATIO    3.0f

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
 * Zero means the LUT is not registered; device code checks before sampling. */
extern __constant__ unsigned long long d_tex_emissivity;
extern __constant__ unsigned long long d_tex_redshift;
extern __constant__ unsigned long long d_tex_spectral;
extern __constant__ float d_doppler_strength;
extern __constant__ float d_background_intensity;
extern __constant__ int   d_background_enabled;

/* ========================================================================
 * Vector helpers (replacing GLSL vec3 operations)
 * ======================================================================== */

__device__ __forceinline__ float3 make_f3(float x, float y, float z) {
    return make_float3(x, y, z);
}

__device__ __forceinline__ float d_dot(float3 a, float3 b) {
    return fmaf(a.x, b.x, fmaf(a.y, b.y, a.z * b.z));
}

__device__ __forceinline__ float d_length(float3 v) {
    return sqrtf(d_dot(v, v));
}

__device__ __forceinline__ float3 d_normalize(float3 v) {
    float inv = rsqrtf(fmaxf(d_dot(v, v), 1.0e-12f));
    return make_f3(v.x * inv, v.y * inv, v.z * inv);
}

__device__ __forceinline__ float3 d_cross(float3 a, float3 b) {
    return make_f3(
        fmaf(a.y, b.z, -a.z * b.y),
        fmaf(a.z, b.x, -a.x * b.z),
        fmaf(a.x, b.y, -a.y * b.x)
    );
}

__device__ __forceinline__ float3 d_scale(float3 v, float s) {
    return make_f3(v.x * s, v.y * s, v.z * s);
}

__device__ __forceinline__ float3 d_add(float3 a, float3 b) {
    return make_f3(a.x + b.x, a.y + b.y, a.z + b.z);
}

__device__ __forceinline__ float3 d_sub(float3 a, float3 b) {
    return make_f3(a.x - b.x, a.y - b.y, a.z - b.z);
}

__device__ __forceinline__ float3 d_lerp(float3 a, float3 b, float t) {
    return make_f3(
        fmaf(t, b.x - a.x, a.x),
        fmaf(t, b.y - a.y, a.y),
        fmaf(t, b.z - a.z, a.z)
    );
}

/* mat3 * vec3 (column-major, matching glm layout) */
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

struct KerrConsts {
    float E;
    float Lz;
    float Q;
};

struct KerrRay {
    float r;
    float theta;
    float phi;
    float t;
    float sign_r;
    float sign_theta;
};

__device__ __forceinline__ float d_kerr_sigma(float r, float a, float cos_theta) {
    return fmaf(r, r, a * a * cos_theta * cos_theta);
}

__device__ __forceinline__ float d_kerr_delta(float r, float a, float rs) {
    return fmaf(r, r, -rs * r + a * a);
}

__device__ __forceinline__ float d_kerr_outer_horizon(float rs, float a) {
    float M = 0.5f * rs;
    float disc = fmaf(M, M, -(a * a));
    if (disc < 0.0f) return rs;
    return M + sqrtf(disc);
}

__device__ __forceinline__ float3 d_kerr_to_cartesian(float r, float theta, float phi) {
    float sin_t, cos_t, sin_p, cos_p;
    sincosf(theta, &sin_t, &cos_t);
    sincosf(phi, &sin_p, &cos_p);
    return make_f3(r * sin_t * cos_p, r * sin_t * sin_p, r * cos_t);
}

__device__ __forceinline__ KerrConsts d_kerr_init_consts(float3 pos, float3 dir) {
    KerrConsts c;
    c.E = 1.0f;
    float3 L = d_cross(pos, dir);
    c.Lz = L.z;
    float L2 = d_dot(L, L);
    c.Q = fmaxf(0.0f, L2 - c.Lz * c.Lz);
    return c;
}

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

__device__ __forceinline__ void d_kerr_step(KerrRay& ray, float rs, float a, const KerrConsts& c, float dlam) {
    float r = ray.r;
    float theta = ray.theta;
    float sin_t, cos_t;
    sincosf(theta, &sin_t, &cos_t);
    float sin2 = fmaxf(sin_t * sin_t, 1.0e-6f);

    float Delta = d_kerr_delta(r, a, rs);
    float A = fmaf(r * r + a * a, c.E, -a * c.Lz);
    float Lz_minus_aE = c.Lz - a * c.E;

    float R = fmaf(A, A, -Delta * (c.Q + Lz_minus_aE * Lz_minus_aE));
    float Theta = c.Q + a * a * c.E * c.E * cos_t * cos_t - c.Lz * c.Lz / sin2;

    if (R < 0.0f) ray.sign_r *= -1.0f;
    if (Theta < 0.0f) ray.sign_theta *= -1.0f;

    float sqrt_R = sqrtf(fmaxf(R, 0.0f));
    float sqrt_Theta = sqrtf(fmaxf(Theta, 0.0f));
    float delta_safe = fmaxf(Delta, 1.0e-6f);

    float dr_dlam = ray.sign_r * sqrt_R;
    float dtheta_dlam = ray.sign_theta * sqrt_Theta;
    float dphi_dlam = c.Lz / sin2 - a * c.E + a * A / delta_safe;
    float dt_dlam = (r * r + a * a) * A / delta_safe + a * (c.Lz - a * c.E * sin2);

    ray.r += dlam * dr_dlam;
    ray.theta += dlam * dtheta_dlam;
    ray.phi += dlam * dphi_dlam;
    ray.t += dlam * dt_dlam;

    ray.theta = fminf(fmaxf(ray.theta, 1.0e-6f), D_PI - 1.0e-6f);
}

/* ========================================================================
 * Schwarzschild geodesic (from interop_trace.glsl)
 * ======================================================================== */

__device__ __forceinline__ float3 d_schwarzschild_accel(float3 pos, float3 vel, float rs) {
    float r = d_length(pos);
    if (r < D_EPSILON) return make_f3(0.0f, 0.0f, 0.0f);

    float3 h = d_cross(pos, vel);
    float h2 = d_dot(h, h);
    float r5 = r * r * r * r * r;
    float coeff = -1.5f * rs * h2 / r5;
    return d_scale(pos, coeff);
}

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

__device__ __forceinline__ bool d_check_disk(float3 old_pos, float3 new_pos,
                             float r_in, float r_out, float3& hit) {
    if (old_pos.z * new_pos.z > 0.0f) return false;
    float t = -old_pos.z / (new_pos.z - old_pos.z);
    hit = d_lerp(old_pos, new_pos, t);
    float r = sqrtf(fmaf(hit.x, hit.x, hit.y * hit.y));
    return r >= r_in && r <= r_out;
}

__device__ __forceinline__ float d_redshift_factor(float r, float rs) {
    if (r <= rs) return 0.0f;
    float f = 1.0f - rs / r;
    if (f <= 0.0f) return 0.0f;
    return sqrtf(f);
}

/* ========================================================================
 * Hit result
 * ======================================================================== */

struct HitResult {
    bool hit_disk;
    bool hit_horizon;
    bool escaped;
    float3 hit_point;
    float phi;
    float redshift;
    float min_radius;
};

/* ========================================================================
 * Full geodesic trace (from bhTraceGeodesic)
 * ======================================================================== */

__device__ __forceinline__ HitResult d_trace_geodesic(float3 cam_pos, float3 ray_dir) {
    HitResult result;
    result.hit_disk = false;
    result.hit_horizon = false;
    result.escaped = false;
    result.hit_point = make_f3(0.0f, 0.0f, 0.0f);
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
        float r_disk_out = 100.0f * rs;

        KerrConsts c = d_kerr_init_consts(cam_pos, ray_dir);
        KerrRay kr = d_kerr_init_ray(cam_pos, ray_dir);

        for (int step = 0; step < max_steps; ++step) {
            float3 old_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
            result.min_radius = fminf(result.min_radius, kr.r);

            if (kr.r <= r_horizon) {
                result.hit_horizon = true;
                result.hit_point = old_pos;
                return result;
            }

            d_kerr_step(kr, rs, a, c, dt);
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
        float r_disk_out = 100.0f * rs;

        for (int step = 0; step < max_steps; ++step) {
            float3 old_pos = pos;
            d_step_rk4(pos, vel, rs, dt);

            float r = d_length(pos);
            result.min_radius = fminf(result.min_radius, r);

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
 * Shading (from interop_trace.glsl: bhDiskColorFromHit, bhShadeHit)
 * ======================================================================== */

/* Disk color: Novikov-Thorne flux with optional LUT sampling.
 * Matches bhDiskColorFromHit in interop_trace.glsl. */
__device__ __forceinline__ float4 d_disk_color(const HitResult& hit, float rs) {
    float r = sqrtf(fmaf(hit.hit_point.x, hit.hit_point.x,
                         hit.hit_point.y * hit.hit_point.y));

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

    float T_norm = powf(flux, 0.25f);
    float3 color;
    if (T_norm > 0.6f) {
        color = make_f3(1.0f, 0.9f, 0.8f);
    } else if (T_norm > 0.3f) {
        color = make_f3(1.0f, 0.6f, 0.2f);
    } else {
        color = make_f3(0.8f, 0.2f, 0.1f);
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

    float intensity = flux * 2.0f * spectral;

    /* Doppler beaming approximation */
    float v = sqrtf(0.5f * rs / fmaxf(r, D_EPSILON));
    float cos_phi = cosf(hit.phi);
    float doppler = 1.0f + d_doppler_strength * v * cos_phi;
    intensity *= doppler * doppler * doppler;

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

    return make_float4(color.x * intensity, color.y * intensity,
                       color.z * intensity, 1.0f);
}

/* Background sky color (simplified -- no cubemap in baseline, just gradient) */
__device__ __forceinline__ float4 d_background_color(float3 dir) {
    float3 n = d_normalize(dir);
    /* Simple sky gradient: dark near horizon, blue at zenith */
    float y = fabsf(n.y);
    float3 sky = make_f3(0.01f * y, 0.01f * y, 0.03f * y);
    return make_float4(sky.x, sky.y, sky.z, 1.0f);
}

/* Full shading dispatch */
__device__ __forceinline__ float4 d_shade_hit(const HitResult& hit, float3 cam_pos) {
    if (hit.hit_horizon) {
        return make_float4(0.0f, 0.0f, 0.0f, 1.0f);
    }
    if (hit.hit_disk) {
        return d_disk_color(hit, d_rs);
    }
    float3 dir = d_normalize(d_sub(hit.hit_point, cam_pos));
    return d_background_color(dir);
}

/* ========================================================================
 * Ray generation from pixel coordinates
 * ======================================================================== */

__device__ __forceinline__ float3 d_ray_dir(int px, int py) {
    float u = (2.0f * (px + 0.5f) / (float)d_width - 1.0f) * d_fov_scale;
    float v = (2.0f * (py + 0.5f) / (float)d_height - 1.0f) * d_fov_scale;
    /* Correct for aspect ratio */
    u *= (float)d_width / (float)d_height;

    float3 local_dir = d_normalize(make_f3(u, v, -1.0f));
    return d_mat3_mul(d_cam_basis, local_dir);
}

#endif /* BLACKHOLE_CUDA_DEVICE_PHYSICS_CUH */
