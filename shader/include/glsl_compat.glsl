/**
 * glsl_compat.glsl
 * GLSL version compatibility layer with feature detection.
 *
 * Supports: GLSL 4.60 → 4.50 → 4.30 → 3.30 fallback chain
 *
 * Include this AFTER #version directive but BEFORE other includes.
 * This file detects available features and provides fallbacks.
 */

#ifndef GLSL_COMPAT_GLSL
#define GLSL_COMPAT_GLSL

// ============================================================================
// Version Detection
// ============================================================================

// GLSL version is defined by __VERSION__ macro
// 460 = GLSL 4.60, 450 = GLSL 4.50, 430 = GLSL 4.30, 330 = GLSL 3.30

#if __VERSION__ >= 460
    #define GLSL_VERSION 460
    #define GLSL_460 1
    #define GLSL_450 1
    #define GLSL_430 1
    #define GLSL_330 1
#elif __VERSION__ >= 450
    #define GLSL_VERSION 450
    #define GLSL_450 1
    #define GLSL_430 1
    #define GLSL_330 1
#elif __VERSION__ >= 430
    #define GLSL_VERSION 430
    #define GLSL_430 1
    #define GLSL_330 1
#elif __VERSION__ >= 330
    #define GLSL_VERSION 330
    #define GLSL_330 1
#else
    #error "Minimum GLSL 3.30 required"
#endif

// ============================================================================
// Extension Detection and Enabling
// ============================================================================

// GPU shader5 for precise operations (GLSL 4.00+)
#if __VERSION__ >= 400
    #define HAS_GPU_SHADER5 1
#else
    #define HAS_GPU_SHADER5 0
#endif

// Compute shaders (GLSL 4.30+)
#if defined(GLSL_430)
    #define HAS_COMPUTE_SHADERS 1
#else
    #define HAS_COMPUTE_SHADERS 0
#endif

// Shader storage buffer objects (GLSL 4.30+)
#if defined(GLSL_430)
    #define HAS_SSBO 1
#else
    #define HAS_SSBO 0
#endif

// Image load/store (GLSL 4.20+)
#if __VERSION__ >= 420
    #define HAS_IMAGE_LOAD_STORE 1
#else
    #define HAS_IMAGE_LOAD_STORE 0
#endif

// ============================================================================
// Precision Qualifiers
// ============================================================================

// High precision is always available in desktop GLSL
// For mobile compatibility, we'd need to check
#ifdef GL_ES
    precision highp float;
    precision highp int;
#endif

// ============================================================================
// Math Function Compatibility
// ============================================================================

// fma() - fused multiply-add (GLSL 4.00+, but emulated on 3.30)
#if !defined(GLSL_430)
float fma_compat(float a, float b, float c) {
    return a * b + c;
}
vec2 fma_compat(vec2 a, vec2 b, vec2 c) {
    return a * b + c;
}
vec3 fma_compat(vec3 a, vec3 b, vec3 c) {
    return a * b + c;
}
vec4 fma_compat(vec4 a, vec4 b, vec4 c) {
    return a * b + c;
}
#define FMA(a, b, c) fma_compat(a, b, c)
#else
#define FMA(a, b, c) fma(a, b, c)
#endif

// frexp/ldexp (GLSL 4.00+)
#if __VERSION__ < 400
// Fallback implementations for older GLSL
float frexp_compat(float x, out int exp) {
    if (x == 0.0) {
        exp = 0;
        return 0.0;
    }
    float absX = abs(x);
    exp = int(floor(log2(absX))) + 1;
    return x / exp2(float(exp));
}

float ldexp_compat(float x, int exp) {
    return x * exp2(float(exp));
}
#define FREXP(x, e) frexp_compat(x, e)
#define LDEXP(x, e) ldexp_compat(x, e)
#else
#define FREXP(x, e) frexp(x, e)
#define LDEXP(x, e) ldexp(x, e)
#endif

// ============================================================================
// Atomic Operations Compatibility
// ============================================================================

#if HAS_SSBO
    // Atomic operations available with SSBO
    #define ATOMIC_ADD(mem, data) atomicAdd(mem, data)
    #define ATOMIC_MIN(mem, data) atomicMin(mem, data)
    #define ATOMIC_MAX(mem, data) atomicMax(mem, data)
    #define ATOMIC_EXCHANGE(mem, data) atomicExchange(mem, data)
    #define ATOMIC_COMPARE_SWAP(mem, compare, data) atomicCompSwap(mem, compare, data)
#endif

// ============================================================================
// Barrier Functions
// ============================================================================

#if HAS_COMPUTE_SHADERS
    #define MEMORY_BARRIER() memoryBarrier()
    #define MEMORY_BARRIER_SHARED() memoryBarrierShared()
    #define MEMORY_BARRIER_BUFFER() memoryBarrierBuffer()
    #define MEMORY_BARRIER_IMAGE() memoryBarrierImage()
    #define GROUP_MEMORY_BARRIER() groupMemoryBarrier()
    #define BARRIER() barrier()
#endif

// ============================================================================
// Inverse Trigonometric Stability
// ============================================================================

// Clamped acos to avoid NaN from floating point errors
float acos_safe(float x) {
    return acos(clamp(x, -1.0, 1.0));
}

// Clamped asin to avoid NaN
float asin_safe(float x) {
    return asin(clamp(x, -1.0, 1.0));
}

// atan2 with proper quadrant handling
float atan2_safe(float y, float x) {
    if (abs(x) < 1e-10 && abs(y) < 1e-10) {
        return 0.0;
    }
    return atan(y, x);
}

// ============================================================================
// Extended Precision Helpers
// ============================================================================

// Kahan summation for reducing floating point error
struct KahanSum {
    float sum;
    float compensation;
};

KahanSum kahan_init() {
    KahanSum k;
    k.sum = 0.0;
    k.compensation = 0.0;
    return k;
}

void kahan_add(inout KahanSum k, float value) {
    float y = value - k.compensation;
    float t = k.sum + y;
    k.compensation = (t - k.sum) - y;
    k.sum = t;
}

float kahan_result(KahanSum k) {
    return k.sum;
}

// ============================================================================
// Numerical Constants with Extended Precision
// ============================================================================

// These constants use maximum float precision
const float PI_HP = 3.14159265358979323846;
const float TWO_PI_HP = 6.28318530717958647693;
const float HALF_PI_HP = 1.57079632679489661923;
const float INV_PI_HP = 0.31830988618379067154;
const float INV_TWO_PI_HP = 0.15915494309189533577;

const float E_HP = 2.71828182845904523536;
const float LN2_HP = 0.69314718055994530942;
const float LN10_HP = 2.30258509299404568402;
const float LOG2E_HP = 1.44269504088896340736;
const float LOG10E_HP = 0.43429448190325182765;

const float SQRT2_HP = 1.41421356237309504880;
const float SQRT3_HP = 1.73205080756887729353;
const float INV_SQRT2_HP = 0.70710678118654752440;

// ============================================================================
// Double Emulation (for extended precision where needed)
// ============================================================================

// Two-float representation for extended precision
// Represents value as (hi + lo) where |lo| < ulp(hi)/2
struct Float2 {
    float hi;
    float lo;
};

Float2 float2_from_float(float a) {
    Float2 result;
    result.hi = a;
    result.lo = 0.0;
    return result;
}

Float2 float2_add(Float2 a, Float2 b) {
    // Dekker's algorithm for error-free addition
    float s = a.hi + b.hi;
    float v = s - a.hi;
    float e = (a.hi - (s - v)) + (b.hi - v);
    float c = e + a.lo + b.lo;

    Float2 result;
    result.hi = s + c;
    result.lo = c - (result.hi - s);
    return result;
}

Float2 float2_mul(Float2 a, Float2 b) {
    // Dekker's multiplication
    float p = a.hi * b.hi;
    float e = FMA(a.hi, b.hi, -p);
    e += a.hi * b.lo + a.lo * b.hi;

    Float2 result;
    result.hi = p + e;
    result.lo = e - (result.hi - p);
    return result;
}

float float2_to_float(Float2 a) {
    return a.hi + a.lo;
}

// ============================================================================
// Interpolation Helpers
// ============================================================================

// Hermite interpolation (smooth step with derivatives)
float hermite(float t) {
    return t * t * (3.0 - 2.0 * t);
}

// Quintic interpolation (smoother, C2 continuous)
float quintic(float t) {
    return t * t * t * (t * (t * 6.0 - 15.0) + 10.0);
}

// ============================================================================
// Matrix Utilities (available in all versions but wrapped for consistency)
// ============================================================================

// Quaternion to rotation matrix
mat3 quat_to_mat3(vec4 q) {
    float xx = q.x * q.x;
    float yy = q.y * q.y;
    float zz = q.z * q.z;
    float xy = q.x * q.y;
    float xz = q.x * q.z;
    float yz = q.y * q.z;
    float wx = q.w * q.x;
    float wy = q.w * q.y;
    float wz = q.w * q.z;

    return mat3(
        1.0 - 2.0 * (yy + zz), 2.0 * (xy + wz), 2.0 * (xz - wy),
        2.0 * (xy - wz), 1.0 - 2.0 * (xx + zz), 2.0 * (yz + wx),
        2.0 * (xz + wy), 2.0 * (yz - wx), 1.0 - 2.0 * (xx + yy)
    );
}

// Axis-angle to rotation matrix
mat3 axis_angle_to_mat3(vec3 axis, float angle) {
    float c = cos(angle);
    float s = sin(angle);
    float t = 1.0 - c;
    vec3 n = normalize(axis);

    return mat3(
        t * n.x * n.x + c,       t * n.x * n.y + s * n.z, t * n.x * n.z - s * n.y,
        t * n.x * n.y - s * n.z, t * n.y * n.y + c,       t * n.y * n.z + s * n.x,
        t * n.x * n.z + s * n.y, t * n.y * n.z - s * n.x, t * n.z * n.z + c
    );
}

#endif // GLSL_COMPAT_GLSL
