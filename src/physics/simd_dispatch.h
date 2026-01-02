/**
 * @file simd_dispatch.h
 * @brief Runtime SIMD architecture detection and tiered dispatch.
 *
 * Provides:
 * - Compile-time and runtime detection of SSE2/SSE3/SSE4/AVX/AVX2/AVX-512
 * - FMA, FMA3, FMA4 variant detection
 * - SLEEF integration for vectorized transcendentals
 * - xsimd::dispatch wrapper for tiered fallback execution
 *
 * Architecture tiers (lowest to highest):
 *   SSE2 -> SSE3 -> SSSE3 -> SSE4.1 -> SSE4.2 -> AVX -> AVX2+FMA -> AVX-512
 *
 * Usage:
 *   #include "simd_dispatch.h"
 *   auto tier = simd::getCurrentArchTier();
 *   simd::dispatch_christoffel(r, dr, dtheta, dphi, theta, r_s, out, count);
 */

#ifndef PHYSICS_SIMD_DISPATCH_H
#define PHYSICS_SIMD_DISPATCH_H

#include <cstddef>
#include <cstdint>

// ============================================================================
// Feature Detection Macros
// ============================================================================

#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
#define SIMD_X86 1
#else
#define SIMD_X86 0
#endif

#if defined(__aarch64__) || defined(_M_ARM64)
#define SIMD_ARM64 1
#else
#define SIMD_ARM64 0
#endif

// CPUID-based runtime detection for x86
#if SIMD_X86
#ifdef _MSC_VER
#include <intrin.h>
#else
#include <cpuid.h>
#endif
#endif

// ============================================================================
// SLEEF Integration
// ============================================================================

#if BLACKHOLE_ENABLE_SLEEF
#include <sleef.h>

// SLEEF provides multiple accuracy levels:
// - _u10 : 1.0 ULP accuracy (high precision)
// - _u35 : 3.5 ULP accuracy (faster, still good)
// We use _u10 for physics accuracy by default.

#if defined(__AVX512F__)
#define SLEEF_SIN_VEC  Sleef_sind8_u10avx512f
#define SLEEF_COS_VEC  Sleef_cosd8_u10avx512f
#define SLEEF_SQRT_VEC Sleef_sqrtd8_avx512f
#define SLEEF_VEC_WIDTH 8
#elif defined(__AVX2__) || defined(__FMA__)
#define SLEEF_SIN_VEC  Sleef_sind4_u10avx2
#define SLEEF_COS_VEC  Sleef_cosd4_u10avx2
#define SLEEF_SQRT_VEC Sleef_sqrtd4_avx2
#define SLEEF_VEC_WIDTH 4
#elif defined(__AVX__)
#define SLEEF_SIN_VEC  Sleef_sind4_u10avx
#define SLEEF_COS_VEC  Sleef_cosd4_u10avx
#define SLEEF_SQRT_VEC Sleef_sqrtd4_avx
#define SLEEF_VEC_WIDTH 4
#elif defined(__SSE4_1__) || defined(__SSE4_2__)
#define SLEEF_SIN_VEC  Sleef_sind2_u10sse4
#define SLEEF_COS_VEC  Sleef_cosd2_u10sse4
#define SLEEF_SQRT_VEC Sleef_sqrtd2_sse4
#define SLEEF_VEC_WIDTH 2
#elif defined(__SSE2__)
#define SLEEF_SIN_VEC  Sleef_sind2_u10sse2
#define SLEEF_COS_VEC  Sleef_cosd2_u10sse2
#define SLEEF_SQRT_VEC Sleef_sqrtd2_sse2
#define SLEEF_VEC_WIDTH 2
#else
// Scalar fallback
#define SLEEF_SIN_VEC  Sleef_sin_u10
#define SLEEF_COS_VEC  Sleef_cos_u10
#define SLEEF_SQRT_VEC Sleef_sqrt
#define SLEEF_VEC_WIDTH 1
#endif

#endif // BLACKHOLE_ENABLE_SLEEF

// ============================================================================
// xsimd Integration
// ============================================================================

#if BLACKHOLE_ENABLE_XSIMD
#include <xsimd/xsimd.hpp>
#endif

namespace simd {

// ============================================================================
// Architecture Tier Enumeration
// ============================================================================

/**
 * @brief SIMD architecture tiers from lowest to highest capability.
 *
 * Each tier implies support for all lower tiers.
 * FMA is treated as a modifier that can be combined with AVX/AVX2.
 */
enum class ArchTier : uint8_t {
    SCALAR   = 0,   ///< No SIMD, scalar fallback
    SSE2     = 1,   ///< 128-bit, baseline x86-64
    SSE3     = 2,   ///< 128-bit, horizontal ops
    SSSE3    = 3,   ///< 128-bit, shuffle improvements
    SSE41    = 4,   ///< 128-bit, blend, round, extract
    SSE42    = 5,   ///< 128-bit, string ops, popcnt
    AVX      = 6,   ///< 256-bit, VEX encoding
    AVX_FMA  = 7,   ///< 256-bit + FMA3
    AVX2     = 8,   ///< 256-bit integer SIMD
    AVX2_FMA = 9,   ///< 256-bit + FMA3 (optimal tier for most)
    AVX512   = 10,  ///< 512-bit (rare on consumer CPUs)
};

/**
 * @brief FMA variant support flags.
 */
enum class FmaVariant : uint8_t {
    NONE = 0,
    FMA3 = 1,   ///< Intel/AMD 3-operand FMA (vfmadd132pd, etc.)
    FMA4 = 2,   ///< AMD 4-operand FMA (deprecated, Bulldozer only)
};

// ============================================================================
// Runtime Detection
// ============================================================================

#if SIMD_X86

namespace detail {

inline void cpuid(int info[4], int leaf, int subleaf = 0) {
#ifdef _MSC_VER
    __cpuidex(info, leaf, subleaf);
#else
    __cpuid_count(leaf, subleaf, info[0], info[1], info[2], info[3]);
#endif
}

inline uint64_t xgetbv(uint32_t xcr) {
#ifdef _MSC_VER
    return _xgetbv(xcr);
#else
    uint32_t eax, edx;
    __asm__ volatile("xgetbv" : "=a"(eax), "=d"(edx) : "c"(xcr));
    return (static_cast<uint64_t>(edx) << 32) | eax;
#endif
}

} // namespace detail

/**
 * @brief Detect the highest available SIMD tier at runtime.
 *
 * Uses CPUID and XGETBV to determine actual CPU capabilities.
 * Cached after first call for performance.
 */
inline ArchTier getCurrentArchTier() {
    static ArchTier cached = ArchTier::SCALAR;
    static bool detected = false;

    if (detected) return cached;
    detected = true;

    int info[4];

    // Get basic CPUID info
    detail::cpuid(info, 0);
    int max_leaf = info[0];
    if (max_leaf < 1) {
        cached = ArchTier::SCALAR;
        return cached;
    }

    // Leaf 1: SSE, SSE2, SSE3, SSSE3, SSE4.1, SSE4.2, AVX, FMA
    detail::cpuid(info, 1);
    bool has_sse2  = (info[3] & (1 << 26)) != 0;
    bool has_sse3  = (info[2] & (1 <<  0)) != 0;
    bool has_ssse3 = (info[2] & (1 <<  9)) != 0;
    bool has_sse41 = (info[2] & (1 << 19)) != 0;
    bool has_sse42 = (info[2] & (1 << 20)) != 0;
    bool has_avx   = (info[2] & (1 << 28)) != 0;
    bool has_fma3  = (info[2] & (1 << 12)) != 0;
    bool has_osxsave = (info[2] & (1 << 27)) != 0;

    // Check OS AVX support via XGETBV
    bool os_avx_support = false;
    bool os_avx512_support = false;
    if (has_osxsave) {
        uint64_t xcr0 = detail::xgetbv(0);
        os_avx_support = (xcr0 & 0x6) == 0x6;  // XMM + YMM state
        os_avx512_support = (xcr0 & 0xE6) == 0xE6;  // + ZMM state
    }

    // Leaf 7: AVX2, AVX-512
    bool has_avx2 = false;
    bool has_avx512f = false;
    if (max_leaf >= 7) {
        detail::cpuid(info, 7, 0);
        has_avx2 = (info[1] & (1 << 5)) != 0;
        has_avx512f = (info[1] & (1 << 16)) != 0;
    }

    // Determine tier
    if (has_avx512f && os_avx512_support) {
        cached = ArchTier::AVX512;
    } else if (has_avx2 && os_avx_support && has_fma3) {
        cached = ArchTier::AVX2_FMA;
    } else if (has_avx2 && os_avx_support) {
        cached = ArchTier::AVX2;
    } else if (has_avx && os_avx_support && has_fma3) {
        cached = ArchTier::AVX_FMA;
    } else if (has_avx && os_avx_support) {
        cached = ArchTier::AVX;
    } else if (has_sse42) {
        cached = ArchTier::SSE42;
    } else if (has_sse41) {
        cached = ArchTier::SSE41;
    } else if (has_ssse3) {
        cached = ArchTier::SSSE3;
    } else if (has_sse3) {
        cached = ArchTier::SSE3;
    } else if (has_sse2) {
        cached = ArchTier::SSE2;
    } else {
        cached = ArchTier::SCALAR;
    }

    return cached;
}

/**
 * @brief Check for FMA variant support.
 */
inline FmaVariant getFmaVariant() {
    int info[4];
    detail::cpuid(info, 1);
    bool has_fma3 = (info[2] & (1 << 12)) != 0;

    // Check for FMA4 (AMD Bulldozer, rare)
    detail::cpuid(info, static_cast<int>(0x80000001u));
    bool has_fma4 = (info[2] & (1 << 16)) != 0;

    if (has_fma4) return FmaVariant::FMA4;
    if (has_fma3) return FmaVariant::FMA3;
    return FmaVariant::NONE;
}

#elif SIMD_ARM64

inline ArchTier getCurrentArchTier() {
    // ARM64 always has NEON, equivalent to SSE4-level
    return ArchTier::SSE42;  // Approximate mapping
}

inline FmaVariant getFmaVariant() {
    // ARM64 NEON always has FMA
    return FmaVariant::FMA3;
}

#else

inline ArchTier getCurrentArchTier() {
    return ArchTier::SCALAR;
}

inline FmaVariant getFmaVariant() {
    return FmaVariant::NONE;
}

#endif // SIMD_X86

// ============================================================================
// Tier Information
// ============================================================================

/**
 * @brief Get human-readable name for architecture tier.
 */
inline const char* getArchTierName(ArchTier tier) {
    switch (tier) {
        case ArchTier::SCALAR:   return "Scalar";
        case ArchTier::SSE2:     return "SSE2";
        case ArchTier::SSE3:     return "SSE3";
        case ArchTier::SSSE3:    return "SSSE3";
        case ArchTier::SSE41:    return "SSE4.1";
        case ArchTier::SSE42:    return "SSE4.2";
        case ArchTier::AVX:      return "AVX";
        case ArchTier::AVX_FMA:  return "AVX+FMA";
        case ArchTier::AVX2:     return "AVX2";
        case ArchTier::AVX2_FMA: return "AVX2+FMA";
        case ArchTier::AVX512:   return "AVX-512";
        default:                 return "Unknown";
    }
}

/**
 * @brief Get SIMD vector width in doubles for a tier.
 */
inline std::size_t getVectorWidth(ArchTier tier) {
    switch (tier) {
        case ArchTier::AVX512:   return 8;
        case ArchTier::AVX2_FMA:
        case ArchTier::AVX2:
        case ArchTier::AVX_FMA:
        case ArchTier::AVX:      return 4;
        case ArchTier::SSE42:
        case ArchTier::SSE41:
        case ArchTier::SSSE3:
        case ArchTier::SSE3:
        case ArchTier::SSE2:     return 2;
        default:                 return 1;
    }
}

// ============================================================================
// xsimd Dispatch Helpers
// ============================================================================

#if BLACKHOLE_ENABLE_XSIMD

/**
 * @brief Architecture list for xsimd::dispatch based on compile-time support.
 *
 * xsimd::dispatch selects the best available implementation at runtime.
 * We include all architectures that might be available on the target.
 */
#if defined(__AVX512F__)
using supported_archs = xsimd::arch_list<
    xsimd::avx512bw,
    xsimd::avx512dq,
    xsimd::avx512cd,
    xsimd::avx512f,
    xsimd::fma3<xsimd::avx2>,
    xsimd::avx2,
    xsimd::fma3<xsimd::avx>,
    xsimd::avx,
    xsimd::sse4_2,
    xsimd::sse4_1,
    xsimd::ssse3,
    xsimd::sse3,
    xsimd::sse2
>;
#elif defined(__AVX2__)
using supported_archs = xsimd::arch_list<
    xsimd::fma3<xsimd::avx2>,
    xsimd::avx2,
    xsimd::fma3<xsimd::avx>,
    xsimd::avx,
    xsimd::sse4_2,
    xsimd::sse4_1,
    xsimd::ssse3,
    xsimd::sse3,
    xsimd::sse2
>;
#elif defined(__AVX__)
using supported_archs = xsimd::arch_list<
    xsimd::fma3<xsimd::avx>,
    xsimd::avx,
    xsimd::sse4_2,
    xsimd::sse4_1,
    xsimd::ssse3,
    xsimd::sse3,
    xsimd::sse2
>;
#elif defined(__SSE4_2__)
using supported_archs = xsimd::arch_list<
    xsimd::sse4_2,
    xsimd::sse4_1,
    xsimd::ssse3,
    xsimd::sse3,
    xsimd::sse2
>;
#elif defined(__SSE2__)
using supported_archs = xsimd::arch_list<
    xsimd::sse2
>;
#else
using supported_archs = xsimd::arch_list<>;
#endif

/**
 * @brief Get the currently selected xsimd architecture name.
 */
inline const char* getXsimdArchName() {
    return xsimd::default_arch::name();
}

/**
 * @brief Get xsimd batch size for doubles on current architecture.
 */
inline std::size_t getXsimdBatchSize() {
    return xsimd::batch<double>::size;
}

#endif // BLACKHOLE_ENABLE_XSIMD

// ============================================================================
// SLEEF Dispatch Helpers
// ============================================================================

#if BLACKHOLE_ENABLE_SLEEF

/**
 * @brief Get SLEEF vector width for doubles.
 */
inline std::size_t getSleefVectorWidth() {
    return SLEEF_VEC_WIDTH;
}

/**
 * @brief Get SLEEF accuracy mode name.
 */
inline const char* getSleefAccuracyMode() {
    return "u10 (1.0 ULP)";
}

#endif // BLACKHOLE_ENABLE_SLEEF

// ============================================================================
// Diagnostic Output
// ============================================================================

/**
 * @brief Print SIMD configuration to stdout.
 */
inline void printSimdConfig() {
    ArchTier tier = getCurrentArchTier();
    FmaVariant fma = getFmaVariant();

    printf("=== SIMD Configuration ===\n");
    printf("Runtime tier: %s\n", getArchTierName(tier));
    printf("Vector width: %zu doubles\n", getVectorWidth(tier));
    printf("FMA variant: %s\n",
           fma == FmaVariant::FMA3 ? "FMA3" :
           fma == FmaVariant::FMA4 ? "FMA4" : "None");

#if BLACKHOLE_ENABLE_XSIMD
    printf("xsimd arch: %s\n", getXsimdArchName());
    printf("xsimd batch<double>: %zu\n", getXsimdBatchSize());
#else
    printf("xsimd: disabled\n");
#endif

#if BLACKHOLE_ENABLE_SLEEF
    printf("SLEEF width: %zu doubles\n", getSleefVectorWidth());
    printf("SLEEF accuracy: %s\n", getSleefAccuracyMode());
#else
    printf("SLEEF: disabled\n");
#endif

    printf("==========================\n");
}

} // namespace simd

#endif // PHYSICS_SIMD_DISPATCH_H
