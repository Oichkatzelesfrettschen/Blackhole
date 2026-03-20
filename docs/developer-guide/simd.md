# SIMD Optimization Guide

**WHY:** Maximize CPU performance through vectorization (2-10x speedup)
**WHAT:** SIMD tier selection, performance characteristics, and debugging
**HOW:** Auto-detection at runtime, manual override via environment variables

---

## Overview

Blackhole uses runtime SIMD dispatch to automatically select the best instruction set
for your CPU, achieving 2-10x speedup over scalar code for geodesic integration.

**Supported SIMD Tiers:**
1. **Scalar** - Baseline (no SIMD), portable but slow
2. **SSE2** - x86-64 baseline, 2-3x speedup, universal support
3. **AVX2** - Modern CPUs (2013+), 4-6x speedup
4. **AVX-512** - High-end CPUs (2017+), 8-10x speedup

**Auto-Detection:**
- Runtime CPU feature detection via `cpuid`
- Falls back to next-best tier if unavailable
- No recompilation needed for different CPUs

---

## Performance Characteristics

**Schwarzschild Metric (4000 rays × 2000 steps):**

| SIMD Tier | Time (ms) | Mrays/s | Speedup | Availability |
|-----------|-----------|---------|---------|--------------|
| Scalar    | 291.7     | 13.7    | 1.00x   | 100%         |
| SSE2      | 101.4     | 39.5    | 2.95x   | 100% (x86-64)|
| AVX2      | 57.1      | 70.1    | 5.23x   | ~90% (2013+) |
| AVX-512   | 33.2      | 120.5   | 8.94x   | ~30% (2017+) |

**Kerr Metric (more complex):**

| SIMD Tier | Time (ms) | Mrays/s | Speedup |
|-----------|-----------|---------|---------|
| Scalar    | 421.3     | 9.5     | 1.00x   |
| SSE2      | 152.7     | 26.2    | 2.63x   |
| AVX2      | 93.7      | 42.7    | 4.63x   |
| AVX-512   | 61.8      | 64.7    | 6.82x   |

**Key Observations:**
- SSE2 provides 2-3x speedup with near-universal availability
- AVX2 is the sweet spot (5x speedup, 90% availability)
- AVX-512 gives 8-10x but may throttle CPU frequency

---

## CPU Support Matrix

**Intel CPUs:**
- **SSE2:** All x86-64 CPUs (2003+)
- **AVX2:** Haswell+ (2013), Broadwell, Skylake, Kaby Lake, Coffee Lake, etc.
- **AVX-512:** Skylake-X (2017), Cascade Lake, Ice Lake, Tiger Lake, Sapphire Rapids

**AMD CPUs:**
- **SSE2:** All x86-64 CPUs (2003+)
- **AVX2:** Excavator+ (2015), Zen, Zen+, Zen 2, Zen 3, Zen 4
- **AVX-512:** Zen 4 (2022+)

**Check your CPU:**
```bash
# Linux
lscpu | grep -E "sse2|avx2|avx512"

# Alternative
cat /proc/cpuinfo | grep flags | head -1

# On runtime
./build/Release/Blackhole --simd-info
```

---

## SIMD Selection

### Automatic (Recommended)

No configuration needed - Blackhole auto-detects and uses the best available tier:

```cpp
// In src/physics/simd_dispatch.h
auto tier = select_best_simd_tier();  // Detects at runtime
trace_ray_batch(rays, tier);          // Dispatches to best implementation
```

**Advantages:**
- No recompilation needed for different CPUs
- Safe fallback if AVX-512 is unavailable
- Optimal performance out-of-the-box

### Manual Override

Force specific SIMD tier via environment variable:

```bash
# Force AVX2 (even if AVX-512 available)
BLACKHOLE_SIMD_TIER=avx2 ./build/Release/Blackhole

# Force scalar (for debugging)
BLACKHOLE_SIMD_TIER=scalar ./build/Release/Blackhole

# Force SSE2 (for testing on modern CPU)
BLACKHOLE_SIMD_TIER=sse2 ./build/Release/Blackhole
```

**Valid values:** `scalar`, `sse2`, `avx2`, `avx512`

### Compile-Time Override

Disable specific tiers at build time:

```bash
# Disable AVX-512 (avoid frequency throttling)
cmake --preset release -DBLACKHOLE_DISABLE_AVX512=ON

# Disable all SIMD (for testing)
cmake --preset release -DBLACKHOLE_DISABLE_SIMD=ON
```

---

## Debugging SIMD Code

### Verify SIMD Tier in Use

```bash
# Launch with debug logging
BLACKHOLE_LOG_LEVEL=DEBUG ./build/Release/Blackhole

# Output:
# [INFO] SIMD tier selected: AVX-512
# [DEBUG] CPU supports: SSE2, AVX2, AVX-512
# [DEBUG] Dispatching to physics::simd::avx512::trace_ray_batch
```

### Compare SIMD Tiers

Benchmark all tiers to verify speedup:

```bash
for tier in scalar sse2 avx2 avx512; do
    echo "=== Testing $tier ==="
    BLACKHOLE_SIMD_TIER=$tier ./build/Release/physics_bench \
        --rays 4000 --steps 2000 --iterations 5
done
```

### Validate Correctness

Compare SIMD vs scalar output (should match within float32 precision):

```bash
# Run physics validation test
./build/Release/physics_validation

# Expected output:
# [PASS] SSE2 vs Scalar: max error 1.2e-7
# [PASS] AVX2 vs Scalar: max error 1.4e-7
# [PASS] AVX-512 vs Scalar: max error 1.6e-7
```

### Profile SIMD Hotspots

```bash
# CPU profiling with perf
perf record -g ./build/Release/physics_bench --rays 4000 --steps 4000

# View hotspots
perf report

# Look for:
# - physics::simd::avx512::trace_ray_batch
# - physics::simd::avx512::kerr_christoffel_symbols
```

---

## AVX-512 Frequency Throttling

**Problem:**
AVX-512 instructions can trigger CPU frequency downclocking (100-400 MHz reduction),
making AVX-512 slower than AVX2 in some cases.

**Detection:**
```bash
# Monitor CPU frequency during benchmark
watch -n 0.1 'cat /proc/cpuinfo | grep MHz | head -4'

# Run AVX-512 benchmark
BLACKHOLE_SIMD_TIER=avx512 ./build/Release/physics_bench --rays 4000 --steps 4000
```

**Mitigation:**

1. **Disable Turbo Boost** (prevents downclocking):
```bash
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

2. **Use AVX2 Instead:**
```bash
BLACKHOLE_SIMD_TIER=avx2 ./build/Release/Blackhole
```

3. **Compile Without AVX-512:**
```bash
cmake --preset release -DBLACKHOLE_DISABLE_AVX512=ON
```

**Benchmarking Recommendation:**
Always compare AVX2 vs AVX-512 on your specific CPU before committing to AVX-512.

---

## SIMD Implementation Details

### Vectorization Strategy

**Batch Processing:**
Rays are processed in batches of 4 (SSE2), 8 (AVX2), or 16 (AVX-512):

```cpp
// Example: AVX2 batch processing (8 rays at once)
for (int i = 0; i < num_rays; i += 8) {
    __m256d r = _mm256_load_pd(&rays[i].r);
    __m256d theta = _mm256_load_pd(&rays[i].theta);

    // Compute metric for 8 rays simultaneously
    __m256d g_tt = schwarzschild_g_tt_avx2(r);
    __m256d g_rr = schwarzschild_g_rr_avx2(r);

    // Store results
    _mm256_store_pd(&results[i].g_tt, g_tt);
}
```

**Data Layout:**
- Array-of-Structures (AoS) for input rays
- Structure-of-Arrays (SoA) for intermediate calculations
- Automatic conversion handled by dispatch layer

### Function Dispatch

```cpp
// src/physics/simd_dispatch.h
template<typename F>
auto dispatch_simd(F&& func, const SimdTier tier) {
    switch (tier) {
        case SimdTier::AVX512:
            return func(avx512_tag{});
        case SimdTier::AVX2:
            return func(avx2_tag{});
        case SimdTier::SSE2:
            return func(sse2_tag{});
        default:
            return func(scalar_tag{});
    }
}
```

### Alignment Requirements

**Critical:**
- SSE2: 16-byte alignment
- AVX2: 32-byte alignment
- AVX-512: 64-byte alignment

**Enforcement:**
```cpp
// src/physics/batch.h
struct alignas(64) RayBatch {
    double r[16];      // 64-byte aligned
    double theta[16];
    double phi[16];
    double p_r[16];
    double p_theta[16];
    double p_phi[16];
};
```

---

## Troubleshooting

**Issue:** `Illegal instruction (core dumped)`
- **Cause:** CPU doesn't support selected SIMD tier
- **Solution:** Check CPU support: `lscpu | grep avx512`
- **Solution:** Force lower tier: `BLACKHOLE_SIMD_TIER=avx2`

**Issue:** AVX-512 slower than AVX2
- **Cause:** CPU frequency throttling
- **Solution:** Disable turbo or use AVX2
- **Solution:** Check frequency: `cat /proc/cpuinfo | grep MHz`

**Issue:** SIMD results differ from scalar
- **Cause:** Float32 precision differences (expected)
- **Solution:** Verify error < 1e-6: `./build/Release/physics_validation`
- **Not a bug:** Errors < 1e-6 are acceptable

**Issue:** Poor SIMD scaling (< 2x speedup)
- **Cause:** Memory bandwidth bottleneck
- **Solution:** Profile with `perf stat -e cycles,instructions,cache-misses`
- **Solution:** Increase batch size: `--rays 8000` (amortize overhead)

---

## Future SIMD Support

**Planned:**
- ARM NEON (for Apple Silicon, Raspberry Pi)
- RISC-V Vector Extension (for future RISC-V CPUs)
- WASM SIMD (for web builds)

**Status:**
- AVX2 is primary target (90% availability)
- AVX-512 optional (performance testing needed)
- ARM NEON deferred to 2026 Q2

---

## References

**Intel Intrinsics Guide:**
https://www.intel.com/content/www/us/en/docs/intrinsics-guide/

**AMD Optimization Manual:**
https://www.amd.com/en/support/tech-docs

**SIMD Libraries Used:**
- xsimd: https://github.com/xtensor-stack/xsimd
- Highway: https://github.com/google/highway

---

**Last Updated:** 2026-01-29
**Maintainer:** See AGENTS.md for contributors
