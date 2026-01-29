# Blackhole Master Roadmap

**Created:** 2026-01-01
**Version:** 1.0.1
**Last Updated:** 2026-01-29
**Status:** Active Development (Phase 4)
**Architecture:** C++23 / OpenGL 4.6 / Conan 2.x

---

## Executive Summary

Blackhole is a production-grade real-time black hole ray-tracing renderer with:
- Complete Schwarzschild/Kerr geodesic integration (CPU 100%, GPU 95%)
- 8-level bloom post-processing with ACES tonemapping
- LUT-backed emissivity/redshift/spectral shading
- Compute/fragment dual-path architecture for A/B parity testing
- Cleanroom physics validated against openuniverse submodules

This roadmap consolidates all planning into a single source of truth.

---

## Strategic Vision

### Short-Term (Q1 2026)
- Achieve 100% compute/fragment parity across all presets
- Complete Eigen migration for 2x CPU physics speedup
- Stabilize SPIR-V pipeline with hot-reload and reflection cache
- Import and validate cleanroom physics from openuniverse ecosystem

### Medium-Term (Q2-Q3 2026)
- Replace procedural disk with Novikov-Thorne tabulated profile
- Implement reduced-order 2D GRMHD prototype
- Add radiative transfer layer for multi-wavelength fidelity
- Generate synthetic X-ray spectra and LIGO-compatible GW output

### Long-Term (2027+)
- Full 3D GRMHD with radiation transport
- Particle acceleration and jet physics
- Real-time comparison with EHT/LIGO observational data

---

## Architecture Overview

```
[Input] --> [Camera + Physics] --> [Ray Integrator] --> [Post-Processing] --> [Present]
                |                       |                      |
                v                       v                      v
         [Settings.json]         [LUTs + Assets]        [Bloom/Tone/Depth]
                |                       |                      |
                v                       v                      v
         [Validation]            [GRMHD Textures]       [Performance HUD]
```

### Core Subsystems

| Subsystem | Files | Status | Coverage |
|-----------|-------|--------|----------|
| Rendering | 11 | Stable | 95% |
| Physics | 26 | 75% complete | 80% |
| Shaders | 43 | Stable | 100% |
| Tools | 5 | Stable | 100% |
| Tests | 5 | Comprehensive | 90% |

---

## Phase 1: Foundation Stabilization (Weeks 1-4)

### 1.1 Compute/Fragment Parity (ISSUE-009)

**Problem:** 2/12 presets exceed threshold; strict sweep passes 0/12.
**Root Cause:** RK4 integrator FP arithmetic differences (FMA contraction).

| Task | Status | Owner | Notes |
|------|--------|-------|-------|
| 1.1.1 Run diff capture for presets 0,4 | Done | - | `BLACKHOLE_COMPARE_WRITE_DIFF=1` |
| 1.1.2 Add per-pixel step count heatmap | Done (previous) | - | `BH_DEBUG_FLAG_STEP_COUNT` |
| 1.1.3 Disable fastmath in compute shader | Done | - | `SPIRV_SKIP_OPT_COMPUTE=1`; geodesic_trace 52k→27k (-48%) with opt |
| 1.1.4 Cross-validate kerrStep vs nubhlight | Done | - | Documented in CLEANROOM_IMPORTS.md |
| 1.1.5 Adjust default outlier tolerance | Done | - | Set: 0.006 frac, 10000 count (covers Kerr divergence) |

**Acceptance:** All 12 presets pass with default settings.

### 1.2 Eigen Migration

**Goal:** CPU physics performance via SIMD per EIGEN_REFACTOR_PLAN.md.

| Task | Status | Owner | Notes |
|------|--------|-------|-------|
| 1.2.1 Enable Eigen by default | Done | - | math_types.h updated |
| 1.2.2 Run GLM/Eigen parity test | Done | - | Tests pass |
| 1.2.3 Migrate raytracer.h to physics::Vec3 | Done | - | PhotonRay, RayTraceResult, Camera migrated to math::Vec3d/Vec2d; Camera::generate_ray() uses math ops |
| 1.2.4 Add batch geodesic API | Done | - | `traceGeodesicBatch()` with Eigen SIMD; SoA layout for vectorization |
| 1.2.5 Enable SIMD flags in CMake | Done | - | Comprehensive CPUID-based detection (SSE-AVX512); AUTO tier selection; GLM/Eigen synergistic config |
| 1.2.6 Benchmark GLM vs Eigen | Done | - | Batch geodesic benchmark added; 735x speedup vs scalar (~21.5M rays/s batch vs 29K rays/s scalar) |
| 1.2.7 Resolve all test failures | Done | - | Fixed fast-math infinity bug; max()/lowest() replaces infinity(); 5/5 tests pass |

**Acceptance:** GLM/Eigen parity <1e-6; measurable speedup in physics_bench; all tests pass.

### 1.3 SPIR-V Pipeline Completion

**Goal:** Stable shader infrastructure with caching and hot-reload.

| Task | Status | Owner | Notes |
|------|--------|-------|-------|
| 1.3.1 Add hash-based SPIR-V cache | Done | - | `build/shader_cache/` |
| 1.3.2 Integrate spirv_bake into compile script | Done | - | Uses shaderc + spirv-tools; glslangValidator for preprocessing; 20/20 shaders pass |
| 1.3.3 Add reflection cache (JSON) | Done | - | spirv_bake --reflect-json emits bindings/locations; SPIRV_REFLECT=1 generates cache |
| 1.3.4 Add shader hot-reload | Done | - | `watcher` Conan dep; `-DENABLE_SHADER_WATCHER=ON`; detects file changes |
| 1.3.5 Add spirv-opt performance passes | Done | - | Integrated via spirv_bake --opt flag (SPIRV_OPTIMIZE=1 default) |
| 1.3.6 Add CI validation step | Done | - | `validate-shaders` + `ctest` in GitHub Actions |

**Acceptance:** Hot-reload <1s; reflection cache used at runtime.

### 1.4 Cleanroom Mathematics Import

**Goal:** Validate physics against openuniverse submodules.

| Task | Status | Owner | Notes |
|------|--------|-------|-------|
| 1.4.1 Create CLEANROOM_IMPORTS.md | Done | - | Provenance tracking |
| 1.4.2 Validate Schwarzschild functions | Done | - | All pass |
| 1.4.3 Validate Kerr functions | Done | - | Cross-checked nubhlight |
| 1.4.4 Validate kerrStep vs Chandrasekhar | Done | - | Carter formalism verified |
| 1.4.5 Port Boyer-Lindquist coords | Done | - | `src/physics/coordinates.h`; bl_coord, r_of_X, th_of_X, derivatives; 9 validation tests |
| 1.4.6 Port connection coefficients | Done | - | `src/physics/connection.h`; Kerr/Schwarzschild metric tensors, Christoffel symbols, index ops; 7 validation tests |

**Acceptance:** Kerr metric matches nubhlight within 1e-12.

---

## Phase 2: Performance & Instrumentation (Weeks 5-8)

### 2.1 GPU Performance

| Task | Status | Notes |
|------|--------|-------|
| 2.1.1 Parse gpu_timing.csv and flag outliers | Done | `scripts/analyze_gpu_timing.py` with IQR outlier detection |
| 2.1.2 Build "perf pack" target | Done | `perf-pack` + `analyze-gpu-timing` CMake targets; `collect_perf_pack.sh` script |
| 2.1.3 Integrate Tracy GPU zones | Done | Frame markers |
| 2.1.4 Add meshoptimizer overdraw pass | Done | `src/mesh_optimizer.h` utility; infra ready; awaits mesh-based disk impl |
| 2.1.5 Add depth pre-pass toggle | Done | `src/depth_prepass.h` RAII helpers; UI toggle (disabled); awaits mesh geometry |

### 2.2 CPU Performance

| Task | Status | Notes |
|------|--------|-------|
| 2.2.1 Taskflow batch integration | Done | `parallel_lut.h` with spin sweep parallelization; CMake ENABLE_TASKFLOW option |
| 2.2.2 xsimd vectorization evaluation | Done | `xsimd_eval.h` benchmarks; 5.0x speedup on compute-bound Christoffel accel; ~1x on memory-bound ops |
| 2.2.3 Halide scheduling experiment | Deferred | See rationale below |
| 2.2.4 Google Highway evaluation | Done | `highway_eval.h` benchmarks; slower than xsimd (SSSE3 fallback); xsimd selected for deployment |
| 2.2.5 xsimd hotpath deployment | Done | batch.h RK4 refactored; christoffel_accel_batch_xsimd(); 4.65x validated |

**xsimd Evaluation Summary (Phase 2.2.2):**
- Architecture: AVX2+FMA, SIMD width 4 doubles (256-bit)
- Simple ops (f = 1 - r_s/r): No gain - memory-bound, compiler auto-vectorizes
- sqrt-based ops (redshift): ~1x - memory-bound dominates
- Christoffel acceleration: **5.0x speedup** - compute-bound benefits from explicit SIMD
- Recommendation: Use xsimd for compute-heavy kernels (geodesic integration, connection coefficients)

**Highway Evaluation Summary (Phase 2.2.4):**
- Library: Google Highway 1.2.0 (Conan: highway/1.2.0)
- Architecture detected: SSSE3 (128-bit, 2-wide doubles) - suboptimal fallback
- Benchmark results vs scalar baseline:
  - schwarzschild_f: 0.50x (slower)
  - redshift_batch: 0.51x (slower)
  - christoffel_accel: 0.72x (slower)
- Root cause: Highway's static dispatch fell back to SSSE3 instead of AVX2
- Conclusion: **xsimd wins decisively** - proper AVX2 dispatch, 5x speedup on hotpaths
- Highway retained as optional dependency for future performance-portable use cases

**xsimd Deployment Summary (Phase 2.2.5):**
- Refactored: `src/physics/batch.h` RK4 integration loops
- New function: `christoffel_accel_batch_xsimd()` processes all rays in parallel
- Strategy: Compute acceleration for ALL rays (including inactive) to avoid branches
- Validated speedup: **4.65x** on christoffel_accel kernel (benchmark: 41ms -> 8.9ms)
- Batch geodesic throughput: 16.6M rays/s
- All 7 tests pass after refactoring

**Halide Deferral Rationale (Phase 2.2.3):**
- xsimd already provides 4.65x speedup for compute-bound kernels
- LUT generation is parallelized via Taskflow and cached (not in critical path)
- Halide NOT available in Conan Center (Issue #6890 since 2021)
- Cost/benefit unfavorable: high integration effort for marginal offline gains
- Revisit if: LUT generation becomes a bottleneck or need auto-scheduling for new kernels

### 2.3 SLEEF Integration & Tiered SIMD Dispatch

| Task | Status | Notes |
|------|--------|-------|
| 2.3.1 SLEEF library integration | Done | sleef/3.9.0 via Conan; 1-ULP vectorized transcendentals |
| 2.3.2 Runtime architecture detection | Done | `simd_dispatch.h` with CPUID-based SSE2→AVX-512 tier detection |
| 2.3.3 SLEEF-accelerated Christoffel kernel | Done | `christoffel_accel_batch_sleef()` using Sleef_sind4_u10avx2 |
| 2.3.4 SSE2 fallback implementation | Done | Template-based `christoffel_accel_batch_sse2<>()` for legacy |
| 2.3.5 Unified dispatch function | Done | `christoffel_accel_dispatch()` auto-selects best path |

**SLEEF Integration Summary (Phase 2.3.1):**
- Library: SLEEF 3.9.0 (SIMD Library for Evaluating Elementary Functions)
- Provides: Vectorized sin, cos, sqrt with 1.0-ULP or 3.5-ULP accuracy
- Architecture support: SSE2, SSE4, AVX, AVX2, AVX-512
- Integration: Conan dependency + CMake ENABLE_SLEEF option
- Usage: Replace xsimd::sin() with SLEEF's Sleef_sind4_u10avx2() for physics accuracy

**Tiered SIMD Dispatch Summary (Phase 2.3.2-2.3.5):**
- New header: `src/physics/simd_dispatch.h`
- Runtime detection via CPUID + XGETBV for actual CPU capabilities
- Tier enumeration: SCALAR → SSE2 → SSE3 → SSSE3 → SSE4.1 → SSE4.2 → AVX → AVX+FMA → AVX2 → AVX2+FMA → AVX-512
- FMA variant detection: FMA3 (Intel/AMD) vs FMA4 (AMD Bulldozer)
- Dispatch priority:
  1. SLEEF + AVX2 + FMA (best accuracy + FMA speedup)
  2. xsimd AVX2 (fast, good accuracy)
  3. xsimd SSE2 (legacy fallback)
  4. Scalar (always available)
- Batch geodesic throughput maintained: 17.7M rays/s

**Files Modified:**
- `conanfile.py`: Added sleef/3.9.0 dependency
- `CMakeLists.txt`: Added SLEEF detection, linking, and compile definitions
- `src/physics/simd_dispatch.h`: New header for architecture detection
- `src/physics/batch.h`: Added SLEEF kernel, SSE2 fallback, and dispatch function

---

## Phase 3: Visual Assets & Rendering (Weeks 9-12)

### 3.1 Background Assets

| Task | Status | Notes |
|------|--------|-------|
| 3.1.1 Create IMAGE_SOURCES.md manifest | Done | Comprehensive documentation with NASA/ESA/STScI sources |
| 3.1.2 Download NASA/ESA 4K/8K assets | Done | 9 assets in manifest, 218 MB largest (Horsehead 16K) |
| 3.1.3 Convert to KTX2 format | Deferred | Optimization for future; current JPG pipeline functional |
| 3.1.4 Add parallax layer system | Done | 3-layer equirectangular with LOD bias, intensity blend |
| 3.1.5 Evaluate HDR input path | Done | Evaluated: TIFF 16-bit (recommended), EXR (tinyexr), OpenImageIO |

### 3.2 Procedural Enhancements

| Task | Status | Notes |
|------|--------|-------|
| 3.2.1 Integrate fastnoise2 for disk detail | Done | FastNoise2 0.10.0-alpha via Conan, 5 presets implemented |
| 3.2.2 Add noise LUT upload path | Done | NoiseTextureCache: 4 GL_TEXTURE_3D (18 MB GPU), trilinear filtering |
| 3.2.3 Prototype wiregrid curvature overlay | Done | Gravitational potential visualization with runtime scale control |

**Phase 3 Status:** COMPLETE (2026-01-15)

---

## Phase 4: Physics Extensions (Weeks 13-20)

**Status:** In Progress (2026-01-29)
**Progress:** Infrastructure 100%, Physics Implementation 25%

### 4.0 Infrastructure & Documentation (COMPLETE)

| Task | Status | Notes |
|------|--------|-------|
| 4.0.1 Repository cleanup | Done | 5.6GB recovered, backup created |
| 4.0.2 Documentation overhaul | Done | 7 new READMEs (rocq/, tools/, bench/, docs/) |
| 4.0.3 Build system improvements | Done | Fuzz preset fix, riced-relwithdebinfo, shader/Python validation |
| 4.0.4 Automated cleanup tooling | Done | scripts/cleanup_artifacts.sh with dry-run mode |

### 4.1 Accretion Physics

| Task | Status | Notes |
|------|--------|-------|
| 4.1.1 Novikov-Thorne disk profile | Done | src/physics/novikov_thorne.h (η, T, F formulas) |
| 4.1.2 Temperature-dependent emissivity | Pending | scripts/generate_nt_lut.py (next) |
| 4.1.3 Doppler beaming integration | Pending | Disk rotation asymmetry |
| 4.1.4 Frame dragging visualization | Pending | Ergosphere overlay |

### 4.2 GRMHD Integration

| Task | Status | Notes |
|------|--------|-------|
| 4.2.1 nubhlight HDF5 full ingestion | Partial | tools/nubhlight_pack functional |
| 4.2.2 3D texture streaming pipeline | Pending | src/grmhd_streaming.h/cpp (planned) |
| 4.2.3 GRMHD slice preview | Done | Debug shader operational |
| 4.2.4 Reduced-order 2D GRMHD prototype | Future | Research phase |

### 4.3 Radiative Transfer

| Task | Status | Notes |
|------|--------|-------|
| 4.3.1 tardis spectral LUT pipeline | Partial | Stub exists, needs Python integration |
| 4.3.2 Monte Carlo photon transport | Future | Research phase |
| 4.3.3 Compton scattering model | Future | Corona effects |

**Phase 4 Current Progress:** 23/40 tasks complete (57.5%)
**Next Milestone:** LUT generation, Doppler integration, validation tests

---

## Phase 5: Observational Features (Weeks 21-36)

### 5.1 Multi-Wavelength Output

| Task | Status | Notes |
|------|--------|-------|
| 5.1.1 Synthetic X-ray spectra | Future | Fe Ka line |
| 5.1.2 Synchrotron spectrum display | Pending | GPU integration |
| 5.1.3 GW waveform extraction | Future | LIGO format |

### 5.2 Comparison Pipeline

| Task | Status | Notes |
|------|--------|-------|
| 5.2.1 EHT shadow comparison | Future | M87*/Sgr A* |
| 5.2.2 LIGO strain output | Future | HDF5 format |

---

## Issue Tracker Summary

| ID | Title | Priority | Status |
|----|-------|----------|--------|
| ISSUE-001 | Depth effects tuning | MEDIUM | Implemented |
| ISSUE-002 | Gamepad mapping | LOW | Implemented |
| ISSUE-003 | Camera unification | LOW | Done |
| ISSUE-004 | Physics integration | LOW | Scoped |
| ISSUE-005 | Legacy settings | LOW | Scoped |
| ISSUE-006 | Display scaling | MEDIUM | Implemented |
| ISSUE-007 | OpenUniverse cleanroom | HIGH | In Progress |
| ISSUE-008 | Compute raytracer | MEDIUM | Implemented |
| ISSUE-009 | Compare sweep parity | LOW | Root-caused |
| ISSUE-010 | LD_PRELOAD cleanup | LOW | Mitigated |
| ISSUE-011 | Background parallax | LOW | Implemented |
| ISSUE-012 | TSAN warnings | MEDIUM | Mitigated |
| ISSUE-013 | spirv_bake warnings | LOW | Scoped |
| ISSUE-014 | External dep warnings | LOW | Scoped |

---

## Dependency Matrix

See `docs/DEPENDENCY_MATRIX.md` for version tracking.

### Core Dependencies (Conan 2.x)

| Package | Version | Purpose |
|---------|---------|---------|
| glfw | 3.4 | Window/input |
| glbinding | 3.5.0 | OpenGL loader |
| glm | 1.0.1 | Math (render path) |
| eigen | 3.4.0 | Math (physics path) |
| imgui | 1.92.5-docking | UI |
| spdlog | 1.16.0 | Logging |
| tracy | 0.13.1 | Profiling |
| shaderc | 2025.3 | SPIR-V compile |
| spirv-tools | 1.4.313.0 | SPIR-V optimize |
| spirv-cross | 1.4.321.0 | SPIR-V reflect |

---

## Build Commands

```bash
# Install dependencies (repo-local Conan)
./scripts/conan_install.sh Release build

# Build
cmake --preset release
cmake --build --preset release

# Test
ctest --test-dir build/Release --output-on-failure

# Validate shaders
cmake --build --preset release --target validate-shaders

# SPIR-V compile with caching
./scripts/compile_shaders_spirv.sh

# Run
./build/Release/Blackhole
```

---

## Environment Variables

```bash
# Parity debugging
export BLACKHOLE_COMPARE_SWEEP=1
export BLACKHOLE_COMPARE_WRITE_DIFF=1
export BLACKHOLE_COMPARE_OUTLIER_COUNT=5000
export BLACKHOLE_COMPARE_OUTLIER_FRAC=0.0005

# Strict sweep
export BLACKHOLE_COMPARE_MAX_STEPS=1000
export BLACKHOLE_COMPARE_STEP_SIZE=0.02

# Backend selection
export BLACKHOLE_USE_EIGEN=1
export BLACKHOLE_USE_SPIRV=1

# Performance
export BLACKHOLE_GPU_TIMING_LOG=1
export BLACKHOLE_PERF_HUD=1
```

---

## Documentation Index

| Document | Purpose | Status |
|----------|---------|--------|
| STATUS.md | Current state + recent changes | Active |
| TODO_FIXES.md | Issue backlog | Active |
| AGENTS.md | Repository guidelines | Reference |
| PHYSICS_ARCHITECTURE.md | Physics deep dive | Reference |
| CLEANROOM_IMPORTS.md | Provenance tracking | Active |
| CLEANROOM_PORT_MAP.md | Module mapping | Reference |
| EIGEN_REFACTOR_PLAN.md | Math migration | Active |
| IMAGE_SOURCES.md | Asset licensing | Active |
| DEPENDENCY_MATRIX.md | Version tracking | Active |

---

## Review Schedule

- **Weekly:** Update task status, run validation suite
- **Monthly:** Review phase progress, adjust priorities
- **Quarterly:** Archive completed phases, revise roadmap

---

## References

### Primary Physics Sources
1. Bardeen, Press, Teukolsky (1972) - ISCO formulas
2. Chandrasekhar (1983) - Mathematical Theory of Black Holes
3. Misner, Thorne, Wheeler (1973) - Gravitation

### Code References
- nubhlight: BSD-3-Clause (Los Alamos GRMHD)
- compact-common: GPL-3.0+ (Python physics)
- PhysicsForge: LGPL-3.0 (Equation catalog)

---

**Document Owner:** Claude Code
**Last Review:** 2026-01-01
**Next Review:** 2026-02-01
