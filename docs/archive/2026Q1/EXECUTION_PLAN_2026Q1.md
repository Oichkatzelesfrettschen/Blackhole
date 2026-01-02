# Blackhole Execution Plan - 2026 Q1

**Created:** 2026-01-01
**Scope:** Multi-phase execution covering compute/fragment parity, Eigen migration,
SPIR-V pipeline, visual assets, and cleanroom mathematics import.

## Executive Summary

This plan consolidates all priority work streams into a granular, actionable roadmap.
Build system is verified working (5/5 tests pass, 20/20 shaders validate).

**Priorities (all selected):**
1. Compute/Fragment Parity - Debug Kerr divergence (~0.015% outliers)
2. Eigen Migration - CPU physics performance via SIMD
3. SPIR-V Pipeline - Reflection cache, hot-reload, spirv-opt
4. Visual Assets - NASA/ESA backgrounds, parallax, fastnoise2
5. Cleanroom Mathematics Import - nubhlight, compact-common, PhysicsForge

---

## Phase 1: Compute/Fragment Parity (Priority: HIGH)

**Issue:** ISSUE-009 - 2/12 presets exceeded threshold (idx 0/4) with default settings.
Strict sweep (1000 steps, 0.02 step) shows 0/12 failures. Root-cause needed.

### Root-Cause Analysis

The Kerr geodesic integrator in `shader/include/kerr.glsl` has potential divergence sources:

1. **Sign flipping at turning points** (lines 91-96): When `R < 0` or `Theta < 0`,
   the ray sign flips. Subtle FP differences between compute/fragment dispatch could
   cause different turning point detection timing.

2. **Carter constant approximation** (`kerrInitConsts`): Uses flat-space angular
   momentum to approximate `E`, `Lz`, `Q`. This is an approximation that may
   accumulate differently across shader stages.

3. **Square root of clamped values** (lines 98-99): `sqrt(max(R, 0.0))` and
   `sqrt(max(Theta, 0.0))` can produce different bit-exact results.

### Tasks

| ID | Task | Status | Notes |
|----|------|--------|-------|
| 1.1 | Run compare sweep with `BLACKHOLE_COMPARE_WRITE_DIFF=1` | Pending | Capture diff images for idx 0,4 |
| 1.2 | Add per-pixel debug heatmap output to integrator | Pending | Visualize step count per pixel |
| 1.3 | Add `BH_DEBUG_FLAG_STEP_COUNT` to `interop_trace.glsl` | Pending | Track max steps hit |
| 1.4 | Compare float bit patterns at turning points | Pending | Log sign flips |
| 1.5 | Add compare-only override env var | Pending | `BLACKHOLE_COMPARE_ONLY=1` |
| 1.6 | Test with `fastmath` disabled in compute shader | Pending | Rule out FP contraction |
| 1.7 | Cross-validate kerrStep against nubhlight metric.c | Pending | Cleanroom reference |

### Acceptance Criteria

- [ ] All 12 presets pass with default settings (outlier count = 0)
- [ ] Diff images show no systematic pattern (random noise only)
- [ ] Debug heatmap shows uniform step distribution

---

## Phase 2: Eigen Migration (Priority: MEDIUM)

**Goal:** Move CPU physics to Eigen for SIMD performance per `docs/EIGEN_REFACTOR_PLAN.md`.

### Current State

- `src/physics/math_types.h` defines type boundary (GLM or Eigen via `BLACKHOLE_USE_EIGEN`)
- `src/physics/math_interop.h` provides conversion helpers
- `tests/math_types_parity_test.cpp` validates GLM/Eigen parity

### Tasks

| ID | Task | Status | Notes |
|----|------|--------|-------|
| 2.1 | Enable Eigen by default in math_types.h | Pending | `#define BLACKHOLE_USE_EIGEN 1` |
| 2.2 | Migrate `raytracer.h` to use `physics::Vec3` | Pending | Replace `glm::vec3` |
| 2.3 | Migrate `raytracer.cpp` integrator loops | Pending | Use Eigen vectorization |
| 2.4 | Add batch geodesic evaluation API | Pending | `traceGeodesicBatch(rays, count)` |
| 2.5 | Enable Eigen SIMD flags in CMake | Pending | `-march=native`, `-DEIGEN_USE_SIMD` |
| 2.6 | Run parity tests | Pending | `ctest -R math_types` |
| 2.7 | Benchmark GLM vs Eigen | Pending | `bench/physics_bench.cpp` |

### Acceptance Criteria

- [ ] All tests pass with `BLACKHOLE_USE_EIGEN=1`
- [ ] GLM/Eigen parity within 1e-6 tolerance
- [ ] Measurable speedup in physics_bench (target: 2x for batch ops)

---

## Phase 3: SPIR-V Pipeline Completion (Priority: MEDIUM)

**Goal:** Complete Phase 1 of SPIR-V roadmap from `docs/ROADMAP.md`.

### Current State

- `spirv_bake` tool exists (shaderc + spirv-tools + spirv-cross)
- `scripts/compile_shaders_spirv.sh` generates `.spv` files
- Runtime load via `BLACKHOLE_USE_SPIRV=1`

### Tasks

| ID | Task | Status | Notes |
|----|------|--------|-------|
| 3.1 | Add hash-based SPIR-V cache directory | Pending | `assets/spirv_cache/{hash}.spv` |
| 3.2 | Integrate `spirv_bake` into compile script | Pending | Replace glslc calls |
| 3.3 | Add reflection cache (JSON) | Pending | Bindings + locations |
| 3.4 | Add shader hot-reload with watcher | Pending | `watcher` Conan dep |
| 3.5 | Add `spirv-opt` performance passes | Pending | Dead code elim, loop unroll |
| 3.6 | Add CI step: SPIR-V vs GLSL hash match | Pending | Detect stale binaries |
| 3.7 | Add specialization constants for runtime toggles | Pending | `adiskEnabled`, etc. |

### Acceptance Criteria

- [ ] Hot-reload works: edit GLSL, see change in <1s
- [ ] Reflection cache used at runtime (no `glGetUniformLocation`)
- [ ] SPIR-V binaries match GLSL sources in CI

---

## Phase 4: Visual Assets + Backgrounds (Priority: LOW)

**Goal:** Import NASA/ESA assets, add parallax layers, procedural noise.

### Tasks

| ID | Task | Status | Notes |
|----|------|--------|-------|
| 4.1 | Create `docs/IMAGE_SOURCES.md` manifest | Pending | NASA/ESA license tracking |
| 4.2 | Download Hubble Deep Field 4K/8K | Pending | STScI archive |
| 4.3 | Download Milky Way panorama | Pending | ESO/ESA archive |
| 4.4 | Convert to KTX2 format | Pending | Optional `ktx` Conan dep |
| 4.5 | Add parallax layer system | Pending | Per-layer drift + LOD |
| 4.6 | Integrate fastnoise2 for disk detail | Pending | Already in Conan deps |
| 4.7 | Add noise LUT upload path | Pending | 3D texture cache |
| 4.8 | Add validation screenshots | Pending | Before/after comparison |

### Acceptance Criteria

- [ ] 3 background layers with distinct parallax rates
- [ ] fastnoise2 procedural noise visible in disk
- [ ] Screenshot comparison shows visual improvement

---

## Phase 5: Cleanroom Mathematics Import (Priority: HIGH)

**Goal:** Import and cross-validate mathematics from openuniverse submodules.

### Source Repositories

| Repo | Path | Content |
|------|------|---------|
| nubhlight | `~/Github/openuniverse/nubhlight/core/` | Kerr metric, Boyer-Lindquist coords |
| compact-common | `~/Github/openuniverse/compact-common/` | ISCO, photon sphere, geodesic |
| PhysicsForge | `~/Github/openuniverse/PhysicsForge/` | Equation catalog, constants |
| grb-common | `~/Github/openuniverse/grb-common/` | GRB cosmology, extinction |

### Tasks

| ID | Task | Status | Notes |
|----|------|--------|-------|
| 5.1 | Port Kerr gcov/gcon from nubhlight | Pending | `bl_gcov_func`, `bl_gcon_func` |
| 5.2 | Port Boyer-Lindquist coords | Pending | `bl_coord`, `r_of_X`, `th_of_X` |
| 5.3 | Port connection coefficients | Pending | `conn_func` from metric.c |
| 5.4 | Import ISCO/photon sphere from compact-common | Pending | Python -> C++ |
| 5.5 | Cross-validate against existing implementation | Pending | Tolerance check |
| 5.6 | Add precision ground-truth tests | Pending | Boost.Multiprecision |
| 5.7 | Create `docs/CLEANROOM_IMPORTS.md` | Pending | Provenance tracking |
| 5.8 | Import PhysicsForge equation catalog | Pending | Validation reference |

### Acceptance Criteria

- [ ] Kerr metric matches nubhlight within 1e-12
- [ ] ISCO matches compact-common within 1e-10
- [ ] All imports documented with source + license

---

## Dependencies

```
Phase 1 (Parity) --> Phase 5 (Cleanroom) [reference validation]
Phase 2 (Eigen) --> independent
Phase 3 (SPIR-V) --> independent
Phase 4 (Assets) --> independent
Phase 5 (Cleanroom) --> Phase 1 [Kerr validation]
```

## Timeline

| Week | Focus |
|------|-------|
| W1 | Phase 1.1-1.4 (Parity debug), Phase 5.1-5.3 (Kerr import) |
| W2 | Phase 1.5-1.7 (Parity fixes), Phase 5.4-5.6 (ISCO validation) |
| W3 | Phase 2.1-2.4 (Eigen migration) |
| W4 | Phase 2.5-2.7 (Eigen benchmarks), Phase 3.1-3.3 (SPIR-V cache) |
| W5 | Phase 3.4-3.7 (SPIR-V hot-reload) |
| W6 | Phase 4.1-4.4 (Assets download) |
| W7 | Phase 4.5-4.8 (Parallax + noise) |
| W8 | Integration testing, documentation |

## Environment Variables

```bash
# Parity debugging
export BLACKHOLE_COMPARE_SWEEP=1
export BLACKHOLE_COMPARE_WRITE_DIFF=1
export BLACKHOLE_COMPARE_WRITE_OUTPUTS=1
export BLACKHOLE_COMPARE_OUTLIER_COUNT=0
export BLACKHOLE_COMPARE_OUTLIER_FRAC=0.0

# Strict sweep
export BLACKHOLE_COMPARE_MAX_STEPS=1000
export BLACKHOLE_COMPARE_STEP_SIZE=0.02

# Eigen backend
export BLACKHOLE_USE_EIGEN=1

# SPIR-V runtime
export BLACKHOLE_USE_SPIRV=1
```

## References

- `docs/ROADMAP.md` - Master roadmap
- `docs/EIGEN_REFACTOR_PLAN.md` - Eigen migration strategy
- `docs/OPENGL_45_46_SHADER_REPORT.md` - SPIR-V pipeline notes
- `TODO_FIXES.md` - Issue backlog
- `STATUS.md` - Current development state
