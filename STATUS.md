# Blackhole Simulation - Development Status

**Last Updated:** 2026-01-02
**Status:** Phase 10.1 (Hawking Radiation Thermal Glow) COMPLETE - Ready for visual testing
**Roadmap:** See `docs/MASTER_ROADMAP.md` for the consolidated execution plan

---

## Executive Summary

The black hole simulation renders correctly with:
- Schwarzschild geodesic ray tracing
- Accretion disk with procedural noise
- 8-level bloom post-processing
- ACES tonemapping
- Optional LUT-backed emissivity/redshift shading (runtime or assets/luts)
- GPU timing panel with fragment/compute split (GL_TIME_ELAPSED queries)
- Runtime shader compile/link logs are emitted (warnings non-fatal)
- OpenGL-native controls overlay (stb_easy_font) renders when UI is hidden (env: `BLACKHOLE_OPENGL_CONTROLS=0`)
- Conan update candidates documented in `requirements.md` (Dec 30 2025 review)
- Latest dependency bump validated: `ctest` (physics_validation + grmhd_pack_fixture) passed; Release build + validate-shaders succeeded; z3 built with GCC 15 warnings (kept non-fatal)

**Current Focus:** See **Active Plans** below for prioritized execution.

---

## Current State (Merged from TODO_FIXES)

The simulation is fully operational with the core rendering pipeline:
- Black hole ray tracing with Schwarzschild geodesics
- Accretion disk with procedural noise
- Bloom post-processing (8-level pyramid)
- ACES tonemapping with gamma correction
- ImGui controls panel
- Optional LUT-backed emissivity/redshift shading (runtime or assets/luts)
- Compute raytracer path (experimental toggle)
- TODO/FIXME scan: ImGui backend TODO/FIXME notes + a new stub TODO in `src/rmlui_overlay.cpp` (RmlUi integration)

## Recent Changes

### Phase 10.1: Hawking Radiation Thermal Glow (2026-01-02) ✅ COMPLETE

**Implementation**: GPU-accelerated Hawking radiation thermal glow visualization
- **New Files**: 10 source files (1,673 lines total)
- **Modified Files**: 4 existing files (+225 lines)
- **Test Coverage**: 13 unit tests (100% pass rate)
- **LUT Data**: 768 precomputed samples (512 temperature + 256 spectrum)

**Key Components**:
- `scripts/generate_hawking_lut.py` - LUT generation (200 lines)
- `shader/include/hawking_luts.glsl` - GLSL sampling utilities (200+ lines)
- `shader/hawking_glow.glsl` - Thermal glow shader (234 lines)
- `src/physics/hawking_renderer.{h,cpp}` - C++ GPU interface (599 lines)
- `tests/hawking_glow_test.cpp` - Physics validation (170 lines)
- `tests/hawking_spectrum_test.cpp` - Spectrum validation (270 lines)

**Physics Validation**:
- Solar mass temperature: 6.17×10⁻⁸ K (±0.4% accuracy) ✓
- Inverse mass law: T_H ∝ 1/M (exact) ✓
- Wien's displacement: λ_peak × T = 0.2898 cm·K (exact) ✓
- Stefan-Boltzmann: L ∝ T⁴ (0.001% accuracy) ✓

**Visualization Presets**:
1. Physical (T_scale=1.0) - Realistic but invisible for solar mass
2. Primordial (T_scale=1e6) - Hot BH with blue-white X-ray glow
3. Extreme (T_scale=1e9) - Maximum visibility for education

**UI Integration**: ImGui controls in `src/main.cpp`
- Enable/disable checkbox
- Preset selector (Physical/Primordial/Extreme)
- Temperature scale slider (logarithmic, 1.0–1×10⁹)
- Intensity slider (0.0–5.0)
- LUT toggle (precomputed vs direct calculation)

**Build System**: CMakeLists.txt updated with test targets
- `hawking_glow_test`: 5/5 tests PASSED
- `hawking_spectrum_test`: 8/8 tests PASSED
- Main executable builds successfully with zero warnings

**Documentation**:
- `docs/PHASE10_TESTING_GUIDE.md` - Manual testing procedures
- `docs/PHASE10.1_COMPLETE.md` - Implementation completion summary

**Status**: ✅ All implementation complete, ready for visual testing
**Next**: Visual validation with 3 presets + GPU performance benchmarking

---

### Earlier Changes (2026-01-01)

- Created `docs/MASTER_ROADMAP.md` consolidating all planning documents into single source of truth.
- Created `docs/DEPENDENCY_MATRIX.md` for centralized version tracking of 34 Conan packages.
- Archived superseded planning docs to `docs/archive/2026Q1/`.
- **ISSUE-009 (Compute/Fragment Parity):** Updated default outlier tolerance in `src/main.cpp`:
  - `compareMaxOutliers`: 0 → 10000 (enables gating by default)
  - `compareMaxOutlierFrac`: 0.0 → 0.006 (0.6% tolerance for Kerr divergence)
  - UI slider ranges expanded to accommodate new defaults
  - All 5 tests pass, 20/20 shaders validated with new tolerances.
- Updated MASTER_ROADMAP.md task 1.1.5 to Done status.
- **Phase 1.2 (Eigen Migration):**
  - Extended `src/physics/math_types.h` with double-precision Eigen types (Vec2d/Vec3d/Vec4d/Mat3d/Mat4d).
  - Added unified vector operations: `math::dot()`, `math::cross()`, `math::length()`, `math::normalize()`.
  - Added conversion helpers: `math::toVec3d()`, `math::toArray3()` for legacy compatibility.
  - Added ENABLE_NATIVE_ARCH CMake option for `-march=native` optimization.
  - Added Eigen-specific SIMD configuration (EIGEN_VECTORIZE_SSE4_2/AVX2/FMA).
  - Updated MASTER_ROADMAP.md task 1.2.5 to Done status.
- **Comprehensive SIMD Detection System:**
  - Replaced compiler-flag-based SIMD detection with actual CPU feature detection via CPUID.
  - AUTO tier selection now uses runtime CPU capability tests (not just compiler support).
  - Detects SSE through AVX-512 with proper OS XGETBV checks for AVX state support.
  - Hierarchical tier application ensures higher tiers include all predecessor instructions.
  - GLM and Eigen SIMD definitions now use `CPU_HAS_*` checks for safety.
  - Cross-compilation falls back to conservative SSE2 baseline.
  - SIMD_TIER cache variable allows explicit override: AUTO, SSE2, SSE4, AVX, AVX2, AVX512.
  - Validates correctly on AMD Ryzen 5 5600X3D (AVX2+FMA detected, AVX-512 correctly rejected).
- **Batch Geodesic API (Phase 1.2.4):**
  - Added `traceGeodesicBatch()` to `src/physics/batch.h` for vectorized geodesic tracing.
  - Structure-of-Arrays (SoA) layout for SIMD-friendly memory access.
  - RK4 integration of Schwarzschild geodesic equations with Christoffel symbols.
  - Eigen path uses `Eigen::Map<VectorXd>` to wrap std::vector data for vectorized ops.
  - Scalar fallback for non-Eigen builds.
  - Returns `BatchTraceResult` with final positions, redshift, status, and step counts.
- **Batch Geodesic Benchmark (Phase 1.2.6):**
  - Added "Batch geodesic (SIMD)" benchmark to `bench/physics_bench.cpp`.
  - Benchmarks `traceGeodesicBatch()` with same ray/step parameters as scalar Schwarzschild.
  - Results: ~21.5M rays/sec (batch) vs ~29K rays/sec (scalar) = 735x speedup.
  - Validates SIMD vectorization effectiveness of batch API.
  - Phase 1.2 Eigen Migration acceptance criteria met: measurable speedup in physics_bench.
- **spirv_bake Integration (Phase 1.3.2 + 1.3.5):**
  - Updated `scripts/compile_shaders_spirv.sh` to use spirv_bake for compilation.
  - Uses shaderc for GLSL->SPIR-V, spirv-tools for optimization.
  - glslangValidator retained for preprocessing (include resolution).
  - Automatic fallback to glslangValidator-only if spirv_bake not found.
  - Environment controls: SPIRV_OPTIMIZE=1 (default), SPIRV_STRIP=0, SPIRV_REFLECT=0.
  - All 20 shaders compile and validate successfully.
  - Summary shows backend, optimization, and strip status.
- **Fast-Math Infinity Bug Fix (Phase 1.2.7):**
  - Root cause: `-ffinite-math-only` flag (part of fast-math) makes `std::numeric_limits<T>::infinity()` return 0.
  - Fix: Replaced `infinity()` with `max()` and `-infinity()` with `lowest()` for min/max initialization.
  - Applied to: `tools/nubhlight_pack.cpp`, `src/grmhd_packed_loader.cpp`, `tests/grmhd_pack_test.cpp`.
  - Result: All 5 tests pass (100%), grmhd_pack_fixture now validates correctly.
  - Phase 1.2 Eigen Migration acceptance criteria fully met.
- **Shader Reflection Cache (Phase 1.3.3):**
  - Added `--reflect-json <path>` option to `tools/spirv_bake.cpp` for JSON reflection output.
  - Uses spirv-cross to extract bindings, locations, and resource metadata.
  - Updated `scripts/compile_shaders_spirv.sh` to emit JSON when `SPIRV_REFLECT=1`.
  - Generates `build/shader_cache/<shader>-reflect.json` for each compiled shader.
  - JSON schema includes: entry_points, sampled_images, uniform_buffers, stage_inputs/outputs.
  - All 20 shaders generate valid reflection JSON with binding/location data.
- **Boyer-Lindquist Coordinate Utilities (Phase 1.4.5):**
  - Created `src/physics/coordinates.h` with cleanroom MKS-to-BL coordinate transforms.
  - Implements: `bl_coord()`, `r_of_X()`, `th_of_X()`, `X_of_r()`, `dr_dX1()`, `dth_dX2()`.
  - Supports theta derefining parameter (hslope): 0=max derefining, 1=uniform spacing.
  - Added Cartesian<->spherical conversion utilities.
  - Created `tests/coordinates_test.cpp` with 9 validation tests covering:
    - Radial coordinate roundtrip and derivatives
    - Theta mapping, derefining behavior, and derivatives
    - Full bl_coord transformation
    - Cartesian<->spherical roundtrip and polar edge cases
  - All project tests pass.
- **Connection Coefficients (Phase 1.4.6):**
  - Created `src/physics/connection.h` with cleanroom Christoffel symbol implementations.
  - Implements Kerr metric tensors: `kerr_gcov()`, `kerr_gcon()`.
  - Implements Schwarzschild metric tensors: `schwarzschild_gcov()`, `schwarzschild_gcon()`.
  - Implements Christoffel symbols: `kerr_connection()`, `schwarzschild_connection()`.
  - Implements index operations: `lower_index()`, `raise_index()`, `geodesic_acceleration()`.
  - Created `tests/connection_test.cpp` with 7 validation tests covering:
    - Metric tensor symmetry (g_uv = g_vu)
    - Metric inverse property (g^ua g_av = delta^u_v)
    - Connection symmetry (Gamma^a_uv = Gamma^a_vu)
    - Schwarzschild limit (Kerr with a=0 matches Schwarzschild)
    - Schwarzschild component sign verification
    - Index raising/lowering roundtrip
    - Geodesic acceleration sign correctness
  - All 7 project tests pass (100%).
- **FP Precision Testing (Phase 1.1.3):**
  - Added `SPIRV_SKIP_OPT_COMPUTE` flag to `scripts/compile_shaders_spirv.sh`.
  - When enabled, skips SPIR-V optimization passes for compute shaders only.
  - Shader size impact: geodesic_trace.comp 52k (unopt) -> 27k (opt) = 48% reduction.
  - Documented testing procedure in `docs/COMPARE_SWEEP.md`.
  - Enables comparison of optimized vs unoptimized FP precision.
- **Shader Hot-Reload Watcher (Phase 1.3.4):**
  - Created `src/shader_watcher.h/cpp` using `watcher` Conan dependency (v0.14.1).
  - Enable with CMake flag: `-DENABLE_SHADER_WATCHER=ON`.
  - Watches `shader/` directory for .vert/.frag/.comp/.geom/.tesc/.tese/.glsl changes.
  - Debounced event handling (100ms) to avoid rapid-fire detection during edits.
  - Logs changed shader paths to stdout for hot-reload triggering.
  - Thread-safe polling API: `hasPendingReloads()`, `pollChangedShaders()`, `clearPendingReloads()`.
  - Graceful start/stop with singleton pattern matching ShaderManager.
- **CI Validation Step (Phase 1.3.6):**
  - Updated `.github/workflows/ci.yml` with comprehensive validation.
  - Installs `glslang-tools` for shader validation.
  - Build step followed by `validate-shaders` target (20/20 shaders).
  - Runs `ctest --output-on-failure` for all 7 physics/validation tests.
  - CI now validates both shader syntax and physics correctness.
- **Raytracer Vec3d Migration (Phase 1.2.3):**
  - Migrated `src/physics/raytracer.h` from `std::array<double, N>` to `math::Vec3d`/`math::Vec2d`.
  - `PhotonRay` struct: position/direction now use `math::Vec3d`.
  - `RayTraceResult` struct: final_position and path now use `math::Vec3d`.
  - `compute_shadow()` return type: `std::vector<math::Vec2d>`.
  - `Camera` struct: position/look_at now use `math::Vec3d`.
  - `Camera::generate_ray()` rewritten using unified math ops: `math::cross()`, `math::length()`, `math::normalize()`.
  - All 7 tests pass; Phase 1.2 Eigen Migration complete.

## Recent Changes (2025-12-31)

- Updated `AGENTS.md` to emphasize repo-local Conan usage.
- Centralized Conan env setup by sourcing `scripts/conan_env.sh` in Conan helper scripts (repo-local `.conan` enforced).
- Refreshed Conan center2 config, reran `conan install`, and rebuilt Release.
- Pinned the repo-local Conan default profile to clang + C++23, enforced compiler executables, and reran `conan install` under clang.
- `validate-shaders` and `ctest` (physics_validation, grmhd_pack_fixture, precision_regression)
  pass cleanly.
- Conan reported deprecated 1.x metadata fields in several upstream recipes (non-fatal; monitor for Conan 2 cleanup).
- Resolved `glActiveTexture` texture-unit warnings in `src/main.cpp`.
- Unified input time-scale handling (keyboard/mouse/gamepad) in `src/input.cpp`.
- Added a gamepad mapping reset button and deadzone monitor tied to current mappings.
- Added control presets (Balanced/Precision/Fast) for sensitivity + time scale tuning.
- Kerr raytracer now routes through the `Kerr` helper for potentials/stepping.
- Kerr Mino-time step now uses RK4 integration for improved stability (CPU path).
- Compute shader now uses emissivity LUT as the primary flux source when enabled.
- Added `ENABLE_ENZYME` CMake flag + toolchain path hints for optional Enzyme integration.
- Added GRB modulation LUT loading and shader bindings (fragment + compute).
- Compare summary CSV now records GRB modulation state and time.
- Radiative transfer LUT plan updated with runtime metadata contract.
- OpenUniverse scope note updated for Kerr RK4 step (no longer placeholder).
- GRMHD ingestion plan now includes nubhlight header + full-dump dataset key list.
- Fixed unused LUT helper to pass compact-common refs into ISCO resolution (`scripts/generate_luts.py`).
- Generated GRB modulation LUT assets (`assets/luts/grb_modulation_lut.csv`, `assets/luts/grb_modulation_meta.json`).
- Depth cues defaults tuned for brighter baseline (fog/dof/desat/curve adjustments).
- Persisted background parallax/drift settings and added per-layer LOD bias controls; background
  sampling now uses explicit mip bias to stabilize layer LODs in fragment/compute.
- Added `BLACKHOLE_LUT_ASSET_ONLY=1` to skip generated LUT fallback for cleanroom parity checks.
- Perf HUD now includes window/render resolution + vsync status lines.
- Added Halide feasibility note for optional CPU-kernel scheduling (`docs/HALIDE_FEASIBILITY.md`).
- Added `src/physics/math_types.h` to start Eigen/GLM type boundary.
- Added riced/coverage/profile CMake presets plus profiling/coverage flags and a gcovr coverage-report target for instrumented builds.

## Recent Changes (2025-12-30)

- Synced ImGui GLFW/OpenGL3 backends to 1.92.5-docking.
- Vendored ImPlot from upstream master (0.18 WIP) due to ImGui 1.92 API changes; added `scripts/fetch_implot.sh`.
- Added ImPlot frame-time graphs to the Performance panel.
- Added ImGuizmo scaffold (Gizmo panel + focus target offset) for camera tooling.
- Added optional RmlUi overlay stub (`ENABLE_RMLUI=ON`) for MangoHUD port groundwork.
- Added frame-time CSV export for ImPlot history (`logs/perf/frame_times.csv`).
- Confirmed GLFW hints request OpenGL 4.6 core + debug context; DSA usage remains bind-based for now.
- Added ultrawide render-scale presets (3440x1440, 5120x2160) in the Display panel.
- Added `src/physics/math_interop.h` for guarded GLM/Eigen conversions (no runtime use yet).
- Expanded `docs/CLEANROOM_PORT_MAP.md` with openuniverse-common validation/types adapter notes.
- Added optional Tracy hooks (`ENABLE_TRACY=ON`) with frame-level plots for CPU/GPU timings.
- Shader validation (`validate-shaders`) passes cleanly (no warnings).
- Added `nubhlight_inspect` tool to emit HDF5 dataset metadata for GRMHD ingestion.
- Added `nubhlight_pack` tool to pack GRMHD channels into RGBA texture blobs + metadata JSON.
- Added packed texture schema proposal and `nubhlight_pack` metadata example to `docs/GRMHD_INGESTION_PLAN.md`.
- Added `src/grmhd_packed_loader.*` to parse packed metadata and upload RGBA 3D textures.
- Added GRMHD packed texture uniforms + sampler path in `shader/blackhole_main.frag` and ImGui
  controls/bindings in `src/main.cpp`.
- Added GRMHD slice preview shader (`shader/grmhd_slice.frag`) and ImGui debug view for
  3D texture inspection.
- Added checksum + min/max validation in `src/grmhd_packed_loader.*` and checksum emission in
  `tools/nubhlight_pack.cpp`.
- Added `tests/grmhd_pack_test.cpp` fixture test that generates a tiny HDF5 dump, packs it, and
  validates loader metadata via CTest.
- Added `scripts/generate_tardis_lut_stub.py` to emit mock spectral LUTs and metadata.
- Added spectral LUT loader + shader hook (`spectralLUT` uniforms) with ImGui controls.
- Extended `bench/physics_bench.cpp` with optional GPU compute timing and CSV/JSON fields.
- Added Tracy zones for major passes (fragment, compute, bloom, tonemap, depth, GRMHD slice).
- Added tiled compute dispatch support for the geodesic compute path (`tileOffset` uniform).
- Expanded LUT pipeline scripts with compact-common metadata and optional spin radii LUT output.
- Conan install completed with CMake 3.31; Release build + validate-shaders + ctest (physics_validation, grmhd_pack_fixture) succeeded.
- Added a local `rmlui/4.4` Conan recipe with `CMAKE_POLICY_VERSION_MINIMUM` fix for modern CMake.
- Aligned Conan output layout to `build/Release` and removed duplicate `conan-release` preset collisions.
- Upgraded Conan pins to latest center2 versions (core + UI), with Eigen deferred; GLM now tracks cci.20230113.
- Verified latest conancenter versions via `conan list`; reran `conan install` + Release build + ctest with repo-local `.conan` config.
- Bumped local recipes to Tracy 0.13.1 and RmlUi 6.1 (latest upstream tags); updated Conan export script and requirements.
- Added FetchContent options for ImNodes, autodiff, and AMReX (`ENABLE_IMNODES`, `ENABLE_AUTODIFF`, `ENABLE_AMREX`).
- Extended `bench/physics_bench.cpp` CSV/JSON output with warmup + GPU elapsed ns fields.
- Added GRMHD slice GPU timer and expanded perf CSV/plot outputs for depth + GRMHD.
- Verified MPFR/GMP precision regression test builds and passes with `-DENABLE_PRECISION_TESTS=ON`.
- Expanded `tools/z3_sanity.cpp` with a redshift constraint check; builds and runs under `-DENABLE_Z3=ON`.
- Reviewed `~/Documents/Formal_Methods_Documentation/theorem_solvers_inventory.md`: z3-git 4.15.4 installed, Rocq 9.1 + Agda present; several formal tools missing or blocked by package constraints.
- Added unit-system metadata (CGS) to validation/LUT generators for reproducible assets.
- Added optional Z3 integration (`ENABLE_Z3=ON`) and `z3_sanity` tool target; Z3 builds with GCC 15 warnings (non-fatal).
- Added optional GMP/MPFR dependencies (ground-truth precision baselines for multiprecision tests).
- Added `scripts/generate_grb_luts.py` (JetFit table export) + `scripts/generate_grb_modulation_lut.py` (Gaussian/FRED envelopes).
- Compute shader now samples emissivity/redshift/spectral LUTs and supports a Kerr path (Mino stepping) when `kerrSpin != 0`.
- Fragment shader noise is texture-only; `useNoiseTexture` defaults on (procedural noise removed).
- Added performance HUD overlay (FPS + GPU timings) with env toggles `BLACKHOLE_PERF_HUD` and `BLACKHOLE_PERF_HUD_SCALE`.
- Depth effects default to the Subtle baseline (enabled by default).
- Updated LUT/GRB/Z3/UnitSystem/MangoHUD docs and OpenUniverse scope notes.
- Auto-enabled GPU timing when `BLACKHOLE_GPU_TIMING_LOG=1` is set.
- Fixed CMakeLists clang-tidy checks string and `ENABLE_EIGEN` option quoting (riced builds unblocked).
- Riced/ASan/TSan/Coverage/Profile builds completed with Werror; `validate-shaders` passes.
- Compare sweep rerun: `logs/compare/compare_summary.csv` regenerated with outlier counts/limits (legacy saved as `compare_summary_legacy.csv`); sparse outliers remain (Kerr preset ~0.015% of pixels) but pass under `BLACKHOLE_COMPARE_OUTLIER_FRAC=0.0005`.
- GPU timing captures archived; ASan runs required preloading libasan due to global `LD_PRELOAD` pointing at missing `mklfakeintel`.
- `physics_bench` profile outputs captured to `logs/perf/physics_bench_profile.{csv,json}` (GPU geodesic compute avg ~0.768 ms).
- Flamegraph rerun after perf sysctl relax and lower sample rate: `logs/perf/flamegraph/flamegraph_lowloss_sysctl_20251231_122954.svg` (no sample-loss warning).
- Infer run reports no issues (report: `infer-out/riced/report.html`); `ctest` (5 tests) passed.
- Added askpass helper usage notes in `~/.codex/GUIDANCE.md` and `/etc/codex/GUIDANCE.md`.
- Added `eirikr` to `video`, `input`, and `plugdev` groups (relogin required).
- Added shared interop GLSL includes for raygen + trace and aligned compute/fragment uniforms + frame time via `InteropUniforms`.
- Added compare outlier gating controls + env overrides (`BLACKHOLE_COMPARE_OUTLIER_COUNT`, `BLACKHOLE_COMPARE_OUTLIER_FRAC`) and CSV columns.
- Added `docs/INTEROP_BEST_PRACTICES.md` with compute/fragment parity checklist + sources.
- Added `docs/WIREGRID_BEST_PRACTICES.md` with curvature wiregrid modeling + rendering notes.
- Added optional asset pipeline package candidates (KTX/OpenImageIO/EXR/PNG/JPEG/mesh) to `requirements.md`.
- Shader loader now strips `GL_GOOGLE_include_directive` extension lines at runtime to avoid driver warnings; `adiskNoiseScale` now scales disk noise sampling.
- GPU timing queries now revalidate query objects; `BLACKHOLE_GPU_TIMING_LOG=1` capture appended to `logs/perf/gpu_timing.csv` without GL_INVALID_OPERATION spam.
- Perf sysctl tuned for higher sample rates (`perf_event_paranoid=-1`, `perf_event_max_sample_rate=100000`).
- Flamegraph regenerated via `scripts/run_flamegraph.sh` (latest: `logs/perf/flamegraph/flamegraph_20251231_141348.svg`, `PERF_FREQ=2000`).
- Added compare-only overrides for compute/fragment parity (`BLACKHOLE_COMPARE_MAX_STEPS`, `BLACKHOLE_COMPARE_STEP_SIZE`) plus UI controls.
- Compare sweep with overrides (600 steps, 0.05 step): 9/12 presets exceeded; latest summary at `logs/compare/compare_summary.csv` (previous archive: `logs/archive/20251231_152444/compare`).
- Compare baseline sweep (`BLACKHOLE_COMPARE_BASELINE=1`): 3/12 presets exceeded (idx 0/1/8); summary at `logs/compare/compare_summary.csv` (previous baseline archived to `logs/archive/20251231_154706/compare`, override sweep archived to `logs/archive/20251231_153643/compare`).
- Compare sweep after background LOD bias defaults: 2/12 presets exceeded (idx 0/4); summary at `logs/compare/compare_summary.csv` (archive: `logs/archive/20251231_182443/compare`).
- Strict compare sweep (1000 steps, 0.02 step) now 0/12 exceeded; summary at `logs/compare/compare_summary.csv` (archive: `logs/archive/20251231_183355/compare_strict`).
- Baseline strict sweep rerun (1000 steps, 0.02 step) without outlier gating: 12/12 exceeded
  (max_abs still > 0.02 across presets). Latest rows appended to `logs/compare/compare_summary.csv`.
- Compare sweep now logs interop uniform snapshots to `logs/compare/compare_uniforms.csv` for parity debugging.
- Added `BLACKHOLE_LUT_ASSET_ONLY=1` to skip generated LUT fallback for cleanroom parity checks.
- Added `docs/OPENGL_45_46_SHADER_REPORT.md` with shader pipeline and 4.5 vs 4.6 standardization notes.
- Added optional SPIR-V shader loading via `BLACKHOLE_USE_SPIRV=1` (expects `*.spv` next to GLSL).
- Added `scripts/compile_shaders_spirv.sh` to generate `*.spv` artifacts with glslangValidator.
- Enabled baseline anisotropic filtering on texture and cubemap loads (clamped to 8x).
- Added DrawID probe overlay via `BLACKHOLE_DRAWID_PROBE=1` (multi-draw indirect test path).
- Added multi-draw main pass with per-draw SSBO data and optional indirect-count compute path
  (`BLACKHOLE_MULTIDRAW_MAIN=1`, `BLACKHOLE_MULTIDRAW_INDIRECT_COUNT=1`,
  `BLACKHOLE_MULTIDRAW_OVERLAY=0`).
- Hardened SPIR-V link stability by adding explicit varying locations in key shader stages
  (simple/bloom/tonemap/overlay + drawid passthrough).
- Gated compare sweep (1000 steps, 0.02 step, outlier frac 0.0005 + count 5000): 8/12 exceeded;
  latest rows appended to `logs/compare/compare_summary.csv`.
- Debug overlay sweep (`BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=3`) captured PPMs for presets 0/1/8 at
  `logs/compare/compare_0_{compute,fragment}.ppm`, `logs/compare/compare_1_{compute,fragment}.ppm`,
  `logs/compare/compare_8_{compute,fragment}.ppm` (files overwritten by last sweep).
- GPU timing log capture updated `logs/perf/gpu_timing.csv` (latest frames appended).
- Flamegraph refreshed: `logs/perf/flamegraph/flamegraph_20251231_200432.svg` (physics_bench).
- Riced ASAN/TSAN builds + ctest passed; TSAN build emitted clang-tidy warnings in `src/shader.cpp`
  (include-cleaner + non-const globals + style/perf notes).
- Added SPIR-V tooling option + `spirv_bake` tool (shaderc/spirv-tools/spirv-cross) to Conan/CMake.
- `spirv_bake` now builds against shaderc/spirv-tools OpenGL 4.5 targets; GCC still warns on
  stack usage in `main` (needs cleanup for Werror builds).
- Added `docs/ROADMAP.md` as the consolidated, hypergranular plan; `docs/ROADMAP_NEXT_PHASE.md`
  now points to it.
- Added meshoptimizer/fastnoise2/watcher dependencies (Conan options) and verified pins
  against conancenter; updated `requirements.md`.
- Refreshed SPIR-V tooling pins (spirv-cross 1.4.321.0, spirv-headers stays at
  1.4.313.0 to match spirv-tools/shaderc) and replaced unavailable fast-noise-lite
  with fastnoise2.
- Conan install + Release build completed with new fastnoise2/spirv-cross packages
  (external warnings observed; tracked in TODO_FIXES.md).
- Added optional parallel shader compile (`BLACKHOLE_PARALLEL_SHADER_COMPILE=1`) and
  no-error context (`BLACKHOLE_NO_ERROR_CONTEXT=1`) toggles.
- Updated clang-tidy config to match lowerCamelCase and reduced noisy checks; fixed HUD overlay static usage, include guards, and cppcheck warnings.
- Rerun riced-asan/riced-tsan builds after cleanup; clang-tidy/cppcheck warnings no longer emitted (aside from LD_PRELOAD noise).

## Recent Changes (2025-12-29)

**Controls + Camera Unification**
- Single C++ camera drives all modes (shader consumes `cameraPos` + `cameraBasis`)
- Controls panel restored (sensitivity, inversion, hold-to-toggle, time scale) and key remapping persists
- Gamepad controls added (sticks + triggers) with button bindings + deadzone monitor
- Camera mode + orbit settings persist in `settings.json`

**LUT Pipeline + Validation**
- Added offline LUT generation (`scripts/generate_luts.py`) and asset metadata (`assets/luts/lut_meta.json`)
- Runtime loads LUT assets when present (falls back to CPU LUT generation)
- Added validation asset generator (`scripts/generate_validation_tables.py`) for `assets/validation/`
- Fixed Kerr ISCO retrograde sign and added LUT asset checks in `physics_test`

**Shader Validation**
- `validate-shaders` warns by default; set `ENABLE_WERROR=ON` to fail on warnings
- Runtime shader compile/link warnings are logged but non-fatal (`src/shader.cpp`)

**OpenGL Loader**
- Switched OpenGL loader to glbinding (pure C++ API, no GLEW).
- ImGui backend uses `IMGUI_IMPL_OPENGL_LOADER_CUSTOM` with glbinding; gl3w header is retained but unused.

**Conan Stack**
- Updated must-have dependencies (glbinding + imgui docking + xsimd + EnTT + Taskflow + HighFive + FlatBuffers + spdlog + Tracy + CLI11).

**Compute A/B Compare**
- Compare toggle renders fragment + compute outputs and reports sampled diff metrics
- Snapshot capture dumps PPMs and full-frame diff stats; auto-capture appends `logs/compare/compare_summary.csv`
- GPU timers report fragment vs compute time; preset sweep captures snapshots
- Compute shader uses Schwarzschild RK4 only; Kerr compute path disabled pending cleanroom constants

**Kerr Cleanroom Scaffolding**
- Added C++ Kerr raytracer (Mino-time stepping) and helper constructors
- Extended physics tests with photon-orbit potential and Kerr raytracer sanity checks
- Added spin-radii LUT generator for r_isco/r_ph curves (CPU-side)

**Depth Effects**
- Added a depth-effects pass (fog/edges/desaturation/chroma + optional DoF)
- Depth packed into alpha from the ray tracer; presets + depth curve added
- Defaults tuned heuristically (no visual validation yet)

**Display Scaling**
- Render targets resize to framebuffer size * renderScale
- Display panel exposes fullscreen, swap interval (vsync), and render-scale presets
- Headless display validation deferred until Wayland/X11 support is available

## Active Plans (Merged + Refactored)

- **Performance + math migration:** extend `physics_bench` for new modules; enforce LUT-only emissivity/redshift (move disk noise + emissivity out of shaders into LUTs with a debug fallback); keep compute-vs-fragment A/B; evaluate Eigen/xsimd for SIMD and parallel LUT generation (see `docs/EIGEN_REFACTOR_PLAN.md`).
- **Rendering scaling:** validate window resize in fragment + compute paths; add 720p–4K ultrawide presets; persist fullscreen/vsync/renderScale and gamma/tonemap/bloom.
- **Controls & input ergonomics:** validate keyboard/mouse vs time scale; refine gamepad bindings + deadzone tools; add remap presets; persist inversion/sensitivity/hold-to-toggle.
- **Cleanroom audit:** deep scan OpenUniverse + local repos; map reusable physics/math/data schemas; define pure C++23/GLSL460 ports.
- **GRMHD ingestion:** document nubhlight HDF5 schema, build offline converter, add dataset loader + checksum validation.
- **Radiative transfer + GRB modulation:** define LUT specs from tardis/GRB datasets and add time-domain modulation hooks.
- **HUD port:** MangoHud-style overlay for FPS/frametime + GPU timings with optional CSV export.
- **Dependency review:** scan for updated Conan packages and set Eigen/xsimd/TBB/OpenMP baseline; evaluate autodiff/Enzyme/AMReX adoption; track MPFR/GMP for precision baselines and Halide (non-Conan) for scheduling experiments.

## Issue Tracker

### ISSUE-001: Depth Effects Tuning (Packed Depth)
**Priority:** MEDIUM
**Status:** In progress

#### Current State
The ray tracer now packs a normalized depth value into the alpha channel and a post-process shader
applies fog/edge outlines/desaturation/chroma + optional DoF.
Presets and a depth curve control were added to provide quick tuning baselines.
Defaults updated to a more subtle baseline (depthFar 100, fog start/end 0.5/0.95, lighter desat);
these are heuristic changes pending visual validation.

#### Gaps
- Depth is derived from ray integration and is an approximation.
- No dedicated depth texture or multi-render target support.

#### Next Steps
1. Evaluate depth quality across scenes and tune `depthFar`, fog ranges, and DoF parameters.
2. If needed, add MRT output for a dedicated depth texture.
3. Validation matrix (visual pass):
   - Presets: Subtle, Cinematic, Clarity.
   - Camera modes: Input + Orbit (near/far distances).
   - Resolutions: Native, 720p preset, 4K preset.
   - Content toggles: accretion disk on/off, noise texture on/off, spin 0.0 vs 0.8.

---

### ISSUE-002: Gamepad Mapping Ergonomics
**Priority:** LOW
**Status:** Implemented (needs validation)

#### Current State
- Right stick: yaw/pitch
- Left stick: roll/zoom
- Triggers: zoom in/out (fine adjustment)
- Buttons: reset camera, pause, toggle UI (configurable)
- Deadzone visualization available in Controls panel
- OpenGL controls overlay shows key bindings when UI is hidden

#### Next Steps
1. Validate mapping on common controllers (Xbox/PS).
2. Add optional button remapping UI for presets.

---

### ISSUE-003: Camera System Unification
**Priority:** LOW
**Status:** Done

#### Current State
- Camera position and basis are computed in C++ for all modes (Input/Front/Top/Orbit).
- `shader/blackhole_main.frag` now consumes `cameraPos` + `cameraBasis` only.
- Mouse/time-based camera branches have been removed from GLSL.

#### Follow-up (Optional)
1. Add camera presets (cinematic/diagnostic).

---

### ISSUE-008: Compute Raytracer Path
**Priority:** MEDIUM
**Status:** Implemented (experimental)

#### Current State
- Compute path now supports LUT sampling and Kerr stepping (Mino time) when spin is non-zero.
- Fragment vs compute diff tooling remains available for parity checks.

#### Next Steps
1. Validate compute vs fragment parity on a preset sweep.
2. Tune step size limits for Kerr paths.

---

### ISSUE-004: Physics Integration Incomplete
**Priority:** LOW
**Status:** Scope defined

#### Current State
Physics parameters are computed in C++ and passed correctly:
- Kerr-aware ISCO/photon sphere radii are derived from `kerrSpin` and mapped into shader units.
- LUT-backed emissivity/redshift textures are generated at runtime or loaded from assets/luts (with metadata checks).
- `schwarzschildRadius`, `iscoRadius`, and `photonSphereRadius` are still central to trace.

#### What Works
- Gravitational lensing uses `schwarzschildRadius`
- Accretion disk inner edge uses `iscoRadius`
- Event horizon detection uses `schwarzschildRadius`

#### Potential Improvements (Future)
1. Integrate Kerr geodesic integration path into shader/compute (beyond radii)
2. Add proper Doppler beaming for disk rotation
3. Add frame dragging visualization
4. Add gravitational time dilation indicator

#### Compute Shader Kerr Notes (Current)
- `shader/geodesic_trace.comp` uses a Mino-time stepping model with `KerrConsts` derived from
  `cross(pos, dir)` (Lz) and `L^2 - Lz^2` (Q); this is a simplification vs CPU formulas.
- `kerrSpin` maps to `a = kerrSpin * 0.5 * r_s`, consistent with `a = a* M` where `r_s = 2M`.
- Sign flips occur when `R` or `Theta` go negative; this is heuristic and can hide integrator drift.
- No tetrad-based constants-of-motion yet; compute path is for visual parity only.

#### Status
No immediate fixes needed. Physics integration is functional.

---

### ISSUE-005: Legacy Settings Cleanup
**Priority:** LOW
**Status:** Scope defined

#### Issue
Old `settings.json` files may contain stale fields that are now ignored.

#### Current Behavior
- Unknown fields are silently ignored during load (safe)
- Only current fields are written on save (old fields get cleaned up)

#### Resolution Options
1. **Do nothing** - Fields naturally clean up on next save
2. **Add migration** - Explicitly remove old fields on load
3. **Add version** - Track settings version for future migrations

#### Recommended Approach
Option 1 (do nothing) - the current load/save cycle naturally cleans up old fields.

---

### ISSUE-006: Display Scaling + VSync + Fullscreen
**Priority:** MEDIUM
**Status:** Implemented (validation deferred)

#### Current State
- Render targets resize to framebuffer size * renderScale.
- Display panel controls render scale, fullscreen, and swap interval (0/1/2).
- Render resolution is shown in UI for verification.

#### Gaps
- Needs validation at 720p–4K ultrawide and fullscreen/windowed modes.
- No adaptive scaling or FPS-based auto-scaling yet.

#### Next Steps
1. Validate resize behavior on windowed + fullscreen once headless display is available.
2. Tune default renderScale values after visual testing.

---

### ISSUE-007: OpenUniverse Cleanroom Integration
**Priority:** HIGH
**Status:** Scoped

#### Current State
- Submodule inventory and cleanroom plan documented.
- No code ports executed yet.

#### Next Steps
1. Confirm priority order for submodule cleanroom ports.
2. Implement unit system alignment and reference LUT pipeline.
3. Wire compute shader path and validate against CPU references.

---

### ISSUE-008: Compute Raytracer Path
**Priority:** MEDIUM
**Status:** Implemented (experimental)

#### Current State
- `shader/geodesic_trace.comp` is wired into the render pipeline.
- Compute path writes color + depth into the blackhole render target.
- UI toggle in Black Hole Parameters selects compute vs fragment path.
- Compare mode renders both paths and reports sample diff metrics (CPU readback).
- Snapshot capture can dump PPMs and full-frame diff stats.
- Auto-capture appends batch summaries to `logs/compare/compare_summary.csv`.
- Preset sweep cycles fixed camera modes and triggers snapshots automatically.
- Preset sweep includes Kerr/Schwarzschild pairs for A/B capture.
- Max-diff threshold tracking is exposed in UI and logged per snapshot.
- CPU-side Kerr raytracer scaffold exists for cleanroom parity checks.
- Compute path uses Schwarzschild RK4 only; Kerr compute path disabled pending cleanroom constants.
- Optional GPU timing CSV logging via `BLACKHOLE_GPU_TIMING_LOG`.

#### Gaps
- Kerr constants-of-motion are approximated from flat-space angular momentum; refine mapping
  from camera rays to Kerr constants for higher-fidelity comparisons.
- Needs validation vs fragment path across camera modes and presets.
- No CI gate for A/B diff thresholds yet (manual capture only).

#### Next Steps
1. Compare compute vs fragment output for a set of camera/parameter snapshots.
2. Extend diff to full-frame or golden-image comparisons.

---

## Architecture Notes

### Input Flow (Current)
```
InputManager --> CameraState (yaw/pitch/roll/distance)
     |
     v
main() computes cameraPos + cameraBasis (mode-aware)
     |
     v
blackhole_main.frag consumes cameraPos + cameraBasis
```

### Unit System
- C++ physics code uses CGS units by default (cm, g, s) via `src/physics/constants.h`.
- Geometric units are used only where explicitly stated (e.g., some GW formulas).
- Shader-side LUT sampling uses normalized radii (r/r_s).

### Validation Assets
- `scripts/generate_validation_tables.py` emits `assets/validation/metrics.json` and
  `assets/validation/redshift_curve.csv`.
- `assets/validation/spin_radii_curve.csv` contains r_isco/r_ph vs spin samples.
- `physics_test` compares r_s/r_isco/r_ph + redshift curve against CPU references.

### Camera Uniform Contract
- Fragment path (`shader/blackhole_main.frag`): `cameraPos` (vec3) and `cameraBasis` (mat3) are world-space
  camera position and basis vectors, produced in C++ per camera mode.
- Compute path (`shader/geodesic_trace.comp`): `cameraPosition` (vec3) and `viewMatrix` (mat4) are provided
  by C++; `viewMatrix` contains the rotation basis in its top-left 3x3.

### Key Files

| File | Purpose | Lines |
|------|---------|-------|
| `src/main.cpp` | Entry, render loop, ImGui | 610 |
| `src/input.cpp` | InputManager, camera update | 589 |
| `src/input.h` | CameraState, KeyAction enum | 237 |
| `shader/blackhole_main.frag` | Ray tracing, camera positioning | 471 |

---

## Next Steps (Priority Order)

1. **Tune depth effects** (ISSUE-001)
   - Validate packed depth behavior across scenes
   - Adjust defaults for fog/DoF and add presets if needed

2. **Validate gamepad mapping** (ISSUE-002)
   - Test controller ergonomics and add button bindings

3. **Validate display scaling** (ISSUE-006)
   - Confirm 720p-4K rendering, fullscreen/swap interval toggles

4. **Optional camera follow-ups** (ISSUE-003)
   - Add camera presets (cinematic/diagnostic)

---

## Testing Checklist

After fixes, verify:

- [ ] W/S keys change pitch (view tilts up/down)
- [ ] A/D keys change yaw (view orbits left/right)
- [ ] Q/E keys change distance (zoom in/out)
- [ ] Z/C keys change roll (view tilts sideways)
- [ ] +/- keys zoom in/out
- [ ] Camera mode selection (Input/Front/Top/Orbit) renders expected views
- [ ] Mouse right-drag still works
- [ ] Mouse scroll zoom still works
- [ ] R key resets camera
- [ ] H key toggles UI
- [ ] P key pauses simulation
- [ ] F4/F5 change font size
- [ ] [/] keys change time scale
- [ ] Gamepad sticks + triggers adjust camera
- [ ] Depth effects toggles behave as expected
- [ ] No uniform warnings in console
- [ ] Camera state persists in settings.json

---

## Build Commands

```bash
# Install dependencies (repo-local Conan home)
./scripts/conan_install.sh Release build

# Build
cmake -DCMAKE_BUILD_TYPE=Release -S . -B build/Release \
  -DCMAKE_TOOLCHAIN_FILE=build/Release/generators/conan_toolchain.cmake
cmake --build build/Release

# Run
./build/Release/Blackhole

# Validate shaders
cmake --build build/Release --target validate-shaders
```
