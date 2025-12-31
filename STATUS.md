# Blackhole Simulation - Development Status

**Last Updated:** 2025-12-31
**Status:** Core simulation operational, controls + depth effects integrated, camera unified

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

## Recent Changes (2025-12-31)

- Updated `AGENTS.md` to emphasize repo-local Conan usage.
- Centralized Conan env setup by sourcing `scripts/conan_env.sh` in Conan helper scripts (repo-local `.conan` enforced).
- Refreshed Conan center2 config, reran `conan install`, and rebuilt Release.
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
