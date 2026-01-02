# Blackhole Roadmap (Hypergranular)

Last updated: 2025-12-31

Scope: this document consolidates the active roadmap into a single, modern plan
with concrete, testable tasks for the OpenGL 4.6 + SPIR-V pipeline, compute/
fragment parity, performance tooling, and asset upgrades.

Legend:
- [ ] pending
- [x] completed
- [~] in progress

## Current TODO (Prioritized Queue)
1. [ ] Verify X11/GUI readiness and document required env vars.
2. [ ] Add Werror Release preset (opt-out flag for local builds).
3. [ ] Add UBSAN preset and document expected failures.
4. [~] Add coverage preset and document reporting workflow.
5. [ ] Enable clang-tidy/cppcheck in a dedicated CI profile.
6. [ ] Clean up `spirv_bake` stack-usage warnings for Werror builds.
7. [ ] Add a fast "smoke test" target for minimal sanity checks.
8. [ ] Add a stable SPIR-V cache directory (hash-based naming).
9. [ ] Integrate `spirv_bake` into `scripts/compile_shaders_spirv.sh`.
10. [ ] Add reflection cache (bindings + locations) for fast runtime lookup.
11. [ ] Add CI step to validate SPIR-V binaries match GLSL sources.
12. [ ] Add `spirv-opt` performance pass config to the bake pipeline.
13. [ ] Define shader specialization constants in SPIR-V for runtime toggles.
14. [ ] Add shader hot-reload path with `watcher` (file change -> recompile).
15. [ ] Add UI signal for shader rebuild failures and fallback path.
16. [ ] Add compare-only override to isolate outlier gating behavior.
17. [ ] Add shader-side NaN/range debug flags in the integrator.
18. [ ] Add per-pixel debug heatmap output for parity sweeps.
19. [ ] Re-sweep parity after debug gating changes and log deltas.
20. [ ] Root-cause analysis for compute/fragment divergence (Kerr presets).
21. [ ] Add regression thresholds tied to LUT metadata + units.
22. [ ] Parse `gpu_timing.csv` and flag outliers in a report.
23. [ ] Document perf sysctl tuning for low-loss sampling.
24. [ ] Build a "perf pack" target that runs GPU timing + flamegraph.
25. [ ] Integrate Tracy capture (GPU zones + frame markers).
26. [ ] Add meshoptimizer overdraw pass for disk geometry.
27. [ ] Add a depth pre-pass toggle for dense disk surfaces.
28. [ ] Import NASA/JPL/ESA assets (2K/4K/8K) and track licenses.
29. [ ] Add parallax expansion with per-layer LOD + drift controls.
30. [ ] Add a curated asset manifest in `docs/IMAGE_SOURCES.md`.
31. [ ] Prototype wiregrid curvature overlay for spacetime visualization.
32. [ ] Evaluate background HDR input path (OpenImageIO/tinyexr).
33. [ ] Add validation screenshots for new backgrounds + parallax.
34. [ ] Consolidate cleanroom decisions and migrations in `docs/CLEANROOM_*`.
35. [ ] Maintain `STATUS.md` + `TODO_FIXES.md` after each milestone.
36. [ ] Add a "release checklist" doc for parity, perf, and visual validation.

## Phase 0: Environment + Build Hardening
1. [ ] Verify X11/GUI readiness and document required env vars.
2. [ ] Add Werror Release preset (opt-out flag for local builds).
3. [x] Add Werror Riced Debug preset (opt-out flag for local builds).
4. [ ] Add UBSAN preset and document expected failures.
5. [~] Add coverage preset and document reporting workflow.
6. [ ] Enable clang-tidy/cppcheck in a dedicated CI profile.
7. [x] Fix clang-tidy warnings in `src/shader.cpp` (TSAN build).
8. [ ] Clean up `spirv_bake` stack-usage warnings for Werror builds.
9. [x] Validate `validate-shaders` target in Release + Riced builds.
10. [ ] Add a fast "smoke test" target for minimal sanity checks.

## Phase 1: SPIR-V Pipeline (Toolchain + Runtime)
11. [x] Add SPIR-V tooling dependencies (shaderc/spirv-tools/spirv-cross).
12. [x] Add `spirv_bake` tool for compile/opt/reflect.
13. [ ] Add a stable SPIR-V cache directory (hash-based naming).
14. [ ] Integrate `spirv_bake` into `scripts/compile_shaders_spirv.sh`.
15. [ ] Add reflection cache (bindings + locations) for fast runtime lookup.
16. [x] Add explicit varying locations in core shader stages.
17. [x] Add SPIR-V runtime load path toggle (`BLACKHOLE_USE_SPIRV=1`).
18. [ ] Add CI step to validate SPIR-V binaries match GLSL sources.
19. [ ] Add `spirv-opt` performance pass config to the bake pipeline.
20. [ ] Define shader specialization constants in SPIR-V for runtime toggles.
21. [ ] Add shader hot-reload path with `watcher` (file change -> recompile).
22. [ ] Add UI signal for shader rebuild failures and fallback path.

## Phase 2: Compute/Fragment Parity and Divergence Debugging
23. [x] Add compute/fragment shared includes for raygen/trace/shade.
24. [x] Add compare sweep overrides for step size/max steps.
25. [x] Add compare outlier gating controls (frac + count).
26. [ ] Add compare-only override to isolate outlier gating behavior.
27. [ ] Add shader-side NaN/range debug flags in the integrator.
28. [x] Run debug overlay sweep for presets 0/1/8.
29. [ ] Add per-pixel debug heatmap output for parity sweeps.
30. [ ] Re-sweep parity after debug gating changes and log deltas.
31. [~] Root-cause analysis for compute/fragment divergence (Kerr presets).
32. [ ] Add regression thresholds tied to LUT metadata + units.

## Phase 3: GPU + CPU Performance Instrumentation
33. [x] Add GPU timing CSV logging with stride control.
34. [ ] Parse `gpu_timing.csv` and flag outliers in a report.
35. [ ] Document perf sysctl tuning for low-loss sampling.
36. [x] Refresh flamegraph via `scripts/run_flamegraph.sh`.
37. [ ] Build a "perf pack" target that runs GPU timing + flamegraph.
38. [ ] Integrate Tracy capture (GPU zones + frame markers).
39. [ ] Add meshoptimizer overdraw pass for disk geometry.
40. [ ] Add a depth pre-pass toggle for dense disk surfaces.

## Phase 4: Visual Assets + Procedural Enhancements
41. [ ] Import NASA/JPL/ESA assets (2K/4K/8K) and track licenses.
42. [ ] Add parallax expansion with per-layer LOD + drift controls.
43. [ ] Add `fastnoise2` noise texture generation for disk detail.
44. [ ] Add noise LUT/texture upload path with caching.
45. [ ] Prototype wiregrid curvature overlay for spacetime visualization.
46. [ ] Evaluate background HDR input path (OpenImageIO/tinyexr).
47. [ ] Add a curated asset manifest in `docs/IMAGE_SOURCES.md`.
48. [ ] Add validation screenshots for new backgrounds + parallax.

## Phase 5: Documentation + Cleanroom Tracking
49. [x] Update `INTEROP_BEST_PRACTICES.md` with SPIR-V/overdraw notes.
50. [x] Update `PERF_TOOLING.md` with SPIR-V bake instructions.
51. [x] Update `OPENGL_45_46_SHADER_REPORT.md` with toolchain summary.
52. [ ] Consolidate cleanroom decisions and migrations in `docs/CLEANROOM_*`.
53. [ ] Maintain `STATUS.md` + `TODO_FIXES.md` after each milestone.
54. [ ] Add a "release checklist" doc for parity, perf, and visual validation.
55. [ ] Review roadmap quarterly and archive completed phases.
