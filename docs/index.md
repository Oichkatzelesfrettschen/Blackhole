# Blackhole Documentation

Real-time black hole rendering in OpenGL -- C++23 + OpenGL 4.6.

## Getting Started

- [Building](getting-started/building.md) -- full build guide (Conan 2.x, CMake presets, PGO)
- [User Guide](getting-started/user-guide.md) -- controls, presets, and runtime options
- [Quick Reference](getting-started/quick-reference.md) -- cheat sheet
- [Troubleshooting](getting-started/troubleshooting.md) -- common issues and fixes
- [Requirements](getting-started/requirements.md) -- system and dependency requirements

## Developer Guide

- [Status](developer-guide/status.md) -- current project status and active issues
- [Roadmap](developer-guide/roadmap.md) -- master development roadmap
- [Backlog](developer-guide/backlog.md) -- bug fixes and TODO items
- [Build Optimization](developer-guide/build-optimization.md) -- compile-time optimization
- [SIMD](developer-guide/simd.md) -- SIMD vectorization guide
- [GLSL Build](developer-guide/glsl-build.md) -- shader compilation workflow
- [Dependencies](developer-guide/dependencies.md) -- dependency matrix
- [Perf Tooling](developer-guide/perf-tooling.md) -- profiling and benchmarking tools
- [Sanitizers](developer-guide/sanitizers.md) -- ASan/TSan/UBSan workflows
- [Compare Sweep](developer-guide/compare-sweep.md) -- compute/fragment parity sweeps

## Physics

- [Architecture](physics/architecture.md) -- physics module design and data flow
- [Lacunae](physics/lacunae.md) -- structured analysis of physics/math/performance gaps
- [Unit System](physics/unit-system.md) -- CGS/geometric/code unit alignment
- [Cleanroom](physics/cleanroom.md) -- port map, imports, decisions, interop, migration

## GPU

- [Shader Report](gpu/shader-report.md) -- OpenGL 4.5 to 4.6 shader changes
- [Scope](gpu/scope.md) -- OpenGL 4.6 feature scope and validation
- [Wayland](gpu/wayland.md) -- Wayland optimization notes
- [Interop](gpu/interop.md) -- compute/fragment interop best practices

## UI

- [HUD](ui/hud.md) -- heads-up display overlay
- [Wiregrid](ui/wiregrid.md) -- wiregrid rendering best practices
- [Integration Snippets](ui/integration-snippets.md) -- UI integration code samples
- [MangoHUD](ui/mangohud.md) -- MangoHUD integration scope

## Assets

- [Image Sources](assets/image-sources.md) -- background image provenance
- [Image Candidates](assets/image-candidates.md) -- candidate images for backgrounds
- [Background Pipeline](assets/background-pipeline.md) -- asset processing pipeline

## Plans

- [Physics Implementation](plans/physics-implementation.md) -- physics implementation plan
- [Phases 5-6](plans/phases-5-6.md) -- phases 5 and 6 implementation plan
- [GRMHD Ingestion](plans/grmhd-ingestion.md) -- GRMHD data ingestion pipeline
- [GRB Modulation](plans/grb-modulation.md) -- GRB time modulation plan
- [LUT Pipeline](plans/lut-pipeline.md) -- look-up table generation pipeline
- [Radiative Transfer LUT](plans/radiative-transfer-lut.md) -- radiative transfer LUT plan
- [Z3 Integration](plans/z3-integration.md) -- Z3 formal verification integration
- [Eigen Refactor](plans/eigen-refactor.md) -- Eigen library refactoring plan
- [Halide Feasibility](plans/halide-feasibility.md) -- Halide DSL feasibility study
- [Reverse Engineering](plans/reverse-engineering.md) -- reverse engineering plan
- [OpenUniverse](plans/openuniverse.md) -- OpenUniverse integration scope
- [Local Repos](plans/local-repos.md) -- local repository scope

## Validation

- [Phase 1](validation/phase-1.md) -- phase 1 validation results

## Archive

Historical docs preserved for git blame traceability.

- [Performance](archive/performance/) -- debugging session investigation docs
- [Sessions](archive/sessions/) -- session reports and summaries
- [Phases](archive/phases/) -- phase completion reports
- [Physics Updates](archive/physics-updates/) -- historical physics update notes
- [Build Migration](archive/build-migration/) -- Conan 2.x migration docs
- [2026Q1](archive/2026Q1/) -- Q1 2026 archive
