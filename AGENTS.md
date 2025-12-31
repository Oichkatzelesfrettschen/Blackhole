# Repository Guidelines

## Architecture Overview
The renderer is a C++23 + OpenGL 4.6 pipeline with fragment + compute raytracing,
post-processing, and optional LUT-backed physics validation.

```
[Input] -> [Camera + Physics] -> [Raytrace frag/comp] -> [Bloom/Tonemap/Depth] -> [Present]
                         \--> [LUTs + Validation Assets] -> [Bench/CSV]
```

## Project Structure & Module Organization
- `src/`: runtime (`src/main.cpp`, `src/input.*`, `src/render.*`, `src/shader.*`) and `src/physics/`.
- `shader/`: GLSL 460 (`.frag/.vert/.comp`) plus `shader/include/`.
- `assets/`: LUTs and validation tables (`assets/luts/`, `assets/validation/`).
- `external/implot`: vendored ImPlot (scripted fetch).
- `bench/`, `docs/`, `scripts/`: perf harness, research plans, and generators.

## Build, Test, and Development Commands
- `./scripts/conan_install.sh Release build` (uses repo-local `.conan/`)
- `cmake --preset release` then `cmake --build --preset release`
- `ctest --test-dir build/Release --output-on-failure`
- Shader checks: `cmake --build --preset release --target validate-shaders`
- Optional toggles: `-DENABLE_TRACY=ON`, `-DENABLE_RMLUI=ON`, `-DENABLE_Z3=ON`, `-DENABLE_PRECISION_TESTS=ON`
- Run: `./build/Release/Blackhole`, `./build/Release/physics_bench`

## Coding Style & Naming Conventions
- C++23, 2-space indent, braces on same line, CamelCase types, lowerCamelCase vars.
- GLSL: `#version 460` first line; includes via `GL_GOOGLE_include_directive`.

## Testing Guidelines
- `physics_test`, `grmhd_pack_fixture`, `precision_regression` (if enabled).
- Keep numeric tolerances explicit and documented near tests.

## Dependencies & Configuration Notes
- Conan pins are the source of truth; see `requirements.md` for versions and notes.
- ImGui 1.92.5-docking and Tracy 0.12.2 ship as local recipes under `conan/recipes/`.
- `settings.json` is runtime-generated; maintain backward compatibility when adding fields.

## Commit & Pull Request Guidelines
- Use short imperative or conventional prefixes (`feat:`, `docs:`, `chore:`).
- PRs include summary, tests run, and screenshots for visual changes.
- Track state in `STATUS.md`; backlog lives in `TODO_FIXES.md`.
