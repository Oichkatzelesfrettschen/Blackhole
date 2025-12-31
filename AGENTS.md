# Repository Guidelines

## Architecture Overview
The core pipeline is C++23 + OpenGL 4.6 with a fragment/compute ray integrator,
post-processing, and LUT-backed validation assets.

```
[Input] -> [Camera + Physics] -> [Ray Integrator (frag/comp)] -> [Bloom/Tone/Depth] -> [Present]
                          \-> [LUTs + Validation Assets] -> [Bench + CSV]
```

## Project Structure & Module Organization
- `src/` (runtime + physics), `shader/` (GLSL 460), `assets/` (LUTs/validation).
- `bench/`, `tests/`, `tools/`: perf harness, test binaries, data utilities.
- `docs/`: integration plans and research notes; `requirements.md` is dependency truth.
- `conan/recipes/` + `scripts/`: local Conan recipes and helper scripts.

## Build, Test, and Development Commands
Use repo-local Conan state (`.conan/`) for reproducible builds:
```bash
./scripts/conan_install.sh Release build
cmake --preset release
cmake --build --preset release
ctest --test-dir build/Release --output-on-failure
cmake --build --preset release --target validate-shaders
```
Run: `./build/Release/Blackhole` or `./build/Release/physics_bench`.

## Coding Style & Naming Conventions
- C++23, 2-space indent, brace-on-same-line (see `.clang-format`).
- Types: `CamelCase`; functions/vars: `lowerCamelCase`.
- GLSL: `#version 460` first line; include via `GL_GOOGLE_include_directive`.

## Testing Guidelines
- Tests live in `tests/` and are driven by `ctest`.
- Keep numeric tolerances explicit near the test and tied to units/LUT metadata.

## Commit & Pull Request Guidelines
- Use conventional prefixes (`feat:`, `fix:`, `docs:`, `chore:`).
- PRs include a short summary, tests run, and screenshots for visual changes.

## Progress & Documentation
- Current status and active plans: `STATUS.md`.
- Backlog only: `TODO_FIXES.md`.
- Deep design references live in `docs/` (GRMHD, LUT pipeline, cleanroom ports).
