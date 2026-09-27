# Repository Guidelines

## Instruction source

`AGENTS.md` is the root instruction file for Blackhole and owns its rules. Every agent and contributor reads it directly. `CLAUDE.md` is a tracked, repository-relative symbolic link to `AGENTS.md`, so Claude Code receives the canonical rules through the same bytes and the body lives in one place. A tool that requires a differently named loader references this file rather than copying doctrine that can drift.

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
- `docs/`: integration plans and research notes; `docs/developer-guide/dependencies.md` is dependency truth.
- `conan/recipes/` + `scripts/`: local Conan recipes and helper scripts.
- `external/`: vendored third-party sources (ImPlot via `scripts/fetch_implot.sh`, ImGui backends, GL debug callback).

## Build, Test, and Development Commands
Use repo-local Conan state (`.conan/`) for reproducible builds:
```bash
./scripts/conan_install.sh Release build
./scripts/fetch_implot.sh
cmake --preset release
./scripts/build.sh release
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
- A new performance assertion compares ratios, not wall time: load N and 8N and bound the time ratio well below the quadratic 64x, or check structurally that the slow path was not entered. ASan+UBSan and shared runners stretch absolute times several fold; a wall-clock bound fails there with no defect present.
- Under `ENABLE_ASAN`, `ENABLE_UBSAN`, or `ENABLE_TSAN` every ctest `TIMEOUT` is multiplied by 4 (end of `CMakeLists.txt`); set a test's `TIMEOUT` from its release timing.
- `ci-clang-fast-math` and `ci-release` build with `-ffast-math`, where `std::isfinite`/`std::isnan`, `infinity()`, and `quiet_NaN()` are undefined and clang rejects them (`-Wnan-infinity-disabled`). Code compiled into the app or `blackhole_testcore` uses `physics::safeIsfinite`/`safeIsnan` (`src/physics/safe_limits.h`); a test that feeds inf or NaN needs the per-target `if(ENABLE_FAST_MATH) -fno-fast-math` override.

## Commit & Pull Request Guidelines
- Use conventional prefixes (`feat:`, `fix:`, `docs:`, `chore:`).
- PRs include a short summary, tests run, and screenshots for visual changes.
- Branch protection requires `ci`, `ci-analysis`, and `ci-release` green, the branch up to date, and every review conversation resolved; the Codex reviewer re-reviews every push, including a server-side update-branch.
- Triage each review thread by reachability. A defect a user reaches through a documented interface (defaults, CLI, environment, UI, story or save files the program writes, a CI lane) with input that interface accepts as valid, including non-default values, is fixed, with all such threads batched into one push. Missing rejection of malformed or adversarial input (a hand-edited save, a story outside its documented schema, a value past a documented floor) and extremes outside the documented domain get a reply naming the boundary, a follow-up issue carrying the falsifier, and resolution without a push. Verify a thread's claim against the source first; a refuted claim gets the refuting file and line in the reply.
- Before a push, run the local replicas of the slow lanes: `scripts/ci/ci_replica.sh` (GCC 14; `CI_REPLICA_RELEASE=1` for fast-math + LTO), `scripts/ci/cppcheck_ci.sh`, and `scripts/ci/tidy.sh` on changed `.cpp` files; for a changed header, pass the translation units that include it (`git grep -l '"path/to/header.h"' -- src tests '*.cpp'`), since both scripts analyze translation units, as hosted `ci-analysis` does. Each push costs a full CI round and a new review.

## Progress & Documentation
- Current status and active plans: [`docs/developer-guide/status.md`](docs/developer-guide/status.md).
- Backlog only: [`docs/developer-guide/backlog.md`](docs/developer-guide/backlog.md).
- Deep design references live in `docs/` (GRMHD, LUT pipeline, cleanroom ports).
- Full documentation index: [`docs/index.md`](docs/index.md).

## Claude Code notes

These notes came from the retired standalone `CLAUDE.md` loader and hold the Claude Code specifics that a tool-generic guide leaves out. A rule that applies to every agent lives in the sections above.

This repository now centralizes contributor guidance, architecture notes,
and progress references in `AGENTS.md`.

Please read `AGENTS.md` and `docs/developer-guide/status.md` for current information.
