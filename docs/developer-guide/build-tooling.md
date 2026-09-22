# Build and analysis tooling

Blackhole compiles with **clang++ 22** in the default configuration (the
`compile_commands.json` records `/usr/bin/clang++`, even though the Conan profile
names gcc for dependency resolution). **gcc 16** is also installed and builds the
tree. The two compilers see different defects, so the strongest coverage comes
from building with both and running each toolchain's analyzers over the result.
This guide maps the maximal tooling to that reality: what is already wired into
CMake, what to add per compiler, and what complementary tools apply to this
specific codebase (a deterministic simulation core plus an OpenGL/CUDA renderer).

## Which compiler, and why it matters

| Capability | clang 22 (the build compiler) | gcc 16 (cross-check) |
| --- | --- | --- |
| Static analyzer | clang-tidy, `scan-build` (Clang Static Analyzer) | `-fanalyzer` (`ENABLE_GCC_ANALYZER`) |
| AddressSanitizer / UBSan / TSan | yes (`-fsanitize=address,undefined,thread`) | yes |
| MemorySanitizer (uninitialised reads) | yes (`-fsanitize=memory`) -- clang only | no |
| libFuzzer | yes (`-fsanitize=fuzzer`) | no (use AFL++ instead) |
| Warning set | clang `-Weverything` subset | gcc `-Wall -Wextra` catches a different tail |

Rule of thumb: keep clang as the primary build (tidy, MSan, libFuzzer), and run a
periodic gcc build for its warnings and `-fanalyzer`. Neither is a superset of
the other.

## Already wired into CMake

These options exist in `CMakeLists.txt`; enable at configure time, e.g.
`cmake --preset release -DENABLE_ASAN=ON`.

| Option | Default | What it does |
| --- | --- | --- |
| `ENABLE_WERROR` | ON | `-Werror`; the build treats warnings as errors. |
| `ENABLE_CLANG_TIDY` | ON | Runs clang-tidy per TU against `.clang-tidy`. |
| `ENABLE_CPPCHECK` | ON | Runs cppcheck as a compiler launcher. |
| `ENABLE_IWYU` | OFF | include-what-you-use include hygiene. |
| `ENABLE_GCC_ANALYZER` | OFF | gcc `-fanalyzer` path-sensitive analysis (gcc build only). |
| `ENABLE_ASAN` / `ENABLE_UBSAN` / `ENABLE_TSAN` | OFF | Sanitizer instrumentation (`-fsanitize=...`). |
| `ENABLE_COVERAGE` | OFF | Coverage instrumentation (gcovr vendored under `tools/gcovr/`). |
| `ENABLE_FUZZING` | OFF | Builds the fuzz targets (clang/libFuzzer). |

Tests that touch non-finite math carry a `-fno-fast-math` override, and the
determinism-sensitive campaign targets stay IEEE under `ENABLE_FAST_MATH`; do not
remove those per-target overrides when enabling sanitizers.

### Sanitizer runs

ASan and UBSan combine; TSan and MSan each need their own build. Because the
campaign core is determinism-sensitive, run the campaign suite under ASan+UBSan:

```
cmake --preset debug -DENABLE_ASAN=ON -DENABLE_UBSAN=ON
cmake --build --preset debug
ctest --test-dir build/Debug -L campaign --output-on-failure
```

TSan is only meaningful for the threaded surfaces (the GRMHD async tile streamer
and Taskflow), not the single-threaded campaign core. MSan needs an
MSan-instrumented libc++ to avoid false positives from the standard library;
reserve it for isolated, dependency-light TUs.

## Complementary tools (not compiler flags)

Available on the host (see `~/Documents/AI/Notes/1_TOOLS.md`), useful here:

- **`rr`** -- record/replay debugging. The campaign core is deterministic by
  design (integer turn count is the only loop variable, FNV-1a state digests), so
  `rr record ./build/Release/campaign_sim --compare` then `rr replay` reproduces
  any digest divergence exactly, which a normal debugger cannot. This is the right
  tool the moment a determinism test fails.
- **`cppcheck`** standalone for a whole-tree pass with the html report:
  `cppcheck --enable=all --project=build/Release/compile_commands.json`.
- **`scan-build`** for the Clang Static Analyzer's interprocedural path checks,
  which clang-tidy does not run: `scan-build cmake --build --preset release`.
- **`valgrind --tool=memcheck`** for a no-instrumentation memory pass (use when a
  sanitizer build is inconvenient; do not combine with ASan). **`callgrind`** plus
  `callgrind_annotate` / `gprof2dot` for call-graph profiling.
- **`perf record` + `hotspot`** (or `perf script | flamegraph`) for CPU sampling
  of the renderer's hot path; **`heaptrack`** for allocation growth; **`uftrace`**
  for function-graph timing of the campaign advance loop.
- **`lizard`** for cyclomatic-complexity and function-length metrics (the main
  loop and the strategic-map render functions are the recurring hotspots kept
  under the tidy cognitive-complexity limit); **`cloc`** / **`scc`** for size
  baselines.

## Renderer (OpenGL/CUDA) specifics

The determinism tooling above covers the campaign core. The GL/CUDA renderer
needs its own instruments: `apitrace` / `gpuvis` for frame capture and CPU-GPU
timeline correlation, NVIDIA Nsight for CUDA kernel profiling, and the in-tree
GL debug callback (already active -- see the `[GL Debug]` startup lines). Keep
these separate from the headless campaign analysis, which links no GL.

## Suggested cadence

- **Every change:** the default clang build is `-Werror` + clang-tidy + cppcheck.
- **Before a merge:** an ASan+UBSan `ctest` run of the affected suite.
- **Periodic:** a gcc build (`-fanalyzer`, gcc warnings), a `scan-build` pass, and
  a `lizard` complexity check.
- **On a determinism failure:** `rr record`/`replay` on `campaign_sim`.
- **On a perf regression:** `perf` + `hotspot`, or `callgrind` for exact counts.

Hosted execution and iteration costs: [CI guide](ci.md).
