# CI execution and iteration cost

GitHub executes `.github/workflows/ci.yml` on hosted Ubuntu 24.04 runners.
The repository owns workflow definitions, Conan profiles, CMake presets,
tests, and replay scripts. GitHub settings own Actions enablement, repository
visibility, and branch protection. Public visibility alone establishes neither
successful validation nor an enforced merge gate.

The `main` branch requires passing `ci`, `ci-analysis`, and `ci-release` checks
against an up-to-date PR branch, resolved review conversations, and PR-based
integration. The protection applies to administrators. Force pushes and branch
deletion are disabled. GitHub stores those settings outside the Git tree; inspect
them with `gh api repos/Oichkatzelesfrettschen/Blackhole/branches/main/protection`.
Branch protection names only those three checks; every other lane below is
advisory, so its red result informs a review without blocking the merge.

## Execution lanes

| Trigger | Preset | Coverage |
| --- | --- | --- |
| Pull request and main push | `ci` | Desktop compilation, CPU tests, GLSL validation; strict warnings and IEEE math |
| Pull request and main push | `ci-analysis` | CPU build/tests with every enabled clang-tidy and cppcheck diagnostic enforced |
| Pull request and main push | `ci-release` | CPU build/tests with LTO and fast-math, including per-target IEEE overrides |
| Pull request and main push | `ci-clang` | Advisory: the `ci` configuration compiled by clang 18 over the same GCC 14 packages; strict warnings, CPU tests |
| Pull request and main push | `ci-clang-fast-math` | Advisory: `ci-clang` with fast-math, where clang's `-Wnan-infinity-disabled` rejects NaN and infinity classification GCC accepts |
| Pull request and main push | `ci-sanitize` | Advisory: GCC 14 AddressSanitizer and UBSan build; every test except `gpu_cpu_parity` and `kerr_shader_capture` |
| Weekly schedule | Every preset above | Revalidate the default branch |
| Weekly schedule and manual dispatch | `bench.yml`, `ci` preset | Advisory `physics_bench` run compared with `bench/baseline-ci.json`; JSON retained 90 days |
| Manual dispatch | Selected preset | Replay any lane against a selected ref |

The hosted CPU lanes establish compilation and executable CPU validation.
CUDA device execution, desktop OpenGL rendering, and Blender/Octane runtime
qualification require their corresponding hardware and environments.

All jobs run independently. The quick `ci` result provides early compiler
and CPU-test feedback while analysis and release validation continue.
Desktop variants share one `blackhole_runtime_assets` producer. The producer
waits for generated fonts and backdrops, then copies changed assets and shaders
once before the desktop targets link. Separate post-link copies raced on the
same destination during a parallel build; the shared dependency removes that
race without reducing compiler parallelism.
Ninja release builds allow one LTO link at a time because each link can spawn
an all-CPU worker pool. Compiler jobs remain parallel; serializing whole-program
links bounds the nested worker pools instead of stacking several per runner. Requested
analyzers must be installed; configuration fails when either executable is absent.
Imported ImGui, STB, and GL callback implementation files retain upstream lint
ownership; project translation units and project headers retain strict analysis.

Conan and CMake use GCC 14 through `conan/profiles/ci`. Python build tools have
explicit versions in `scripts/ci/requirements.txt`; `conan.lock` pins dependency
recipe revisions. Local recipes are exported before resolving the lock.
Conan dependencies use a cache keyed by the lock, recipe, profile, and tool
inputs. Successful dependency installation saves that cache before project
compilation; compiled objects are also retained when a later build fails. ccache stores compiler output separately for each lane. Each compiler
invocation still checks its source, headers, compiler, and flags. CMake build
directories stay fresh on hosted jobs.

Only main pushes and pull requests trigger automatic per-change builds, avoiding
a second branch-push run for every PR commit. A newer PR revision cancels its
superseded run. Main pushes retain their own validation. Each job has a 90-minute
upper bound; a timeout is a failed gate, never validation evidence.

## Clang lanes

Conan identifies the dependency packages by the GCC 14 settings of
`conan/profiles/ci`, and the generated toolchain's own
`set(CMAKE_CXX_COMPILER ...)` overrides a compiler given on the CMake command
line. The clang lanes therefore run a second `conan install` into
`build/CI-clang-deps` with
`tools.build:compiler_executables={"c":"clang-18","cpp":"clang++-18"}`: that
configuration stays out of the package id, so the same cached packages resolve,
and `--build=never` keeps clang from compiling a package into the shared cache.
The install also sets `tools.cmake.cmaketoolchain:user_presets` empty, because a
second include of a generated `conan-release` preset in `CMakeUserPresets.json`
is a duplicate CMake rejects. The `ci-clang` and `ci-clang-fast-math` presets
read that toolchain; `compile_commands.json` in `build/CI-Clang` names
`clang++-18`. LTO stays off in these presets, since the packages carry GCC
objects.

Clang and GCC reject different code. clang 18 diagnoses `std::isnan`,
`std::isinf`, `std::isfinite`, and `numeric_limits<T>::infinity()` under
`-ffinite-math-only` as errors with `-Werror`, which the GCC 14 `ci-release`
lane accepts silently while folding those checks to constants.

## Sanitizer lane

`ci-sanitize` inherits `ci` with `ENABLE_ASAN` and `ENABLE_UBSAN` on. Hardening
is off because `_FORTIFY_SOURCE` conflicts with the ASan interceptors, and
`-Werror` is off because instrumentation inflates stack frames past
`-Wstack-usage=8192` and perturbs GCC's flow-sensitive warnings
(`-Wmaybe-uninitialized`, `-Wstrict-overflow`); the uninstrumented lanes
enforce those warnings on the same sources. `ENABLE_UBSAN` compiles with
`-fno-sanitize-recover=undefined`, so a UBSan report aborts the test instead of
printing and exiting 0. The lane excludes `gpu_cpu_parity` and
`kerr_shader_capture` by name: they open a GL context through GLFW when a
display exists and carry no `detect_leaks=0` environment, so LeakSanitizer
reports the GL driver's allocations as leaks. The other `gpu`-labeled tests
run: `grmhd_pbo_state_machine` mocks GL, and `gpu_compute_validation`,
`grmhd_gpu_async_validation`, and `z3_verification` (which also creates a GLFW
window when it can) already disable LeakSanitizer through
`SANITIZER_TEST_ENV`.

`SANITIZER_TEST_ENV` in `CMakeLists.txt` gains `ASAN_OPTIONS=detect_leaks=0`
partway through test registration, and a test's `ENVIRONMENT` property
overrides the job environment. LeakSanitizer therefore checks only the tests
registered before that point or registered without the property; the lane
establishes memory-safety and undefined-behavior evidence, and leak evidence
only for that subset.

## Strict source validation

The `ci` lane runs `scripts/ascii_sweep.py` in verifier mode before any build
step. Its scope is every `docs/**/*.md` outside a path containing `archive`,
plus `AGENTS.md`, `README.md`, `CHANGELOG.md`, `gemini.md`, and `CLAUDE.md`;
any non-ASCII character there fails the lane. The sweep has no exemption for
quoted upstream text or accented names, so such material belongs under
`docs/archive/` or in ASCII transliteration.

Every enabled clang-tidy diagnostic is an error.
The header filter covers maintained C++ headers, including `.hpp` reference
implementations. Analysis objects depend on `.clang-tidy`, so an incremental
build also reruns analysis after a policy edit.
The C++ reference APIs follow repository naming rules; an explicit
[GLSL interface adapter](verified-glsl-generation.md) preserves maintained shader
names. Shader validation uses the checked-in shader sources; the generator's
separate lowering limitations remain documented in that guide. The cleanup
preserves the configured diagnostic set and fixes compiler, clang-tidy, and
cppcheck findings in project sources, tests, and tools. Renderer helper
extraction preserves the checked render-call ordering; settings persistence
tests exercise serialized
values and legacy alias precedence. HDF5 tool tests cover malformed metadata,
argument handling, and native fixture round trips through CTest dependencies.

CPU fixtures identify their evidence boundary explicitly. Fixed layout facts
use compile-time assertions; runtime checks exercise buffer contents, temporal
interpolation, and numerical helpers. A CPU fixture does not establish shader
execution, occupancy, asynchronous device behavior, or GPU timing.

## Measured dependency costs

Hosted Ubuntu runs on September 22, 2026 reported four logical CPUs. Cold Conan
installation used 365-372% CPU, demonstrating roughly 3.7 active cores during
the dependency stage. The restored dependency graph completed in 2.94 seconds;
GitHub cache download and extraction are separate steps.

| Observation | Wall time | Evidence run |
| --- | --- | --- |
| Cold release dependencies | 19 min 9.78 s | `35696550322` |
| Cold analysis dependencies | 25 min 24.97 s | `35696547660` |
| Cached analysis dependencies | 2.94 s | `35699075120` |

The cold release log attributes 722.1 seconds to Z3, 108.0 to Highway, 67.8 to
glbinding, 51.0 to FlatBuffers, 40.7 to HDF5, 29.7 to GMP, 27.1 to SLEEF, and
17.4 to MPFR. These package times identify dependency compilation as the largest
observed cold-start cost. The reusable compressed dependency cache is about
170 MB. The measurements cover dependencies; project build and test completion
must be assessed from their separate retained stage records.

## Processor allocation and replay

The runner records `nproc`, `lscpu`, and available memory, then supplies that CPU
count to Conan `tools.build:jobs`, CMake `--parallel`, and CTest `--parallel`.
The count belongs to the assigned runner, not the developer workstation.
CTest respects each registered test's own timeout and dependency properties.

For local iteration with the repository's Clang profile, use the separate
`dev` tree. The installer records the actual Clang major version; Conan must
support that version instead of assigning another compiler's package identity.

```sh
./scripts/conan_install.sh --preset dev
cmake --preset dev
./scripts/build.sh dev
ctest --test-dir build/Dev/Release --output-on-failure --parallel "$(nproc)"
```

For an existing Release configure, use:

```sh
./scripts/build.sh release
CMAKE_BUILD_PARALLEL_LEVEL=6 ./scripts/build.sh release
```

The wrapper defaults to all CPUs reported by `nproc`. An explicit positive job
count lets a memory-constrained host bound concurrent compiler processes.

Replay the hosted lane after installing the workflow's system dependencies and
setting `PYTHON` to the intended interpreter:

```sh
"$PYTHON" -m pip install -r scripts/ci/requirements.txt
export CONAN_HOME="$PWD/.conan"
export CMAKE_BUILD_PARALLEL_LEVEL="$(nproc)"
export CTEST_PARALLEL_LEVEL="$CMAKE_BUILD_PARALLEL_LEVEL"
./scripts/conan_export_local_recipes.sh
conan install . --output-folder=build/CI-deps --lockfile=conan.lock \
  --build=missing -pr:a conan/profiles/ci \
  -c:a tools.build:jobs="$CMAKE_BUILD_PARALLEL_LEVEL"
cmake --preset ci -DPYTHON3_EXECUTABLE="$PYTHON"
./scripts/build.sh ci
ctest --test-dir build/CI --output-on-failure --no-tests=error \
  --parallel "$CTEST_PARALLEL_LEVEL"
```

`scripts/ci/run_stage.sh NAME COMMAND...` records command logs, exit status,
wall time, CPU time, and peak RSS under `build/ci-reports`. GitHub publishes the
timings in the job summary and retains logs, JUnit output, and CMake failure
records for 14 days. Compare dependency, compilation, and test times separately;
cache restoration and scheduling remain visible as GitHub job steps.

## Local replicas of the hosted lanes

A workstation build and a hosted lane disagree for three reasons. The local
Conan toolchain pins clang (the `release` preset's `compile_commands.json`
records `/usr/bin/clang++`), while every hosted lane except the clang lanes
compiles with GCC 14 through `conan/profiles/ci`. The analysis lane runs the
Ubuntu 24.04 analyzers, clang-tidy 18.1.3 (package `clang-tidy-18`,
`1:18.1.3-1ubuntu1`) and cppcheck 2.13.0, and host
analyzers of other versions report a different set: clang-tidy 22 enforces
checks clang-tidy 18 lacks, such as `readability-math-missing-parentheses` and
`modernize-use-designated-initializers` in `tests/wiregrid_overlay_test.cpp`,
and cppcheck 2.21 reports `uninitMemberVarNoCtor` in `src/settings.cpp`, which
2.13 accepts. A local `release` build with `ENABLE_CLANG_TIDY` and
`ENABLE_CPPCHECK` on can therefore fail on sources the required lanes pass.
The CI analyzer versions are the merge gate; findings from newer host
analyzers are advisory until the lane's pinned versions move.

The fast-math lanes (`ci-release` and `ci-clang-fast-math`) compile with
`-ffast-math`, under which GCC folds `std::isnan` and `std::isfinite` to
constants and clang rejects them. Production code classifies infinity and NaN
through `physics::safeIsfinite`, `safeIsnan`, and `safeIsinf` from
`src/physics/safe_limits.h`, on a value that reaches memory through a
reference or an output parameter: clang marks a by-value floating-point return
`nofpclass(nan inf)` under `-ffinite-math-only`, so a NaN returned by value is
poison before any check sees it. A test that constructs or classifies
non-finite values takes the per-target `-fno-fast-math` override in
`CMakeLists.txt`.

| Script | Reproduces | Needs |
| --- | --- | --- |
| `scripts/ci/ci_replica.sh [REGEX]` | `ci` build and CTest with GCC 14; `CI_REPLICA_RELEASE=1` for `ci-release`, `CI_REPLICA_SANITIZE=1` for `ci-sanitize` | `gcc-14`, `g++-14`, `bwrap`, Ninja, and `./scripts/conan_install.sh Release build` |
| `scripts/ci/cppcheck_ci.sh [-p DIR] [-b BASE] [-f] [FILE...]` | `ci-analysis` cppcheck 2.13.0 over changed and untracked `.cpp` files, once per distinct CMake `-D`/`-I`/`-U` flag set among each file's compile entries | Docker or Podman; `build/CiLike` from `ci_replica.sh` |
| `scripts/ci/tidy18.sh [-p DIR] [-f] FILE...` | `ci-analysis` clang-tidy 18 (wheel 18.1.1; CI runs 18.1.3) against GCC 14's libstdc++, over the `ci` configuration | `uv` (or `CLANG_TIDY` pointing at a clang-tidy 18 binary), `g++-14`, and `build/CiLike` from `ci_replica.sh` |

`ci_replica.sh` copies the local Release generators, replaces the compiler the
toolchain names with GCC 14, and mounts an empty `/usr/include/glm` through
`bwrap`, since the runner has no system glm; logs land in
`build/cilike*.log`. It reuses the locally built Conan packages, so it
reproduces the compiler, flags, and tests of a lane but not the lane's own
package binaries. `cppcheck_ci.sh` builds its image from
`scripts/ci/Dockerfile.cppcheck` on first use and mounts the checkout and the
Conan cache read-only at their host paths. CMake attaches cppcheck to every
target, so a source compiled by several targets is analyzed with each target's
definitions: `src/main.cpp` runs twice, once with
`BLACKHOLE_APP_VARIANT_GLSL_ONLY=1`, and a defect inside that variant's
`#if` block fails the script. `tidy18.sh` runs the PyPI
`clang-tidy==18.1.1` wheel through `uvx`. PyPI publishes no 18.1.3 wheel, and
18.1.1 is the nearest release; its `--list-checks --checks='*'` output is
identical to the Ubuntu 18.1.3 binary's (537 checks). clang-tidy 18 cannot
parse the libstdc++ of a newer host GCC, so the script substitutes GCC 14's
headers for the compile database's standard library. Both analyzer scripts
default to `build/CiLike`, the GCC 14 tree `ci_replica.sh` configures and
exports, because `SIMD_TIER`, `ENABLE_FAST_MATH`, and `ENABLE_NATIVE_ARCH`
select preprocessor branches (the `__AVX2__` paths in `src/physics/batch.h`);
`scripts/ci/check_ci_config.sh` compares a tree's cache with every
`cacheVariables` entry of the `ci` preset in `CMakePresets.json`, inherited
entries included, except the toolchain path and the analyzer switches
ci-analysis turns on; that covers the switches that register targets and
sources (`BUILD_TESTING`, `ENABLE_DESKTOP_APP`, `ENABLE_CUDA`,
`ENABLE_BLENDER_BRIDGE`, `ENABLE_SHADER_VALIDATION`) as well as the
preprocessor ones. A mismatch stops either script with exit 2 unless `-f` is
given. `tidy18.sh` also exits 2 when clang-tidy fails on a file without
printing a diagnostic. Each script documents its options in its header comment.

## Audit baseline

The September 21 audit queried all 64 retained C++ CI runs. Every run reported
failure; creation-to-completion elapsed times ranged from 31 to 74 seconds
(mean 38.77 seconds). Historical logs had expired with HTTP 410. Retained
annotations reported exit 1 and deprecated Node 20 actions, which establish
failure but leave the original command-level cause unknown.

At audit entry, the repository was private, Actions were disabled, and `ci.yml`
was manually disabled. The user authorized publication and restored hosted CI.
The previous workflow used `build/build/Release`, while the Conan recipe uses
`cmake_layout(build_folder=".")`; it also omitted local recipe export and the
font compiler required by desktop configuration.

The local Release cache used Unix Makefiles, clang-tidy, cppcheck, and LTO.
Its compile database contained 341 commands for 165 distinct source paths;
`schwarzschild.cpp` appeared nine times and `shader.cpp` seven times. Generated
Makefiles attached clang-tidy to 88 targets and cppcheck to 84 targets. Every
build preset omitted a job count. The documented plain CMake build command
therefore used Make's serial default unless the environment supplied jobs.
The inspected commit/push hooks invoked Git LFS; the pre-commit hook was absent.
The generated Release compile commands reference repository-local `.conan/p/`
packages, while the referenced package directories and default profile were absent
from the inspected cache. Existing build metadata therefore does not establish a reusable
installed dependency cache. The native Boost probe used the separate global
`~/.conan2` source cache and establishes only its five tested consumers.

Repeated compilation, attached analysis, and linking explain mechanisms that
increase local iteration cost. Historical evidence does not establish a measured
hours-long GitHub C++ build. Some repeated physics compilation preserves distinct
floating-point flags and ABI variants; replacing every copy with one library
would require a separate numerical and layout audit.

Boost uses `header_only=True`: the five numerical test consumers link
`Boost::headers` and assert their Bessel/Jacobi feature macros at compile time.
The locked recipe omits `Boost::math` in header-only mode, so changing the Conan
option alone would have weakened those tests. The recipe retains `Boost::boost` as an alias requiring `Boost::headers`,
which preserves the bridge dependency. Existing desktop and bridge numerical
paths retain their own dependency declarations.
