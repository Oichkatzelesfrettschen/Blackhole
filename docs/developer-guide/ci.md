# CI execution and iteration cost

GitHub executes `.github/workflows/ci.yml` on hosted Ubuntu 24.04 runners.
The repository owns workflow definitions, Conan profiles, CMake presets,
tests, and replay scripts. GitHub settings own Actions enablement, repository
visibility, and branch protection. Public visibility alone establishes neither
successful validation nor an enforced merge gate.

## Execution lanes

| Trigger | Preset | Coverage |
| --- | --- | --- |
| Pull request and main push | `ci` | Desktop compilation, CPU tests, GLSL validation; strict warnings and IEEE math |
| Weekly schedule | `ci-analysis` | CPU build/tests with clang-tidy and cppcheck |
| Weekly schedule | `ci-release` | CPU build/tests with LTO and fast-math, including per-target IEEE overrides |
| Manual dispatch | Selected preset | Replay any lane against a selected ref |

The hosted CPU lanes establish compilation and executable CPU validation.
CUDA device execution, desktop OpenGL rendering, and Blender/Octane runtime
qualification require their corresponding hardware and environments.

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
