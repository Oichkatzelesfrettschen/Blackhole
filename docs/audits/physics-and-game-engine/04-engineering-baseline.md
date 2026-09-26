# Engineering baseline audit -- Blackhole

Scope: measured state of the build, test, CI, static-analysis, and hygiene
baseline at HEAD `34e1bf1` (2026-09-22 19:28 -0700), against
`/home/eirikr/Github/Blackhole`. No source edit, no `.gitignore`/`.ignore`
change, and no compilation was performed by this audit. One caveat: the
prescribed command `ctest --test-dir build/Release --output-on-failure -j8`
itself invokes five test targets that shell out to `cmake --build
${CMAKE_BINARY_DIR} --target X` (CMakeLists.txt:1774, 3100, 3111, 3128,
3139). Because `CMakeLists.txt` is 24 commits newer than the tree's last
configure, each of those five triggered `make`'s automatic
`cmake_check_build_system` reconfigure, which failed partway through
(`find_package(imgui)` error) and touched `build/Release/CMakeCache.txt`
plus these 7 files under `build/Release/CMakeFiles/`, all with a
2026-09-25 15:34 mtime: `cmake.check_cache`, `CMakeConfigureLog.yaml`,
`4.4.3/CMakeSystem.cmake`, `4.4.3/CMakeCXXCompiler.cmake`,
`4.4.3/CMakeDetermineCompilerABI_CXX.bin`,
`4.4.3/CompilerIdCXX/CMakeCXXCompilerId.cpp`,
`4.4.3/CompilerIdCXX/a.out`. All 7 are CMake's own compiler-detection
bootstrap files, not project object files or CMake's per-target
`*.dir/` build directories. The 14 cached option values recorded in the
pre-existing `build/Release/reports/repo_truth.json` (generated
2026-07-24, before today) match the same 14 keys read from
`build/Release/CMakeCache.txt` after today's run exactly (`BUILD_TESTING`,
`CMAKE_BUILD_TYPE=Release`, `ENABLE_CUDA=ON`, `ENABLE_WERROR=ON`, and 10
others). No project source file was recompiled or relinked
(`find build/Release -maxdepth 1 -newermt "2026-09-25 00:00" -type f`,
excluding `CMakeCache.txt`/`reports/`, returns nothing). The tree was not
rebuilt, but running the audit's own prescribed test command left CMake's
bootstrap metadata touched -- recorded here rather than asserted away.

## Facts table

| Item | Measured value | Source command | Matches docs? |
| --- | --- | --- | --- |
| HEAD commit | `34e1bf1`, 2026-09-22 19:28:32 -0700 | `git log -1 --format='%H %ci'` | -- |
| Build cache age (before ctest run) | `build/Release/CMakeCache.txt` mtime 2026-07-19 14:24:29 -0700; binaries mtime up to 2026-07-23 17:43 | `stat`, `ls -la build/Release` | status.md does not claim build freshness; build is stale, see Finding 1 |
| Commits since build | 24 commits between build cache and HEAD | `git log --oneline --since=@1784496269` | -- |
| Other build trees | `build/` holds only `Release`, `FastMathCheck` (2026-07-11, an unrelated one-off probe), and `ci-evidence`; no `build/Dev`, `build/CI`, `build/CI-Analysis`, `build/CI-Release`, or `build/Riced` tree exists locally | `ls -la build/`, `find build -iname CMakeCache.txt` | confirms `build/Release` is the only candidate baseline on this host |
| cmake | 4.4.3 | `cmake --version` | -- |
| ctest | 4.4.3 | `ctest --version` | -- |
| clang++ (local `release` preset toolchain) | 22.1.8; confirmed as the tree's actual compiler two ways: `CMAKE_CXX_COMPILER_AR=/usr/bin/llvm-ar` in `CMakeCache.txt`, and `/usr/bin/clang++ ...` as the literal compiler invocation in `build/Release/compile_commands.json`'s first entry | `clang++ --version`; grep of `CMakeCache.txt`; `compile_commands.json[0].command` | matches MEMORY.md note "BUILD COMPILER = clang++ 22" (project memory, not AGENTS.md) |
| gcc (CI compiler for every lane) | `conan/profiles/ci` pins `compiler=gcc`, `compiler.version=14`, `tools.build:compiler_executables={"c":"gcc-14","cpp":"g++-14"}`; `.github/workflows/ci.yml`'s single `conan install` step passes `-pr:a conan/profiles/ci` once, shared by the `[ci, ci-analysis, ci-release]` matrix, and the ccache cache key literally encodes it: `ccache-ubuntu24-gcc14-${{ matrix.preset }}-...` | `cat conan/profiles/ci`; `grep -n "profiles/ci\|gcc14" .github/workflows/ci.yml` | ci.md states this ("Conan and CMake use GCC 14 through `conan/profiles/ci`") -- confirmed for all three lanes |
| nvcc | Cuda 13.4, `cuda_13.4.r13.4` | `nvcc --version` | -- |
| glslangValidator | 16.4.0 | `glslangValidator --version` | -- |
| cppcheck | 2.21.1 | `cppcheck --version` | -- |
| include-what-you-use | not installed | `which include-what-you-use` | consistent -- IWYU never required by CI or the local `release` preset |
| ctest total | 93 tests | `ctest --test-dir build/Release -N` and the stale `repo_truth.json` (generated 2026-07-24) both report 93 | status.md deliberately does not hardcode a count ("release-tree test count is tracked in repo truth") -- accurate hedge |
| ctest pass/fail | 83 passed, 10 failed (89%) | `ctest --test-dir build/Release --output-on-failure -j8` | -- |
| ctest skipped/disabled | 0. All 93 registered tests executed (83 + 10 = 93, no gap); `grep -n "DISABLED\|SKIP_RETURN_CODE" CMakeLists.txt` finds no such property anywhere in the tree | ctest log (`83 passed`/`10 failed`, no "Not Run" entries); CMakeLists grep | -- |
| CUDA-labeled tests | 8/93 (label `cuda`), all passed | `ctest -N -L cuda` | matches memory "8 CUDA on SM8.9" |
| GPU/GL/parity-labeled tests | label `gpu` (5): `grmhd_pbo_state_machine`, `gpu_cpu_parity`, `gpu_compute_validation`, `grmhd_gpu_async_validation`, `z3_verification`; label `parity` (5): those plus `math_types_parity`, `metric_parity_validation`, `glsl_parity_validation`, `cuda_geodesic_orbit`; label `compute` (1): `gpu_compute_validation`; label `blender` (covers the 5 meta-build tests that failed today, see Finding 1). All GPU-labeled tests passed on this host, which has a live GL 4.6 context and a CUDA-capable GPU. `z3_verification` carries the `gpu` label despite being an SMT (Z3) proof check -- a label-taxonomy quirk, not a claim this audit resolves. | `ctest --print-labels`; `ctest -N -L gpu\|parity\|compute\|blender` | matches memory "gpu_cpu_parity 6/6 GLSL-vs-C++ on live GL 4.6" |
| CI workflow files | 1: `.github/workflows/ci.yml` (170 lines); 2 other "workflows" from `gh api .../workflows` are GitHub-managed Copilot PR-review agents, not test gates | `gh api repos/.../actions/workflows` | -- |
| Branch protection required checks | `ci`, `ci-analysis`, `ci-release`; `enforce_admins=true`; `required_approving_review_count=0`; `required_conversation_resolution=true` | `gh api repos/.../branches/main/protection` | matches status.md and ci.md claims exactly |
| Latest main run (34e1bf1, run #79, id 35810499042) | `ci` success, `ci-analysis` success, `ci-release` success | `gh api .../actions/runs/35810499042/jobs` | matches "green locally" / required-checks claim |
| `ci` preset flags | `ENABLE_CUDA=OFF`, `ENABLE_FAST_MATH=OFF`, `ENABLE_CLANG_TIDY=OFF`, `ENABLE_CPPCHECK=OFF`, `ENABLE_WERROR=ON`, `WARNING_LEVEL=5`, `ENABLE_SHADER_VALIDATION=ON`, `SIMD_TIER=SSE2` | `CMakePresets.json` | matches ci.md table row for `ci` |
| `ci-analysis` preset flags | inherits `ci` + `ENABLE_CLANG_TIDY=ON`, `ENABLE_CPPCHECK=ON` | `CMakePresets.json` | matches ci.md |
| `ci-release` preset flags | inherits `ci` + `ENABLE_LTO=ON`, `ENABLE_FAT_LTO=ON`, `ENABLE_FAST_MATH=ON` | `CMakePresets.json` | matches ci.md |
| ASAN/UBSAN/TSAN/coverage/fuzzing/IWYU/GCC-analyzer/CUDA in CI | none of the 3 CI presets enable any of these; they exist only in local-only presets `asan`, `tsan`, `coverage`, `fuzz`, `analyze-full`, `cuda-only`, absent from `.github/workflows/ci.yml`'s matrix (`["ci","ci-analysis","ci-release"]`, line 34) | `CMakePresets.json` matrix vs `ci.yml` matrix | ci.md states this scope explicitly and correctly |
| Local `build/Release` preset used | `release`: `ENABLE_CUDA=ON`, `ENABLE_FAST_MATH=ON`, `ENABLE_CLANG_TIDY=ON`, `ENABLE_CPPCHECK=ON`, `ENABLE_WERROR=ON`, `ENABLE_LTO=ON`, `WARNING_LEVEL=5` (`CMakeCache.txt`, cross-checked against `repo_truth.json`'s `configured_build`) | grep of both files | -- |
| `ENABLE_FAST_MATH` default | `OFF` (CMakeLists.txt:677) | `grep option(ENABLE_FAST_MATH` | matches memory "ENABLE_FAST_MATH defaults OFF" |
| `ENABLE_WERROR` default | `ON` (CMakeLists.txt:899) | grep | -- |
| `ENABLE_CLANG_TIDY` / `ENABLE_CPPCHECK` defaults | both `ON` (CMakeLists.txt:1521-1522) | grep | overridden `OFF` by the `ci` preset, `ON` again by `ci-analysis`. clang-tidy always parses with the Clang frontend regardless of which compiler builds the project, so `ci-analysis`'s clang-tidy coverage is not GCC-14-limited; only the compiler's own `-Werror` diagnostics are GCC-14-only in CI (see Finding 3) |
| `-fno-fast-math` per-target overrides | 34 `target_compile_options` sites, 37 textual hits | `grep -c fno-fast-math CMakeLists.txt` | matches memory pattern (grown from ~10 named files to 34 sites as more tests were added) |
| `.clang-tidy` | present, `bugprone-*`, `cert-*`, `clang-analyzer-*`, `cppcoreguidelines-*`, `misc-*`, `modernize-*`, `performance-*`, `portability-*`, `readability-*`, with an explicit suppression list | `.clang-tidy` | -- |
| `RESOURCE_LOCK` / `RUN_SERIAL` on the 5 `cmake --build`-invoking meta ctest targets | none. `grep -n "RESOURCE_LOCK\|RUN_SERIAL" CMakeLists.txt` returns 0 hits anywhere in the file | grep | see Finding 7 |
| AGENTS.md build commands | `conan_install.sh`, `fetch_implot.sh`, `cmake --preset release`, `cmake --build --preset release --target validate-shaders`, `ctest --test-dir build/Release` all exist and resolve | file existence + `CMakePresets.json` preset-name check | matches |
| Repo-local Conan cache (`.conan/p/`) | `cache.sqlite3` (28,672 bytes) with 0 rows in both its `recipes` and `packages` tables; no package folder tree exists (`.conan/p/b/` absent) | `sqlite3 .conan/p/cache.sqlite3 "SELECT count(*) FROM recipes"` / `... FROM packages` both 0; `find .conan/p -maxdepth 2 -type d` | root cause of 10 ctest failures, see Finding 1 |
| `.conan/` metadata mtimes | `settings.yml`, `version.txt`, `migrations/`, `extensions/`, `p/cache.sqlite3` all dated 2026-09-21 23:43:37-38 (same run); `global.conf`, `remotes.json` dated 2026-08-13 14:09:47 | `stat -c '%y %n' .conan/*` | pattern consistent with a `CONAN_HOME` re-initialization on 2026-09-21, not a `conan cache clean` |
| `conan cache clean` scope | `--source --build --download --temp` removes only source/build/download/temp scratch folders; it does not remove the `.../p/b/...` installed-package folders that the dangling `RUNPATH` entries point at | `conan cache clean --help` | rules out `ci.yml:123`'s `conan cache clean '*' --source --build --download --temp` as the mechanism -- see Finding 1 |
| `git lfs ls-files` | 120 files | `git lfs ls-files \| wc -l` | -- |
| `git count-objects -vH` | 456.00 KiB loose, 44.78 MiB in 4 packs, 6322 in-pack objects, 0 garbage | `git count-objects -vH` | healthy, no bloat |
| Largest tracked blobs | skybox PNGs ~2.7-4.0 MB each; `docs/blackhole-screenrecord.gif` 3.0 MB; `carina-cosmic-cliffs-4k.jpg` 2.3 MB; `crab-nebula-4k.jpg` 2.6 MB; `gcovr-python-8.4-vendored-source.tar.gz` 1.9 MB | `git rev-list --objects --all \| git cat-file --batch-check` sorted | matches memory: carina/crab are plain blobs, not LFS |
| `carina-cosmic-cliffs-4k.jpg`, `crab-nebula-4k.jpg` LFS status | `filter: unspecified` -- plain git blobs, not in `git lfs ls-files` | `git check-attr filter <path>` | matches memory ledger `gororoba-rename-lfs-budget` |
| Stray build artifacts (`CMakeFiles/`, `infer-out/`, `logs/`, `imgui.ini`, `settings.json`) | all present on disk, all matched by `.gitignore` rules, none tracked | `git ls-files --error-unmatch`, `git check-ignore -v` | clean |
| `gemini.md` | tracked, 227 bytes, thin pointer to AGENTS.md (mirrors `CLAUDE.md` symlink pattern) | `git ls-files`, `cat gemini.md` | intentional, not stray |
| `scripts/ascii_sweep.py` default scope | when run with no path arguments, it walks `(root/"docs").rglob("*.md")` excluding any path containing `archive`, plus exactly `AGENTS.md`, `README.md`, `CHANGELOG.md`, `gemini.md`, `CLAUDE.md` at repo root. It does **not** by default touch `src/`, `tests/`, `scripts/`, `tools/`, or `rocq/`. | `sed -n '85,105p' scripts/ascii_sweep.py` | see Finding 5 -- narrows what "verifier green" in the debt ledger can mean |
| Non-ASCII hits inside `scripts/ascii_sweep.py`'s own default scope (`docs/*.md` excl. archive) | 0 | `git grep -cP '[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]' -- 'docs/**/*.md' ':(exclude)docs/archive/**'` | confirms `docs/developer-guide/debt-ledger.md:476`'s "verifier green" is accurate for the tool's actual, narrower scope |
| `ascii_sweep.py` CI wiring | not referenced by `.github/workflows/ci.yml`, `.pre-commit-config.yaml`, or `CMakeLists.txt` (0 hits) | grep of those three files | `docs/developer-guide/debt-ledger.md:476` self-documents this: "scripts/ascii_sweep.py is sweeper and verifier; verifier green; CI wiring open under VERIFY" -- the tool's own docstring claim ("which is how CI holds the line") is an overclaim independent of scope, since nothing invokes it automatically anywhere |
| Symbol-range hits outside `docs/archive/`, expanded scan (`.md .cpp .h .hpp .py .cmake .txt .yml .yaml .glsl .comp .frag .vert .cu .cuh .sh`) | 217 matching lines across 24 files, 213 lines / 23 files when `scripts/ascii_sweep.py`'s own translation table is excluded (up from 191/20 files in a narrower first pass limited to `.md/.cpp/.h/.hpp/.py`) | `git grep -cP '[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]' ... \| awk -F: '{s+=$2}'`, with and without `:(exclude)scripts/ascii_sweep.py` | see Finding 5 -- includes genuine pictographic emoji, not just status-mark glyphs |
| Genuine pictographic emoji found | `scripts/build-quick.sh` lines 29, 35, 40, 49, 55: U+1F9F9 (broom), U+1F4E6 (package), U+2699 (gear), U+1F528 (hammer), U+2705 (check mark button) | `grep -noP '[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]' scripts/build-quick.sh` | violates the user's global "checked-in text is emoji-free" rule; outside `ascii_sweep.py`'s own scan scope so its default run would not catch it |
| Em dash / curly quotes / ellipsis / en dash in tracked text (expanded scan) | all hits confined to `scripts/ascii_sweep.py`'s own translation table (2 lines, 26-27) and one exempt line in `docs/archive/phases/PHASE9_COMPLETE.md` | `git grep -nP` for U+2014, U+2018/19/1C/1D, U+2026, U+2013 with the expanded extension list | clean outside the enforcement tool's own data and the archive |
| New-file copyright headers (last 30 commits, 85 added files) | 0 source files add a copyright/SPDX header; 4 hits are upstream font provenance files (`OFL.txt`, `AUTHORS.txt`, etc.) | `git log --diff-filter=A` + grep | matches rule: no invented attribution, upstream headers preserved |
| `src/cuda/` size | 6,144 lines across 17 files | `find src/cuda -type f -name '*.h' -o -name '*.hpp' -o -name '*.cu' -o -name '*.cuh' -o -name '*.cpp' \| xargs wc -l` | close to memory's "~4700 LOC" estimate but measured higher; the measured figure is used above |
| `status.md` "Known issue: z3_verification_test has googletest linker error" (line 551) | Sits under the dated section header "Shader Validation & Transpilation Fixes (2026-01-15)" (line 507), i.e. it is a historical changelog entry, not a live claim. `z3_verification` (ctest #73) passed in today's run (3.13s). This is not a live doc/reality contradiction -- it is a resolved historical note correctly scoped to its own date header. | `sed -n '490,552p' docs/developer-guide/status.md`; ctest log line "93/93 Test #73: z3_verification ... Passed 3.13 sec" | status.md's changelog-style dating is doing its job here; flagged only to show the check was run, not as a finding |
| Benchmark baseline | `bench/baseline-riced.json` not committed; `scripts/check_bench_regression.py --allow-missing` is hardcoded inside `bench/ci_bench.sh` (not an ad hoc flag); `bench/ci_bench.sh` is not referenced anywhere in `.github/workflows/ci.yml` | `git ls-files \| grep baseline`, `grep ci_bench .github/workflows/ci.yml`, `bench/ci_bench.sh` | see Finding 4 |
| `bench/ci_bench.sh` vs the `riced` preset | the script runs `cmake --preset riced` directly, with no prior `conan install` for that preset's output folder; `build/Riced/Debug/generators/conan_toolchain.cmake` does not exist on this host, so the configure step the script depends on would fail before the script's own binary-path lookup (`./build/Riced/physics_bench`, then `./build/riced/physics_bench`) is even reached. Neither of those two paths matches the preset's real `binaryDir`, `${sourceDir}/build/Riced/Debug` (`CMAKE_BUILD_TYPE=Debug`). `CMakeLists.txt` sets no `RUNTIME_OUTPUT_DIRECTORY` (0 hits), so `physics_bench` would land directly under `binaryDir` if the build succeeded, not under either path the script checks. | `ls build/Riced/Debug/generators/conan_toolchain.cmake` (missing); `CMakePresets.json` `riced` entry; `grep -n RUNTIME_OUTPUT_DIRECTORY CMakeLists.txt` (0 hits) | neither path the script checks exists -- see Finding 4 |
| `bench/README.md` numbers | sample console-output block (rays/s, ms, speedup) with no CPU model, compiler flags, or date attached | `bench/README.md:104-153` | illustrative only, not a recorded run |

## Ranked findings

1. **All 10 local ctest failures share one root cause: the repo-local Conan
   package cache is empty, and `build/Release`'s binaries and Conan-generated
   CMake files still point at package paths that no longer exist.**
   `.conan/p/cache.sqlite3` has 0 rows in `recipes` and 0 in `packages`
   (verified via `sqlite3`), and `find .conan/p -maxdepth 2 -type d` finds
   nothing under `.conan/p/b/`. `readelf -d build/Release/camera_math_test`
   shows a `RUNPATH` entry
   `/home/eirikr/Github/Blackhole/.conan/p/b/hdf57e5dc28c5385b/p/lib`,
   which does not exist on disk -- hence `error while loading shared
   libraries: libhdf5_hl_cpp.so.310: cannot open shared object file` for
   `settings_sync`, `compare_sweep_state`, `camera_math`,
   `grmhd_pack_fixture`, `grmhd_hdf5_loader`. Separately,
   `shader_validation`, `repo_truth_generation`, `physics_claims_matrix`,
   `blender_addon_package`, `blender_addon_stage` each invoke `cmake
   --build ${CMAKE_BINARY_DIR} --target X`; because `CMakeLists.txt` is 24
   commits newer than the 2026-07-19 configure, `make` auto-reconfigures on
   every invocation and fails at `find_package(imgui)` ("Library 'imgui'
   not found in package") because the Conan-generated
   `imgui-Target-release.cmake` points at
   `.conan/p/b/imgui4027d16bef573/p/lib`, also gone.
   Observed: empty package cache, dangling `RUNPATH`, dangling
   `find_package` path, and 10/10 failures explained without residue. The
   mechanism is *not* `ci.yml:123`'s `conan cache clean '*' --source
   --build --download --temp` -- `conan cache clean --help` documents that
   flag combination as removing only source/build/download/temp scratch
   folders, never the installed `p/b/...` package folders those `RUNPATH`
   entries reference, and that step runs on GitHub-hosted runners, not
   this host. The stronger signal is timing: `.conan/settings.yml`,
   `version.txt`, `migrations/`, `extensions/`, and `p/cache.sqlite3` all
   carry the same 2026-09-21 23:43:37-38 mtime, while `global.conf` and
   `remotes.json` are from 2026-08-13 -- a pattern consistent with
   `CONAN_HOME` (`.conan/`, per `scripts/conan_env.sh:6`) having been
   deleted and re-initialized on 2026-09-21, one day before the HEAD
   commit and four days before this audit, leaving `build/Release` (last
   built 2026-07-23) orphaned from the packages it links against. No shell
   history or log was available to name the exact command; this mechanism
   is inferred from filesystem timestamps, not observed directly. Fix:
   repopulate the cache and refresh the build tree together --
   `./scripts/conan_install.sh Release build && cmake --preset release &&
   cmake --build --preset release` -- then rerun ctest. Falsifier: if the
   same 10 tests still fail with the same messages after that rebuild, the
   empty-cache hypothesis is wrong.

2. **The measured pass rate (83/93, 89%) is not evidence of 10 code
   regressions across the 24 unbuilt commits.** Every failing test's error
   text is a link-time or configure-time environment failure, not an
   assertion failure inside test bodies -- zero of the 10 failures printed
   a test assertion, physics-tolerance, or numeric-mismatch message. The
   stale `build/Release/reports/repo_truth.json` (generated 2026-07-24)
   already reports `total: 93`, identical to today's count, so the test
   suite itself has not grown or shrunk since the last known-good full
   build; there is no evidence in this pass that any of the 24 intervening
   commits (which include "enforce strict verified-source and GLSL
   interface gates" and "replace tautological validation") broke a test.
   Falsifier: after the rebuild in Finding 1, a still-failing test with a
   physics/logic assertion message would be a real regression to chase
   down from that commit range.

3. **CI never builds or tests the CUDA backend, never runs
   ASAN/UBSAN/TSAN/coverage/fuzzing/IWYU/GCC-analyzer, and its compiler
   `-Werror` gate is GCC-14-only.** `CMakePresets.json` shows `ci`,
   `ci-analysis`, and `ci-release` (the three required branch checks) all
   set `ENABLE_CUDA=OFF`; the sanitizer/analyzer/coverage/fuzz options
   exist only on presets (`asan`, `tsan`, `coverage`, `fuzz`,
   `analyze-full`) absent from `.github/workflows/ci.yml`'s matrix
   (`["ci","ci-analysis","ci-release"]`, line 34). `conan/profiles/ci`
   pins `gcc-14`/`g++-14` and is applied identically to all three matrix
   lanes in one shared `conan install -pr:a conan/profiles/ci` step, so
   every CI compiler diagnostic, in particular `-Werror`, is GCC-14's
   warning set, never Clang's -- the local `build/Release` tree (and
   ordinary local iteration, per MEMORY.md) instead builds with Clang 22.
   clang-tidy is not affected by this split: it always parses with its
   own bundled Clang frontend regardless of which compiler actually
   builds the project, so `ci-analysis`'s clang-tidy coverage is real and
   not weakened by the GCC-14 build compiler. This is not a doc/reality
   mismatch -- `docs/developer-guide/ci.md` states the CUDA/GPU/Blender/
   Octane limitation plainly and correctly names the GCC 14 profile.
   Recorded as a finding because it means 6,144 lines of CUDA
   (`src/cuda/`, 17 files, 8 CUDA ctest entries), every sanitizer/coverage/
   fuzz lane, and any Clang-specific `-Werror` diagnostic depend entirely
   on a developer's local machine and memory to run at all -- there is no
   server-side gate for any of them. Falsifier: a future `ci.yml` diff
   adding a CUDA, ASAN, coverage, or Clang-compiler job to the
   required-checks matrix would retire part of this finding.

4. **The benchmark regression gate cannot currently produce a result:
   it is not wired into CI, has no committed baseline, and its own driver
   script cannot reach a built binary.** `bench/ci_bench.sh` is not
   referenced anywhere in `.github/workflows/ci.yml` (`grep ci_bench
   .github/workflows/ci.yml` returns nothing), so nothing currently
   invokes it automatically. The script runs `cmake --preset riced`
   directly with no preceding `conan install` for that preset's output
   folder; on this host `build/Riced/Debug/generators/conan_toolchain.cmake`
   does not exist, so that configure step would fail immediately on a
   clean checkout, before the script ever reaches its benchmark-JSON or
   regression-check logic. Even past that, the script checks for the
   binary at `./build/Riced/physics_bench` then `./build/riced/physics_bench`;
   the `riced` preset's actual `binaryDir` per `CMakePresets.json` is
   `${sourceDir}/build/Riced/Debug`, and `CMakeLists.txt` sets no
   `RUNTIME_OUTPUT_DIRECTORY` override (0 hits), so the binary would land
   at `build/Riced/Debug/physics_bench` -- a third path, matching neither
   of the two the script checks. `riced` also inherits `debug`
   (`CMAKE_BUILD_TYPE=Debug`), the wrong build type for a performance
   regression measurement even once the path is fixed. Independent of all
   of the above, no `bench/baseline-riced.json` is tracked (`git ls-files
   | grep baseline` is empty), and the script hardcodes
   `scripts/check_bench_regression.py --allow-missing`, which prints a
   notice and exits 0 whenever no baseline exists -- so even a successful
   run today would not gate anything. `bench/README.md:104-153`'s
   ms/rays-per-second numbers are a sample output format, not a recorded
   run -- no CPU model, compiler version, or date is attached anywhere
   near them. Fix: add a `conan install` step for the `riced` output
   folder ahead of the configure in `bench/ci_bench.sh`, correct the
   binary path to `build/Riced/Debug/physics_bench` (or switch to a
   Release-type preset such as `riced-relwithdebinfo`), run it once on
   representative hardware, record a baseline with `python3
   scripts/check_bench_regression.py --record bench_cpu.json`, commit
   `bench/baseline-riced.json` with the CPU model and compiler version in
   the commit message, drop the hardcoded `--allow-missing` once that
   baseline exists, and add a CI job (scheduled or self-hosted, since
   GitHub-hosted runners have no stable perf floor) that invokes
   `bench/ci_bench.sh`. Falsifier: running `bench/ci_bench.sh` as-is on a
   clean checkout and getting a benchmark JSON out would mean this reading
   is wrong.

5. **The repository's documented ASCII-only policy is genuinely enforced
   within its own narrow scope, but real emoji exist just outside that
   scope, and the tool's own docstring overclaims CI enforcement it does
   not have.** `scripts/ascii_sweep.py`, run with no arguments, walks only
   `docs/**/*.md` (excluding any path containing `archive`) plus exactly
   `AGENTS.md`, `README.md`, `CHANGELOG.md`, `gemini.md`, and `CLAUDE.md`
   at repo root -- it does not touch `src/`, `tests/`, `scripts/`,
   `tools/`, or `rocq/` by default. A direct check of that exact scope
   (`git grep -cP '[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]' --
   'docs/**/*.md' ':(exclude)docs/archive/**'`) finds 0 hits, so
   `docs/developer-guide/debt-ledger.md:476`'s "verifier green" claim is
   accurate for what the tool actually scans. What is not accurate is the
   tool's own docstring: "Run without --fix as a verifier ... which is
   how CI holds the line" -- neither `.github/workflows/ci.yml`,
   `.pre-commit-config.yaml`, nor `CMakeLists.txt` references
   `ascii_sweep` at all, a gap the debt ledger's own next clause already
   names ("CI wiring open under VERIFY"). Outside that narrow default
   scope, an expanded grep across `.sh`, `.cmake`,
   `.glsl`/`.comp`/`.frag`/`.vert`, and `.cu`/`.cuh` (beyond the
   `.md`/`.cpp`/`.h`/`.hpp`/`.py` set used in a first pass) finds 213
   matching lines across 23 files under `src/`, `tests/`, `scripts/`,
   `tools/`, and `rocq/`. Most are U+2713/U+2717 (check mark/cross mark)
   used as pass/fail status markers, and U+2609 (solar mass sign, e.g.
   `src/physics/tov.h:13`) -- neither is covered by the user's global rule's
   explicit verbatim-exemption list (math operators, Greek letters in
   equations, arrows in state transitions, box-drawing, degree/micro
   signs, accented names), though U+2609 as a genuine scientific-notation
   symbol is a closer call than the status-mark glyphs and is not treated
   here as a settled violation. `scripts/build-quick.sh` (lines 29, 35,
   40, 49, 55) additionally contains unambiguous pictographic emoji --
   U+1F9F9, U+1F4E6, U+2699, U+1F528, U+2705 -- with no ambiguity at all
   under the user's rule. Fix: wire `python3 scripts/ascii_sweep.py`
   (verifier mode) into `ci.yml` or `.pre-commit-config.yaml` as the debt
   ledger already intends for its current scope, separately replace the
   pictographic emoji in `scripts/build-quick.sh` with plain text, and
   decide (as a repo-policy question, not an audit finding) whether
   U+2713/U+2717 status marks in source and test files should be
   normalized the same way `ascii_sweep.py`'s own `MAPPING` table already
   would if that file's glob were widened to include them. Falsifier:
   `git grep -cP '[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]' --
   ':(exclude)docs/archive/**'` returning 0, or `ascii_sweep` appearing in
   `ci.yml`, would retire parts of this finding.

6. **Repo hygiene is otherwise clean.** No stray tracked build artifacts
   (`CMakeFiles/`, `infer-out/`, `logs/`, `imgui.ini`, `settings.json` are
   all gitignored and untracked). No new source file in the last 30
   commits/85 added files carries an invented copyright header; the only
   copyright hits are legitimate upstream font provenance files.
   `git count-objects -vH` shows 44.78 MiB packed, 0 garbage, no runaway
   blob growth; the two de-LFS'd JWST plain blobs
   (`carina-cosmic-cliffs-4k.jpg`, `crab-nebula-4k.jpg`) remain plain blobs
   as the memory ledger records, not accidentally re-added to LFS or
   duplicated.

7. **Five ctest targets share the build tree with no lock, so a parallel
   `ctest -j` run against a stale tree races itself.**
   `shader_validation`, `repo_truth_generation`, `physics_claims_matrix`,
   `blender_addon_package`, and `blender_addon_stage` (CMakeLists.txt:1774,
   3100, 3111, 3128, 3139) each independently invoke `cmake --build
   ${CMAKE_BINARY_DIR} --target X` against the same `build/Release` tree.
   `grep -n "RESOURCE_LOCK\|RUN_SERIAL" CMakeLists.txt` finds neither
   property set anywhere in the file, so ctest is free to start several of
   these concurrently under `-j8`. Today's run demonstrates the race
   directly: `shader_validation` and `blender_addon_stage` (both started
   within the same second per the log) show a transient
   `CMake Error at /usr/share/cmake/Modules/CMakeDetermineSystem.cmake:231
   (configure_file): No such file or directory` ahead of the shared
   `imgui` failure, while `repo_truth_generation`, `physics_claims_matrix`,
   and `blender_addon_package` -- which started later, after the first
   wave's reconfigure had progressed further -- do not show that error and
   fail only at `find_package(imgui)`. Both outcomes trace back to Finding
   1's empty package cache, so this race is not today's root cause, but it
   is an independent, real defect: any `ctest -j>1` invocation on a tree
   whose `CMakeLists.txt` is newer than its configure (for example,
   immediately after a `git pull` with no rebuild, which `docs/developer-
   guide/ci.md`'s own `ctest --parallel "$(nproc)"` local-iteration
   command would trigger) risks several concurrent `cmake_check_build_system`
   reconfigures corrupting each other's transient CMake bootstrap files.
   Fix: add `RESOURCE_LOCK cmake_build_system` (or equivalent) to these
   five test properties so ctest serializes them against each other. 
   Falsifier: rerunning `ctest -j8` against a tree whose configure is
   already current with `CMakeLists.txt` (no pending reconfigure) would
   show whether the race requires a stale configure to manifest, or can
   also corrupt an up-to-date tree.

## Not run

- **Full clean rebuild** (`rm -rf build/Release && ./scripts/conan_install.sh
  Release build && cmake --preset release && cmake --build --preset
  release`): not run. Reason: task scope is a read-only audit of the
  existing baseline; a rebuild in the primary checkout was explicitly out
  of scope. This is the single highest-value follow-up -- it would confirm
  or refute Finding 1's causal chain end to end and produce a true
  post-HEAD ctest result.
- **`analyze-full` preset (IWYU + GCC `-fanalyzer`)**: not run. Reason:
  `include-what-you-use` is not installed on this machine
  (`which include-what-you-use` empty), and per `docs/developer-guide/ci.md`
  ("Requested analyzers must be installed; configuration fails when either
  executable is absent") a configure would fail immediately.
- **`asan`, `tsan`, `coverage`, `fuzz`, `riced` presets**: not run. Reason:
  out of scope for a read-only baseline audit of the existing
  `build/Release` tree; each requires its own separate configure/build
  tree the task did not authorize creating. (`riced`'s missing
  `conan_toolchain.cmake` was confirmed by a file-existence check only,
  not by attempting the configure.)
- **Re-running ctest at `-j1`** to fully isolate the reconfigure race
  (Finding 7) from the base Conan-cache failure (Finding 1): not run.
  Reason: the `RUNPATH` and `find_package` evidence in Finding 1 already
  accounts for all 10 failures independent of parallelism; a `-j1` rerun
  would only confirm which secondary CMake error string appears, not
  change the pass/fail outcome. It would, however, be the correct next
  step to isolate Finding 7 as a standalone repro once Finding 1 is fixed.
- **GitHub Actions run logs / job step timing for run 35810499042**: not
  fetched in detail beyond job-level status. Reason: `gh run watch` and
  `gh pr checks` are excluded by the task's tooling constraints (GraphQL
  quota); `gh api .../jobs` gave sufficient job-level pass/fail evidence
  for the facts table.
- **`docs/physics/lacunae.md` and `docs/physics/architecture.md`
  cross-check against `physics_claims.json`'s claim list and against
  source**: not run. Reason: task scope is the engineering baseline
  (build/test/CI/hygiene), not a physics-completeness audit. One dated
  status.md "100%"/"known issue" entry was spot-checked against today's
  ctest result (see facts table, `z3_verification` row) and found to be a
  correctly-dated historical note, not a live contradiction; the
  undated, current-tense "100%" rows in `lacunae.md` and
  `architecture.md` were located (`git grep -n '100%'`) but not
  independently re-verified against source in this pass.
- **Identifying the exact command that emptied `.conan/p/`**: not
  determined. Reason: no shell history, log file, or commit is available
  linking a specific invocation to the 2026-09-21 23:43 timestamp; Finding
  1 records the timing correlation and rules out the one CI-side
  candidate command (`conan cache clean`) but does not name the true
  cause.
