# Debt Ledger and Remediation Roadmap

**Last Updated:** 2026-07-09
**Baseline:** commit c1a1118 (main, clean tree)
**Owner docs:** `backlog.md` (issue table), `status.md` (current state),
`repo-truth.md` (generated counts). This ledger owns debt classification and
the remediation ordering; when an item ships, it moves to `status.md` history.

This ledger records every debt class found by a full-repo audit (five scoped
sweeps: deferred-work markers, build/package/workspace, tests/verification,
docs/organization, structure/architecture) plus an instrumented capture
(cscope cross-reference, lizard complexity, scc metrics; see Appendix A).
Every finding carries file:line evidence gathered at the baseline commit.

Naming: findings are keyed by debt class (STRUCT-, TEST-, BUILD-, ORG-,
DOC-, PHYS-, METHOD-); remediation tasks are keyed by their tranche's
mechanism name (DETOX-, ABSENCE-, CANON-, FACTS-, STATE-, VERIFY-,
FIDELITY-, BLENDER-). No key needs a glossary.

---

## 1. Root-cause generators

Nearly every finding below is an instance of one of three generators. Fixing
generator instances without the generator reproduces the debt.

**Generator: silent-absence -- absence is not an error.** The build treats
missing things as silently fine: ~55 `if(EXISTS tests/...)` guards vanish a
renamed test with no diagnostic (CMakeLists.txt:3459, 3504, 3547, ...);
`find_program` silently disables coverage (gcovr, CMakeLists.txt:1722),
shader validation (glslangValidator, :1577), and Z3 verification (:4689);
dependency-gated tests (`TARGET nubhlight_pack`, :3543) skip with a STATUS
message CI never reads. Direct product: seven orphaned test sources that
never compile, including the only shader-output correctness tests
(`tests/glsl_parity_test.cpp`, `tests/gpu_cpu_parity_test.cpp`).

**Generator: copy-then-diverge.** Facts and files are duplicated, then one
copy rots: `blender_addon/` is the abandoned fork ancestor of
`blender/addon` (161 stale-only lines, every one superseded by a rewrite
on the canonical side); `src/grmhd/grmhd_streaming.cpp` is a stale 6.5KB skeleton of
the real, built `src/grmhd_streaming.cpp` (13KB, nlohmann/json); the backlog
issue table is duplicated divergently in `roadmap.md:459-476`; two phase
taxonomies coexist (CHANGELOG "Phase 10.1" vs roadmap "Phase 6 COMPLETE");
GLSL/CUDA share verbatim-copied comments that already drift
(kerr.glsl:64 vs device_physics.cuh:306).

**Generator: fanned-facts -- one fact hand-edited in N places.** A
CUDA-visible uniform touches 5-6 sites (InteropUniforms struct
src/main.cpp:1041-1078, applyInteropUniforms :1112-1153, inline
rtti.*Uniforms block :4999-5104, applyInteropComputeUniforms :1158-1207,
BH_LaunchParams src/cuda/kernel_launch.h:28, cp.* fill :5106-5193, plus
`__constant__` decls in device_physics.cuh); the synchrotron LUT domain
X_MIN/X_MAX is a literal in four files (synchrotron.h,
synchrotron_emission.glsl:88-89, device_physics.cuh:32-33, lut_texture.h)
with a comment saying "change all three together"; the 20-target
-fno-fast-math list is maintained by hand; test counts are hand-written into
three docs and disagree.

---

## 2. Debt taxonomy and findings

### 2.1 Structural debt

- STRUCT-1 (CRITICAL) `main()` at src/main.cpp:2627 is 3,046 NLOC,
  cyclomatic complexity 675, calls 871 unique functions (cscope). The
  blocker for any decomposition is the block of 233 function-local statics
  at src/main.cpp:2804-3440 -- no struct owns the render state, so every
  panel and dispatch site takes references into `main()`'s frame.
- STRUCT-2 (HIGH) Uniform plumbing fans one uniform across 5-6 hand-edited
  sites (generator: fanned-facts); string-keyed `rtti.floatUniforms["name"]`
  maps fail silently at runtime on typos.
- STRUCT-3 (HIGH) Physics triplication across three unit conventions: C++
  CGS (constants.h:58), GLSL r_s=1 uniform-driven (physics_constants.glsl:6),
  CUDA d_rs=2M (device_physics.cuh:27,44). `unit_system.h` is the only
  bridge; the synchrotron LUT domain is a 4-site literal (generator:
  fanned-facts).
- STRUCT-4 (HIGH) Kerr-Schild coordinates exist only in GLSL
  (shader/include/kerr_schild.glsl); no C++ oracle, no CUDA port. The GLSL
  tests validate against C++ tests of formulas the shader re-derives, not
  against a shared source.
- STRUCT-5 (MED) Duplicate module: src/grmhd/grmhd_streaming.{cpp,h} is a
  stale skeleton; CMake builds only src/grmhd_streaming.cpp
  (CMakeLists.txt:1130). src/gpu reaches upward via `../grmhd_streaming.h`
  includes. DONE 2026-07-09: src/grmhd/ no longer exists in the tree;
  src/grmhd_streaming.{cpp,h} is the single module.
- STRUCT-6 (MED) Vendored code inside src/: imgui_impl_glfw.cpp,
  imgui_impl_opengl3.cpp carry all 13 FIXME and all 14 XXX markers in the
  repo and pollute first-party complexity metrics (CCN-120 function).
- STRUCT-7 (MED) src/physics/physics_test.cpp is a test living in src/;
  gravitational_waves.h is a 1,478-line all-inline header (compile cost);
  stokes_transport.h 749L, batch.h 740L template-heavy.
- STRUCT-8 (LOW) Layering is otherwise clean: physics and cuda are leaves,
  no include cycles; blender_bridge depends one-way on core (8 physics
  headers + kernel_launch.h via fragile `../` relative paths); core never
  includes blender_bridge.
- STRUCT-9 (HIGH, found 2026-07-09 while resurrecting orphaned tests)
  src/physics/verified/ carries parallel .h and .hpp forks of the same
  four headers (kerr, schwarzschild, rk4, geodesic) plus kerr_extended.h
  -- a copy-then-diverge instance that incubated real physics bugs: the
  .h fork's bptZ1 carried a spurious /2 (prograde ISCO 3.48M instead of
  6M at a=0, LIVE in the shipped batch tracer via batch.h:140),
  kerr_extended.h did not compile at all and additionally had a wrong
  bptZ2 radicand (6.87M ISCO) and a retrograde ISCO returning the
  prograde radius (Z1/Z2 are even in a, so its -a trick selected
  nothing). All fixed 2026-07-09 and pinned by kerr_geodesic_test and
  verify_headers_compile value checks. MERGED 2026-07-09: the .h fork
  (kerr.h, schwarzschild.h, rk4.h, geodesic.h) is deleted; the snake_case
  .hpp Rocq-extraction set plus kerr_extended.h and axiodilaton.h are the
  canonical surface. A full diff before deletion found four more .h-fork
  defects that never reached a build: radialAcceleration used +Gamma^r_tt
  where the geodesic equation needs -Gamma^r_tt, geodesic.h energy()
  shadowed its own parameter `a` in a self-referential initializer,
  iscoRadiusPrograde(m, a) skipped the a/M normalization (wrong for any
  m != 1), and seven functions called snake_case names defined nowhere
  (rk4Step, integrate, carterConstant, the compute* wrappers). CLAIM
  CORRECTED: the batch.h *Verified wrappers over the buggy ISCO had zero
  callers, so the 3.48M ISCO was latent in shipped headers, not live in
  rendered output; the wrappers and both verified/ includes are removed
  from batch.h. verify_headers_compile.cpp is rewritten as a
  compile-and-value gate over all twelve remaining verified headers and
  un-quarantined (target verify_headers_compile, test
  verified_headers_gate). kerr_extended.h's re-derived
  Sigma/Delta/horizon/BPT formulas now delegate to kerr.hpp (its
  kerrIscoPrograde had also fed raw a into M=1 helpers -- the same
  normalization bug class, invisible to unit-mass pins; the gate now
  checks r_isco(2M, 2a) = 2*r_isco(M, a)), keeping only its
  range-checked wrappers plus the energy/angular-momentum/four-norm/
  validity surface kerr.hpp lacks. RESIDUAL CLOSED 2026-07-09:
  src/physics/gpu_raytracer_kernel.hpp and gpu_raytracer_wrapper.h were
  a CPU prototype of a GPU kernel with zero production consumers,
  superseded by src/cuda/; their geodesic RHS computed accelerations
  and returned the input state unchanged (a no-op integrator), so the
  pair and their test are deleted rather than resurrected.
  gpu_cpu_parity_test is rewritten and registered (target
  gpu_cpu_parity_test, test gpu_cpu_parity): it inlines the
  shader/include/verified GLSL modules via an include expander, skips
  without a GL 4.6 context, and fails on shader compile errors. Its
  first run caught real transpiler bit-rot in the auto-generated GLSL:
  eos.glsl and cosmology.glsl declared uniform-block instances where
  struct types were needed, carried `double`, bare prose lines inside
  struct bodies, static_cast/std::size_t/std::log10/std::numbers leaks,
  C++ brace-init, and a call to a nonexistent E_z(FlatLCDM) overload --
  all fixed and validated by glslangValidator plus 6/6 parity passes on
  live GL. The quarantine list now holds only the conditional entries
  (precision tests, CUDA-off).

### 2.2 Test and verification debt

- TEST-1 (HIGH) Seven orphaned test sources never build:
  glsl_parity_test.cpp, gpu_cpu_parity_test.cpp,
  gpu_raytracer_kernel_test.cpp, kerr_geodesic_test.cpp,
  verified_physics_test.cpp, verify_headers_compile.cpp,
  metric_parity_test.cpp (the last registered only by the orphan standalone
  tests/CMakeLists.txt, which root CMake never add_subdirectory's).
  noise_math_audit.cpp likewise unreferenced.
- TEST-2 (HIGH) Verification theater risk: the "verified physics" layer
  exists in four systems and none is enforced -- verified_physics_test.cpp
  orphaned; rocq/ proofs never referenced by any build file;
  z3_verification_test skipped when Z3 absent (CMakeLists.txt:4689); the
  GLSL verified/ modules stub their integrators because GLSL lacks function
  pointers (energy_conserving_geodesic.glsl:178,
  null_constraint.glsl:420,599 -- steps return unstepped state).
- TEST-3 (HIGH) CI (.github/workflows/ci.yml) is single-OS single-config
  Release; ENABLE_CUDA defaults OFF (CMakeLists.txt:341) so all 8 CUDA tests
  never run in CI; no sanitizer, coverage, fuzz, or benchmark job despite
  all options existing; fuzzers additionally require clang while CI uses gcc
  (CMakeLists.txt:5450).
- TEST-4 (HIGH) No golden-image or render-regression test exists for GL or
  CUDA output; the only shader gate is syntax-only glslangValidator
  (CMakeLists.txt:1566). scripts/compare_raw_texblackhole.py is unwired.
- TEST-5 (HIGH) safe_limits.h -- the site of the documented fast-math
  infinity()=0 workaround -- has no test; a regression silently reintroduces
  the bug class.
- TEST-6 (MED) Coverage is dead: ENABLE_COVERAGE off in CI, gcovr archived
  (commit f54f355), coverage-report target silently self-disables
  (CMakeLists.txt:1722). No measured number exists.
- TEST-7 (MED) bench/README.md documents bench/ci_bench.sh and
  scripts/check_bench_regression.py; neither file exists.
- TEST-8 (MED) Core metric/geodesic .cpp (kerr.cpp, geodesics.cpp,
  schwarzschild.cpp) have no dedicated registered unit test (only the
  physics_test runner plus orphaned dedicated files). Untested headers
  include batch.h, conservation_monitor.h, event_detection.h, lut.h,
  simd_dispatch.h, thin_disk.h, unit_system.h; src/gpu/lut_texture.h;
  render/noise_texture_cache.
- TEST-9 (MED) Test/benchmark Python harnesses are stubs that never touch
  GL: tests/gpu_parity_harness.py:142ff, tests/benchmark_raytracer.py:157ff
  return constants.
- TEST-10 (LOW) tests use -Werror with a hand -Wno-stack-usage escape
  (CMakeLists.txt:3474); brittle across compiler upgrades.

### 2.3 Build, package, and reproducibility debt

- BUILD-1 (HIGH) No conan.lock exists; conanfile.py pins direct versions
  with 9 override=True forces (conanfile.py:49-130) but transitive
  resolution is unreproducible over time.
- BUILD-2 (MED) validate() checks C++23 only when cppstd is set
  (conanfile.py:141-146); unset cppstd skips the check.
- BUILD-3 (MED) ENABLE_FAST_MATH defaults ON (CMakeLists.txt:669) while 20
  test targets hand-carry -fno-fast-math overrides and a Rocq proof tree
  checks the same numerics under IEEE semantics. The _FORTIFY_SOURCE=3
  interaction (CMakeLists.txt:1003) that motivated the pattern is
  documented only partially (status.md Phase 1.2.7 note; no CMake comment
  ties membership of the 20-target list to the root cause).
- BUILD-4 (MED) ENABLE_NATIVE_ARCH defaults ON -> -march=native binaries
  (CMakeLists.txt:427); non-portable artifacts by default.
- BUILD-5 (MED) scripts/fetch_implot.sh:4 pins vendored ImPlot to `master`;
  FetchContent deps pin tags, not SHAs (imnodes :299, autodiff :309,
  amrex :327). cfitsio is system-only via pkg-config with the conan/system
  split undocumented (CMakeLists.txt:85-100).
- BUILD-6 (MED) Hardcoded /home/eirikr paths in generate_grb_luts.py:54
  (points outside the repo), run_glsl_showcase_sweep.py:46-57,
  run_glsl_headless.py:22-27, askpass-unified.sh:13-15.
- BUILD-7 (LOW) conan/recipes carries unused tracy/0.12.2 and rmlui/4.4
  trees (conanfile requires 0.13.1 and 6.1); 5-branch elseif(EXISTS)
  toolchain probe (CMakeLists.txt:25-31). RESOLVED 2026-07-09 (recipe
  trees deleted under DETOX-8; toolchain probe remains).
- BUILD-8 (MED, found 2026-07-09 during the detox build gate) The conan
  and CMake feature gates disagree: conanfile.py required rmlui and
  tracy unconditionally while ENABLE_RMLUI and ENABLE_TRACY default OFF,
  so every default install built libraries the binary never links --
  and the rmlui build BROKE the gate when clang 22 + GCC 16 libstdc++
  rejected its bundled robin_hood.h (missing <cstdint> include).
  RESOLVED for rmlui/tracy 2026-07-09: enable_rmlui/enable_tracy conan
  options default False, matching CMake. z3 audited: its unconditional
  require is legitimately consumed by the default config --
  ENABLE_Z3_VERIFICATION defaults ON and finds the conan z3 via
  find_package(Z3 CONFIG QUIET) for z3_verification_test. OPEN:
  document the conan-option/CMake-option pairing in dependencies.md.
  Toolchain
  drift corroborated twice in one gate: highway/1.3.0 vqsort fails
  under clang 22 target-feature checks (fixed by 1.4.0), rmlui/6.1
  robin_hood under GCC 16 headers -- both are BUILD-1 lockfile-absence
  consequences.

### 2.4 Organizational / workspace debt

- ORG-1 (HIGH) infer-out/ commits SQLite WAL/SHM transients while
  .gitignore:79 ignores the dir -- the rule is a no-op for tracked files.
- ORG-2 (HIGH) blender_addon/ is the abandoned ancestor of a fork whose
  successor is blender/addon: identical file lists and LFS blob hashes,
  but 9 Python files diverge with 161 stale-only lines, all superseded by
  canonical-side rewrites (verified hunk-by-hunk 2026-07-09); pyproject
  references only blender/. RESOLVED 2026-07-09: tree removed.
- ORG-3 (HIGH) rocq/ tracks ~60 compiled proof artifacts (.vo/.vos/.vok/
  .glob/.aux, Makefile.coq*) alongside legitimate .v sources.
- ORG-4 (MED) Three dated dirs at repo root are unrelated hygiene archives
  (openmach-lites-header-stubs-20260521/, v7x86-32-vendor-subprojects-
  20260521/, repo-hygiene-sweep-20260521/) containing .tar.gz blobs tracked
  in plain git (no LFS rule for *.tar.gz); .gitattributes:9-11 already
  marks them -diff. tools/gcovr carries a vendored tarball.
- ORG-5 (HIGH) The "Blender is a separate project" boundary holds
  structurally (one-way includes) but not in the build: 516 Blender
  references in CMakeLists.txt, find_program(BLENDER_EXECUTABLE) and ~40
  BLENDER_*/DREAM_TEXTURES_* vars configured unconditionally (:1733,
  :1738-1770) ignoring ENABLE_BLENDER_BRIDGE=OFF (:379); 34 of 78 scripts/
  files are Blender/Octane/Dream-Textures integration.

### 2.5 Documentation / canon debt

- DOC-1 (HIGH) Two phase taxonomies: CHANGELOG.md:321-322 ("Phase 10.1
  complete, next Phase 11") vs roadmap.md:393 ("Phase 6 COMPLETE");
  status.md uses both (:349 vs :541).
- DOC-2 (HIGH) Test counts disagree: roadmap.md:65 ("5 tests"),
  status.md:269 ("70/70"), status.md:324 ("34/36"), roadmap.md:370
  ("53/53"); repo-truth.md:48-53 already names the generated report as
  truth.
- DOC-3 (HIGH) AGENTS.md:15 points to a root requirements.md that no longer
  exists (moved to developer-guide/dependencies.md); status.md:413 same.
- DOC-4 (MED) roadmap.md referenced five dead flat-name docs (:406,:455
  PHYSICS_MATH_LACUNAE.md -- fixed 2026-07-09; :482 DEPENDENCY_MATRIX.md;
  :560-562 CLEANROOM_PORT_MAP.md, EIGEN_REFACTOR_PLAN.md,
  IMAGE_SOURCES.md); status.md:395 lacunae dead path fixed 2026-07-09;
  CHANGELOG.md:260 MASTER_ROADMAP.md fixed 2026-07-09. gemini.md still
  points to missing root STATUS.md.
- DOC-5 (MED) backlog issue table duplicated divergently in
  roadmap.md:459-476 (ISSUE-007/-008/-012 statuses disagree); ISSUE-009
  residual figure stated three ways (roadmap.md:73 "2/12", backlog.md
  ISSUE-009 "preset 0 only", lacunae.md:481 "11/12 pass").
- DOC-6 (MED) Orphan docs: docs/raw_cuda_glsl_parity_postmortem.md,
  docs/physics/BLACKHOLE_RENDERING_NEXT_42_STEPS.md,
  docs/physics/BLACKHOLE_RENDERING_RESEARCH_2026-03-29.md (the latter two
  also violate mechanism-first naming, as does docs/plans/phases-5-6.md and
  docs/validation/phase-1.md).
- DOC-7 (MED) Superseded plans not archived: phases-5-6.md ("READY TO
  BEGIN" vs Phase 6 COMPLETE), eigen-refactor.md (all items Done), halide/
  z3 plans. CHANGELOG.md stalls at 2026-01-15. Shader-count claims disagree
  (21 vs 43 vs 26 on-disk).
- DOC-8 (LOW) Build-entry drift: README includes fetch_implot.sh step;
  AGENTS.md/building.md omit it; ctest invocation style differs. Archive
  promotion/retention policy is one sentence (index.md:84-86).
- DOC-9 (LOW) Non-ASCII characters (en-dashes, arrows, checkmarks) persist
  in older doc lines (backlog.md:19, status.md:434,449, roadmap.md:80,194,
  CHANGELOG.md:13,33, others) against the ASCII-only policy; sweep with a
  verifier so CI holds the line.

### 2.6 Physics-fidelity debt (code-level, from marker sweep)

- PHYS-0 (HIGH, found 2026-07-09 while building the safe_limits gate)
  The fast-math-safety layer was itself unsound on current compilers,
  in three layers: (a) safeIsfinite/safeIsnan/safeIsinf used
  __builtin_is* predicates that GCC 16 and clang 22 constant-fold to
  no-ops under -ffinite-math-only -- the NaN guards in batch.h:718,:730
  and raytracer.h:314 compiled to nothing in the shipped build; (b)
  clang 22 annotates by-value float parameters AND returns with
  nofpclass(inf nan), so any non-finite crossing a by-value boundary is
  poison -- empirically confirmed when a test helper returning NaN by
  value made clang thinLTO collapse main() into a jump to address zero;
  (c) 27 production sites return safeInfinity<double>() by value as a
  "no solution" sentinel (elliptic_integrals.h x6, doppler.h x4,
  hawking.h x3, newman_penrose.h x4, synchrotron.h x3, others) -- all
  latent poison in fast-math TUs under clang. RESOLVED 2026-07-09 for
  (a): classifiers rewritten to byte-level inspection via memcpy behind
  reference parameters, validated by safe_limits_test across
  gcc/clang x fast-math/IEEE. RESOLVED for (c) 2026-07-09 by consumer
  analysis + the fast-math default inversion, with the originally
  proposed migration REJECTED: tracing all 27 sites found zero
  consumers that classify the sentinel (no safeIsinf, no std::isinf,
  no comparisons) -- 9 sites propagate it arithmetically and 18 are
  never read. Under IEEE semantics (the default since the inversion)
  arithmetic propagation of a true infinity is the correct physics
  (infinite cooling time -> zero mass-loss rate; 1/inf = 0), so
  safeInfinity + propagation is the right design as-is. Migrating to
  the finite divergentResult() would silently corrupt that downstream
  arithmetic -- a regression, not a fix. Residual exposure: the five
  app-reachable arithmetic consumers (synchrotron.h:170,
  schwarzschild.cpp:139, doppler.h:55,:95,
  gravitational_waves.h:178) are unsound only under explicit
  -DENABLE_FAST_MATH=ON, which the option text now documents as
  non-IEEE. The 18 never-read sentinel producers are dead API surface
  (inventory kept in the audit record).

- PHYS-1 (MED) shader/integrator.glsl:55-58: the Kerr branch of
  geodesic_rhs() falls back to Schwarzschild ("For now, return
  placeholder"). Included only by shader/raytracer.frag (non-production;
  live path is blackhole_main.frag per src/main.cpp:4299), but the path
  exists, claims Kerr, and silently drops frame-dragging.
  geodesic_trace.comp:10 claims the stub was replaced -- true only for the
  compute path.
- PHYS-2 (MED) GLSL verified/ modules stub stepping because GLSL lacks
  function pointers: energy_conserving_geodesic.glsl:178 (never advances
  state), null_constraint.glsl:420 (constraint-after-step evaluates
  pre-step state), :599 (null-preserving RK4 returns input). Fix family:
  inline the RK4 stages as geodesic_trace_optimized.comp already does.
- PHYS-3 (MED) Approximations flagged in-source as incomplete:
  kerr_de_sitter.hpp:303 drops Lambda from the ergosphere (result equals
  pure Kerr; mirrored kerr_de_sitter.glsl:163); axiodilaton.h:24 linear
  1+z truncation; stokes_transport.h:604,642 Faraday coefficients use the
  no-Boost fallback fit with growing error at Theta_e ~ 1-3;
  gravitational_waves.h:1072 QNM table lacks modes beyond 22/21/33/44;
  generate_tardis_lut_stub.py emits a Gaussian mock spectrum consumed as
  rt_spectrum_lut.csv.
- PHYS-4 (MED) src/gpu/async_compute_pipeline.* is scaffolding:
  submitToGPU()/beginAsyncReadback() issue no GL calls (cpp:7),
  recordBufferCopy is a stub (h:137), telemetry returns hardcoded
  16.67ms/75% (cpp:17).
- PHYS-5 (LOW) bhbCudaTraceGeodesics returns -1 (CPU fallback) pending a
  per-ray path-storage kernel (blender_bridge.cpp:706); FastNoise2 cellular
  texture disabled on an upstream heap bug (noise_texture_cache.cpp:139);
  depth pre-pass UI force-disabled awaiting mesh geometry (main.cpp:2545);
  multi-viewport commented out on Wayland artifacts (main.cpp:1555).

### 2.7 Methodology debt

- METHOD-1 The marker vocabulary is misleading: zero real TODOs exist; all
  FIXME/XXX are vendored ImGui. Real deferred work hides in prose ("For
  now", "not yet", "stub", "placeholder") -- greps for standard markers
  under-report by construction.
- METHOD-2 The three generators (section 1) are process patterns, not
  one-off mistakes; the roadmap below fixes generators before instances.
- METHOD-3 cflow is not a usable call-graph oracle for this C++23 codebase
  (GNU cflow parses C; it resolves one function in main.cpp). The retained
  cscope database and -L2/-L3 queries are the working substitute
  (Appendix A).

---

## 3. Remediation roadmap

Tranches are mechanism-named and dependency-ordered. Within a tranche,
tasks are atomic (each independently verifiable). Acceptance criterion in
brackets.

### Tranche workspace-tracking-detox  (independent; do first, all mechanical)

- DETOX-1 DONE 2026-07-09. infer-out/ untracked; the pre-existing ignore
  rule now takes effect. [git status clean after a fresh infer run]
- DETOX-2 DONE 2026-07-09. 96 rocq build artifacts untracked; ignore
  rules added; 57 source/doc files remain tracked. [rocq/ tracked files
  are sources only]
- DETOX-3 DONE 2026-07-09. The final diff falsified the byte-identical
  claim: 161 stale-only lines across 9 files, each verified as the
  pre-rewrite ancestor of a canonical-side successor (quality tiers,
  Dream Textures modal flow, material variant purge). Tree deleted;
  git history retains the ancestor. [single addon tree; pyproject green]
- DETOX-4 DONE 2026-07-09. hygiene-archive branch retains the three
  dated dirs; main drops the trees, their -diff rules, and rewords the
  ignore note. [repo root contains only renderer-related dirs]
- DETOX-5 Delete stale skeleton src/grmhd/grmhd_streaming.{cpp,h}; if
  src/grmhd/ becomes the intended home, move the real files there and
  update the three CMake references plus src/gpu `../` includes in the
  same commit. [one grmhd_streaming module; build green]
- DETOX-6 Relocate vendored imgui_impl_*.{cpp,h} and
  GLDebugMessageCallback.cc to external/ (or src/vendor/) and exclude from
  first-party lint/metrics. [lizard/clang-tidy scope excludes vendored
  code]
- DETOX-7 Move src/physics/physics_test.cpp to tests/. [target still
  registered]
- DETOX-8 DONE 2026-07-09. Unused tracy/0.12.2 and rmlui/4.4 recipe
  trees deleted; the export script names only 0.13.1 and 6.1. [conan
  install green]
- DETOX-9 DONE 2026-07-09. gcovr provenance tarball converted to an LFS
  pointer; the other tarballs left with the hygiene archives. Finding
  along the way: git-lfs was never `git lfs install`ed in this clone, so
  attribute-driven conversion silently committed a raw blob on the first
  attempt (a silent-absence instance) -- fixed with `git lfs install
  --local` and verified via `git show :path`. [no plain-git tarballs]

### Tranche silent-absence-hardening  (kills generator silent-absence)

- ABSENCE-1 DONE 2026-07-09 (as a configure-time completeness gate rather than a manifest rewrite: every tests/*.cpp|.cu must be a source of some target or carry a quarantine entry with a reason; fired correctly on first run). Original task: Replace ~55 if(EXISTS) test guards with an explicit manifest
  list + a configure-time assertion that every listed file exists and every
  tests/*.cpp is either listed or explicitly excluded. [renaming a test
  breaks configure]
- ABSENCE-2 DONE 2026-07-09 for five of eight (kerr_geodesic, verified_physics, metric_parity, glsl_parity, plus safe_limits new); three quarantined against the STRUCT-9 fork merge (gpu_raytracer_kernel, verify_headers_compile, gpu_cpu_parity). Resurrection exposed the STRUCT-9 physics bugs. Original task: Register the orphaned tests: kerr_geodesic_test,
  metric_parity_test, verify_headers_compile, verified_physics_test
  (unconditional); gpu_cpu_parity_test, glsl_parity_test,
  gpu_raytracer_kernel_test (GL-gated but present in the manifest with a
  REQUIRES_GL label). Delete the vestigial tests/CMakeLists.txt standalone
  project. [ctest -N lists them]
- ABSENCE-3 DONE 2026-07-09 (bh_tool_gate: AUTO warns, ON hard-requires, OFF silent; glslang/gcovr/Doxygen/Z3; both branches script-verified). Original task: Convert find_program silent-disables into tri-state: ON
  requires the tool, AUTO warns loudly, OFF is explicit -- for gcovr,
  glslangValidator, Z3, Doxygen. [CI configure log shows an explicit
  decision per tool]
- ABSENCE-4 DONE 2026-07-09 (conan.lock, 38 pinned revisions; lockfile-aware install script; CI drift gate). Original task: Commit conan.lock; add a CI step that fails when the lockfile
  drifts from conanfile.py. [two clean-room installs resolve identically]
- ABSENCE-5 DONE 2026-07-09. Original task: Make conanfile.validate() enforce cppstd>=23 unconditionally.
  [configure fails without cppstd]
- ABSENCE-6 DONE 2026-07-09 (pinned to commit d65a2bef + sha256 log; FetchContent SHA pins remain open). Original task: Pin fetch_implot.sh to a release tag + sha256; pin FetchContent
  tags to commit SHAs. [re-fetch is byte-stable]
- ABSENCE-7 DONE 2026-07-09 (both files implemented against the real physics_bench JSON schema; behavior-tested). Original task: Either implement bench/ci_bench.sh +
  scripts/check_bench_regression.py or delete their README contract. [no
  documented-but-missing files]
- ABSENCE-8 DONE 2026-07-09. Original task: Fix hardcoded /home/eirikr paths (BUILD-6 list) to derive from
  repo root or env. [scripts run for any checkout path]

### Tranche canon-doc-reconciliation  (kills the DOC- class; COMPLETE 2026-07-09)

- CANON-1 DONE 2026-07-09. Declared in repo-truth.md. Original task: Declare one phase taxonomy in repo-truth.md (release-history
  numbering lives only in CHANGELOG; workstream numbering only in roadmap)
  or renumber; fix status.md to one scheme. [a reader can date "Phase 6"]
- CANON-2 DONE 2026-07-09 (roadmap current-state counts removed; dated history entries keep their numbers as records). Original task: Remove hand-written test/shader counts from roadmap.md and
  status.md; reference the repo-truth generated report. [zero hardcoded
  counts]
- CANON-3 DONE 2026-07-09. Original task: Delete the duplicated issue table from roadmap.md:459-476;
  backlog.md is the owner. [one issue table]
- CANON-4 DONE 2026-07-09 (link-check CI script remains open under VERIFY). Fixed: AGENTS.md:15 requirements.md ->
  developer-guide/dependencies.md; roadmap.md:482,:560-562 dead flat
  names; gemini.md STATUS.md pointer. Add a link-check script to CI.
  [zero dead intra-repo links]
- CANON-5 DONE 2026-07-09. Original task: Archive superseded plans (phases-5-6.md, eigen-refactor.md,
  halide, z3) under docs/archive/ with the stated policy; write the
  1-paragraph archive promotion/retention policy into index.md. [plans/
  contains only live plans]
- CANON-6 DONE 2026-07-09 (RESEARCH doc archived as rendering-research-notes.md; postmortem moved to gpu/). Original task: Rename phase/date-named docs mechanism-first:
  BLACKHOLE_RENDERING_NEXT_42_STEPS.md -> renderer-fidelity-tranche.md;
  BLACKHOLE_RENDERING_RESEARCH_2026-03-29.md -> archive;
  plans/phases-5-6.md -> archive; validation/phase-1.md ->
  openuniverse-import-validation.md. Link the three orphan docs from
  index.md or archive them. [index.md reaches every live doc]
- CANON-7 DONE 2026-07-09 (fetch_implot step added to AGENTS.md and building.md, matching README and the ImPlot FATAL_ERROR gate). Original task: Harmonize build entry points (fetch_implot step, ctest style)
  across README/AGENTS/building.md. [verbatim-identical core sequence]
- CANON-8 DONE 2026-07-09. Original task: Reconcile the ISSUE-009 residual figure to one statement
  (backlog owns it); update lacunae.md:481 and roadmap.md:73 to point at
  it. [single stated figure]
- CANON-9 DONE 2026-07-09 (scripts/ascii_sweep.py is sweeper and verifier; verifier green; CI wiring open under VERIFY). Original task: ASCII-only sweep of docs/ (DOC-9) plus a CI verifier rejecting
  non-ASCII in md/source outside docs/archive/.
  [grep -P '[^\x00-\x7F]' clean]

### Tranche single-source-fact-tables  (kills generator fanned-facts; prerequisite for render-state-reification)

- FACTS-1 DONE 2026-07-09 for the mechanical fan-out (struct + fragment map + compute call generated from one X-macro row in src/render/interop_uniform_registry.h, 30 uniforms; emitted name sets proven identical to the hand-written code). The CUDA fill stays deliberately explicit (semantic transforms, ABI-guarded separately); the inline rtti block at the render loop remains a candidate for a later row-migration pass. Original task: Uniform registry: one declarative table (name, type, default,
  which paths: frag/compute/cuda) that generates or drives the
  InteropUniforms struct, both apply functions, the rtti map keys,
  BH_LaunchParams fields, and the cudaMemcpyToSymbol setters. Start as a
  checked table (static assert on field counts) before full codegen.
  [adding a uniform = one table row + shader usage; typo fails at compile
  time]
- FACTS-2 DONE 2026-07-09 for the LUT domain (six literal sites, not four, now read shader/include/synchrotron_lut_domain.h across C++/CUDA/GLSL); the r_s/M convention table remains open with FACTS-3. Original task: Physics-constants table: single source for r_s/M conventions and
  the synchrotron LUT domain, emitted to C++ header, GLSL include, and
  CUDA header (build step). Kill the 4-site X_MIN/X_MAX literals. [one
  edit site; parity test asserts equality across the three emitted forms]
- FACTS-3 Document the three unit conventions in physics/unit-system.md
  with the conversion sites named, until FACTS-2 eliminates the divergence
  surface. [conventions stated where a porter looks]

### Tranche render-state-reification  (unblocks main.cpp decomposition)

- STATE-1 Reify the 233 static locals (src/main.cpp:2804-3440) into a
  RenderState struct (grouped substructs: camera, disk, grmhd, stokes,
  wiregrid, background, post). Mechanical move, no behavior change.
  [main.cpp statics block deleted; frame renders identically]
  DONE 2026-07-10 (eb52f5c + e820d66): 231 pre-loop + 60 in-loop statics
  now live in RenderState with 22 subsystem groups; member names kept
  verbatim, uses qualified as rs.group.name inside main() only. The two
  first-frame GL loads keep lazy timing behind an explicit
  baseTexturesLoaded guard. Verified by 81/81 suite, identical live-run
  log message classes vs pre-change baseline, and zero unknown-uniform
  warnings (an earlier transform draft that rewrote uniform string
  literals was caught by exactly that check). Remaining statics: two
  constexpr constants, the display panel presetIndex (STATE-3), and
  PostProcessPass quadVao (STATE-2).
- STATE-2 Extract self-contained blocks in dependency order: crash
  handlers -> src/platform/crash_handler.*; resource-root ->
  src/platform/resource_paths.*; compare harness ->
  src/tools/compare_harness.*; PostProcessPass/GpuTimer ->
  src/render/post_process.* / gpu_timing.*. [main.cpp under 4,000 lines;
  no block owns hidden statics]
  DONE 2026-07-10 (365b307 + 93383f9): crash handler (platform::),
  resource paths (platform::), GpuTimer/GpuTimerSet/TimingHistory + CSV
  writers (blackhole::), and PostProcessPass (blackhole::, quad VAO now
  a lazy member, not a static) extracted; main.cpp 6118 -> 5708. Crash
  handler verified live via SIGTERM trace. Compare harness (DiffStats,
  readback/PPM/PFM writers, compare CSVs, 12-entry ComparePreset table)
  -> src/tools/compare_harness.* (blackhole::); CameraMode -> input.h;
  InteropUniforms -> src/render/interop_uniforms.h beside its registry;
  main.cpp 5708 -> 5334. Verified by a full BLACKHOLE_COMPARE_SWEEP=1
  12-preset sweep writing both CSVs through the extracted module with
  zero threshold exceedances.
- STATE-3 Extract ImGui panels to src/ui/*.cpp taking RenderState&.
  [main.cpp under 2,500 lines]
  MOSTLY DONE 2026-07-10 (6413c66 + 4c4f6e5): RenderState +
  BackgroundAsset + WiregridParams -> src/render/render_state.h
  (blackhole::); the eight standalone panels + setupImGuiStyle +
  initializeImGui + resetLayout + applyWiregridModeProfile ->
  src/ui/panels.* (ui::); the Settings tab-bar window (Visuals/GRMHD/
  Physics/Compute) + curve overlay + bloom + tonemap + depth-effects
  panels + drawCurvePlot + loadGrmhdPacked helper ->
  src/ui/settings_window.* taking RenderState&. Integrator debug bit
  constants moved into RenderState::CompareGroup. main.cpp 5334 ->
  3374. The panels-take-RenderState& goal is met (2231ebe, under STATE-4);
  residual main-loop blocks (LUT loading, GRMHD streaming glue, recording)
  are STATE-4 territory.
- STATE-4 Extract uniform dispatch sites (frag/compute/cuda fill) into
  src/render/uniform_binding.* consuming the FACTS-1 registry. [main.cpp
  under 1,500 lines; cscope callee count of main under 300]
  FILL EXTRACTION DONE 2026-07-10 (61f1ed7 + 1739f63 + 59e8617 + 79fa39d):
  src/render/uniform_binding.* (blackhole::) now owns applyInteropUniforms,
  applyInteropComputeUniforms, applyHawkingUniforms (seed move), plus the
  three fill surfaces -- bindCudaLaunchParams (#if BLACKHOLE_HAS_CUDA),
  bindComputeUniforms, bindFragmentUniforms. All three read persistent state
  from RenderState and per-frame transients from one hoisted
  FrameBindingInputs (the *Effective compare-baseline gates, LUT readiness,
  grmhdTexId, precomputed record frame shift), populated once per frame and
  shared by all lanes. bindFragmentUniforms deletes the preliminary rtti
  writes its post-derivation pass overwrote; it deliberately LEAVES
  emissivity/redshift/photonGlow/diskDensity at the first-pass site because
  updateLuts reassigns those handles between the passes (moving them is a
  first-frame behavior change, out of scope for a mechanical move). main.cpp
  3374 -> 3146. Each commit verified by clean -Werror build, 81/81 ctest, an
  8s live-run log-class diff, zero unknown-uniform warnings, and -- for the
  compute/fragment fills -- a 12-preset BLACKHOLE_COMPARE_SWEEP=1 parity CSV
  byte-identical to the pre-STATE-4 baseline (every preset exceeded=0). The
  CUDA fill was runtime-exercised via a --record-profile cinematic run.
  PANEL HARMONIZATION DONE 2026-07-10 (2231ebe): the seven standalone panels
  (controls-settings, gizmo, display, background, wiregrid, RmlUi,
  performance) now take blackhole::RenderState& plus their genuine per-frame
  transients (GLFWwindow + extents for display, cpuFrameMs for performance),
  matching the settings_window.cpp family. Mechanical reference-alias move
  (int &cameraModeIndex = rs.camera.cameraModeIndex; ...) keeps every body
  byte-identical; eight call sites collapse from ~20 enumerated field
  references to one rs each. Verified by clean -Werror build, 81/81 ctest,
  8s live-run log-class match, zero uniform warnings (no compare-sweep:
  never touches the GPU fill path). main.cpp 3146 -> 3142.
  REMAINING to hit the 1,500-line target: move the residual main-loop glue
  (LUT load/create side effects at the top of the render block, GRMHD
  streaming, recording). Also open: the updateLuts emissivity-staleness fix
  as its own behavior-change commit.
- STATE-5 Split gravitational_waves.h (1,478L) into interface + .cpp or
  partitioned headers; measure compile-time delta. [recorded before/after
  timing in perf-tooling.md]

### Tranche verification-enforcement  (depends on silent-absence-hardening; kills the TEST- class)

- VERIFY-1 CI matrix: add jobs for (a) Debug+ASAN/UBSAN, (b) coverage with
  gcovr restored as a pinned dep and a recorded baseline percentage, (c)
  clang build so ENABLE_FUZZING compiles (smoke-run each fuzzer 60s), (d)
  a CUDA compile-only job (no GPU runner) so cuda_* targets at least
  build. [four green jobs; coverage number exists]
- VERIFY-2 Offscreen GL in CI (EGL/xvfb) so the GL-gated tests and the
  revived parity tests run headless. [gpu_cpu_parity_test green in CI]
- VERIFY-3 Golden-image harness: render N presets, compare SSIM against
  committed goldens with stated tolerance; wire
  scripts/compare_raw_texblackhole.py or replace it. [render regression
  fails CI]
- VERIFY-4 DONE 2026-07-09 (test runs deliberately WITH fast-math; drove the PHYS-0 classifier rewrite). Original task: Add safe_limits_test covering the infinity()/fast-math
  boundary; add a CMake comment at the -fno-fast-math list tying
  membership to the _FORTIFY_SOURCE=3 + -ffinite-math-only root cause.
  [test exists; list self-documents]
- VERIFY-5 DONE 2026-07-09 (IEEE default; measured: Schwarzschild 571->737ms, SIMD batch within noise, and the fast-math Kerr number was fiction -- 2000x faster by computing nothing; per-target override list kept to protect explicit opt-in). Original task: Invert fast-math polarity: ENABLE_FAST_MATH=OFF default, opt IN
  the measured-hot targets, delete the 20-target override list. Benchmark
  before/after with physics_bench to keep the perf claim honest.
  [IEEE-by-default; recorded perf delta]
- VERIFY-6 Wire one rocq proof target and the Z3 verification into an
  optional CI job so "verified" is enforced somewhere. [verification job
  exists]
- VERIFY-7 Implement real GL context in tests/gpu_parity_harness.py and
  benchmark_raytracer.py or delete them in favor of the C++ parity tests.
  [no stub harnesses that pretend to measure]

### Tranche physics-fidelity-completion  (depends on single-source-fact-tables and verification-enforcement for parity gates)

- FIDELITY-1 Wire verified::kerr_geodesic_rhs into shader/integrator.glsl's
  Kerr branch (or delete the raytracer.frag path if blackhole_main.frag is
  the only supported entry -- decide and record in gpu/scope.md). [no
  silent Schwarzschild fallback for a!=0]
- FIDELITY-2 Inline RK4 stages in the GLSL verified/ modules
  (energy_conserving_geodesic.glsl, null_constraint.glsl x2) following the
  geodesic_trace_optimized.comp pattern. [steps advance state; constraint
  drift measured post-step]
- FIDELITY-3 Add C++ Kerr-Schild oracle (src/physics/kerr_schild.h
  mirroring shader/include/kerr_schild.glsl) and extend kerr_schild_test
  to compare both. [GLSL-only mechanism gains a CPU reference]
- FIDELITY-4 Kerr-de-Sitter ergosphere: solve the full Lambda-dependent
  condition in kds_ergosphere_radius (kerr_de_sitter.hpp:303 + .glsl
  mirror). [Lambda!=0 changes the result; test added]
- FIDELITY-5 Stokes Faraday coefficients: gate exact Boost Bessel
  evaluation as the default path, keep the 1/(1+Theta_e^2) fit only for
  no-Boost builds (stokes_transport.h:604). [documented accuracy domain]
- FIDELITY-6 Extend QNM table (gravitational_waves.h:1072) with remaining
  Berti 2009 Table VIII modes actually requested by callers. [no
  valid=false for supported l<=4 modes]
- FIDELITY-7 Async compute pipeline: either implement
  submitToGPU/beginAsyncReadback GL calls + GL_TIME_ELAPSED telemetry, or
  excise the scaffold module until the render path needs it
  (src/gpu/async_compute_pipeline.*). [no hardcoded 16.67ms/75% telemetry
  in tree]
- FIDELITY-8 Replace the TARDIS mock spectrum LUT or label the output file
  itself as mock (column header), so downstream cannot mistake it
  (generate_tardis_lut_stub.py). [provenance travels with the CSV]

### Tranche blender-boundary-enforcement  (independent; policy decision first)

- BLENDER-1 Decide: enforce separation or retract the claim. If enforcing:
  gate the ~40 unconditional BLENDER_*/DREAM_TEXTURES_* CMake vars and
  find_program(BLENDER_EXECUTABLE) behind ENABLE_BLENDER_BRIDGE; move the
  34 Blender/Octane scripts under blender/scripts/; give the subproject
  its own CMakeLists consuming installed core headers instead of
  `../physics/` relative includes. [default configure mentions Blender
  zero times]
- BLENDER-2 If retracting: update the project-scope memory/doc to "in-tree
  optional target", and keep BLENDER-1's include-path cleanup only.
  [claim and build agree]

---

## Appendix A -- instrumented capture provenance (2026-07-09)

Tools: cscope 15.9 (kernel-mode xref over src/+tests/, 1.8MB db), GNU cflow
1.8 (finding METHOD-3: parses C only -- resolves 1 function in main.cpp; not
a C++ oracle), lizard (function metrics), scc (LOC/complexity).

Headline numbers at c1a1118: 66,351 code lines (C++ 28,937; headers 14,242;
GLSL 5,406; CUDA 3,985; Python 11,415; shell 1,898). main() = 3,046 NLOC,
CCN 675, 871 unique callees. 24 functions exceed CCN 15; first-party worst
after main: SettingsManager::load (90), renderControlsSettingsPanel (68),
runTests in src/physics/physics_test.cpp (68), InputManager::updateCamera
(37), physics::traceGeodesicBatch (31), loadGrmhdPackedTexture (30).
applyInteropComputeUniforms has exactly one caller (main, src/main.cpp:5237).

Capture commands are re-runnable:
`cscope -b -q -k -i <filelist>`; `lizard src --CCN 15 -w`; `scc --no-cocomo
src shader tests scripts`.
