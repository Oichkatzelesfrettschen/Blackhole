# Blackhole Backlog

**Last Updated:** 2026-09-26
**Roadmap:** See `roadmap.md` for consolidated execution plan
**Dependencies:** See `dependencies.md` for version tracking
**Debt:** See `debt-ledger.md` for the audited debt taxonomy and remediation
tranches (source of ISSUE-015 through ISSUE-020)

This file is a lightweight backlog only. For current state, recent changes, and
active plans, see `status.md`.

| Issue | Priority | Status | Notes |
| --- | --- | --- | --- |
| ISSUE-001: Depth effects tuning (packed depth quality) | MEDIUM | Implemented (needs validation) | Defaults set; visual validation pending |
| ISSUE-002: Gamepad mapping ergonomics | LOW | Implemented (needs validation) | Validate Xbox/PS, add remap presets |
| ISSUE-003: Camera system unification | LOW | Done | Optional presets follow-up |
| ISSUE-004: Physics integration incomplete | LOW | Scoped | Kerr path, Doppler, frame-dragging improvements |
| ISSUE-005: Legacy settings cleanup | LOW | Scoped | Optional versioning/migration |
| ISSUE-006: Display scaling + vsync + fullscreen | MEDIUM | Implemented (validation deferred) | Validate 720p-4K and fullscreen |
| ISSUE-007: OpenUniverse cleanroom integration | HIGH | Scoped | Audit + cleanroom ports |
| ISSUE-008: Compute raytracer path | MEDIUM | Implemented (experimental) | Kerr + LUT parity checks pending |
| ISSUE-009: Compute vs fragment compare sweep threshold failures | LOW | Root-caused | **Root cause:** RK4 integrator FP arithmetic differences (FMA contraction) between compute/fragment pipelines. Only preset 0 (Schwarzschild "Input Near" at ~4 r_s) fails with 2-4 outlier pixels out of 2M (0.0002%). Error is at rays grazing event horizon where tiny FP differences cause divergent capture/escape outcomes. **Resolution:** Expected driver behavior; adjust tolerance threshold or use strict sweep (1000 steps, 0.02 step) which passes 12/12. |
| ISSUE-010: LD_PRELOAD mklfakeintel missing | LOW | Mitigated | Added zshenv cleanup for invalid LD_PRELOAD entries; automated runs may still inherit stale env vars (clear LD_PRELOAD for CI/builds). |
| ISSUE-011: Background parallax/LOD tuning | LOW | Implemented (needs validation) | Parallax/drift persisted; per-layer LOD bias sliders added; verify visuals/perf on high-res assets. |
| ISSUE-012: TSAN clang-tidy warnings in shader.cpp | MEDIUM | Done | Zero warnings in shader.cpp and shader_watcher.cpp: added direct glbinding sub-headers, const-correctness, endl->'\n', .contains(), NOLINTNEXTLINE for intentional static/recursion. (commit 4fe1fc6, 2026-03-21) |
| ISSUE-013: spirv_bake warnings under GCC | LOW | Closed (obsolete) | spirv_bake.cpp deleted (Phase 3); CMake target removed. compile_shaders_spirv.sh still references the binary but has graceful fallback to glslangValidator. No source to warn about. |
| ISSUE-014: External dependency warnings under GCC | LOW | Scoped | fastnoise2 overflow warnings + spirv-cross deprecated lambda captures; suppress via system includes or patch recipes if Werror is enabled. |
| ISSUE-015: Orphaned test sources never built | HIGH | Done | CMake rejects unregistered `tests/*.cpp` and `tests/*.cu` sources at configure time; formerly orphaned parity and verified-header tests have targets. See debt-ledger.md ABSENCE-1/ABSENCE-2 and the CMake test-source completeness gate. |
| ISSUE-016: main() god function blocks decomposition | HIGH | Partially resolved | `RenderState` owns the former static state; renderer, UI, and helper code moved to dedicated translation units. `src/main.cpp` is 1,782 lines in the 2026-09-26 checkout. Continue the remaining decomposition from debt-ledger.md tranche render-state-reification. |
| ISSUE-017: Uniform plumbing fans one fact across 5-6 edit sites | HIGH | Partially resolved | `BH_INTEROP_UNIFORM_FLOATS` generates the `InteropUniforms` fields, fragment map entries, and compute uniform calls from one registry. CUDA launch fields and semantic transforms remain explicit; see debt-ledger.md FACTS-1. |
| ISSUE-018: Workspace tracking debt | MEDIUM | Scoped | infer-out/ SQLite transients tracked against own .gitignore rule; blender_addon/ byte-identical duplicate of blender/addon; ~60 rocq build artifacts tracked; three unrelated dated hygiene dirs at root; stale src/grmhd/grmhd_streaming skeleton. debt-ledger.md tranche workspace-tracking-detox. |
| ISSUE-019: No conan lockfile | MEDIUM | Done | Tracked `conan.lock` pins dependency revisions; CI regenerates and checks the lockfile. See debt-ledger.md ABSENCE-4 and ci.md. |
| ISSUE-020: Cross-path physics fact duplication | MEDIUM | Partially resolved | The synchrotron LUT domain is shared across C++, CUDA, and GLSL. The unit-convention conversion-site inventory and the C++ Kerr-Schild oracle remain separate obligations in debt-ledger.md FACTS-3/FIDELITY-3. |
