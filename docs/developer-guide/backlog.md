# Blackhole Backlog

**Last Updated:** 2026-07-09
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
| ISSUE-006: Display scaling + vsync + fullscreen | MEDIUM | Implemented (validation deferred) | Validate 720p–4K and fullscreen |
| ISSUE-007: OpenUniverse cleanroom integration | HIGH | Scoped | Audit + cleanroom ports |
| ISSUE-008: Compute raytracer path | MEDIUM | Implemented (experimental) | Kerr + LUT parity checks pending |
| ISSUE-009: Compute vs fragment compare sweep threshold failures | LOW | Root-caused | **Root cause:** RK4 integrator FP arithmetic differences (FMA contraction) between compute/fragment pipelines. Only preset 0 (Schwarzschild "Input Near" at ~4 r_s) fails with 2-4 outlier pixels out of 2M (0.0002%). Error is at rays grazing event horizon where tiny FP differences cause divergent capture/escape outcomes. **Resolution:** Expected driver behavior; adjust tolerance threshold or use strict sweep (1000 steps, 0.02 step) which passes 12/12. |
| ISSUE-010: LD_PRELOAD mklfakeintel missing | LOW | Mitigated | Added zshenv cleanup for invalid LD_PRELOAD entries; automated runs may still inherit stale env vars (clear LD_PRELOAD for CI/builds). |
| ISSUE-011: Background parallax/LOD tuning | LOW | Implemented (needs validation) | Parallax/drift persisted; per-layer LOD bias sliders added; verify visuals/perf on high-res assets. |
| ISSUE-012: TSAN clang-tidy warnings in shader.cpp | MEDIUM | Done | Zero warnings in shader.cpp and shader_watcher.cpp: added direct glbinding sub-headers, const-correctness, endl->'\n', .contains(), NOLINTNEXTLINE for intentional static/recursion. (commit 4fe1fc6, 2026-03-21) |
| ISSUE-013: spirv_bake warnings under GCC | LOW | Closed (obsolete) | spirv_bake.cpp deleted (Phase 3); CMake target removed. compile_shaders_spirv.sh still references the binary but has graceful fallback to glslangValidator. No source to warn about. |
| ISSUE-014: External dependency warnings under GCC | LOW | Scoped | fastnoise2 overflow warnings + spirv-cross deprecated lambda captures; suppress via system includes or patch recipes if Werror is enabled. |
| ISSUE-015: Orphaned test sources never built | HIGH | Scoped | Seven tests exist but no CMake target compiles them, including the only shader-output parity tests (glsl_parity_test.cpp, gpu_cpu_parity_test.cpp). Root cause: if(EXISTS) registration pattern treats absence as success. debt-ledger.md ABSENCE-1/ABSENCE-2. |
| ISSUE-016: main() god function blocks decomposition | HIGH | Scoped | main() is 3,046 NLOC, CCN 675, 871 callees; 233 function-local statics (src/main.cpp:2804-3440) are the shared-state blob every extraction depends on. debt-ledger.md tranche render-state-reification. |
| ISSUE-017: Uniform plumbing fans one fact across 5-6 edit sites | HIGH | Scoped | InteropUniforms struct + frag apply + inline rtti block + compute apply + BH_LaunchParams + cudaMemcpyToSymbol; string-keyed maps fail silently on typos. debt-ledger.md FACTS-1. |
| ISSUE-018: Workspace tracking debt | MEDIUM | Scoped | infer-out/ SQLite transients tracked against own .gitignore rule; blender_addon/ byte-identical duplicate of blender/addon; ~60 rocq build artifacts tracked; three unrelated dated hygiene dirs at root; stale src/grmhd/grmhd_streaming skeleton. debt-ledger.md tranche workspace-tracking-detox. |
| ISSUE-019: No conan lockfile | MEDIUM | Scoped | Direct pins exist but transitive resolution is unreproducible; commit conan.lock + CI drift check. debt-ledger.md ABSENCE-4. |
| ISSUE-020: Cross-path physics fact duplication | MEDIUM | Scoped | Synchrotron LUT domain literal in 4 files; three unit conventions (CGS / r_s=1 / rs=2M); Kerr-Schild exists only in GLSL with no C++ oracle. debt-ledger.md FACTS-2/FIDELITY-3. |
