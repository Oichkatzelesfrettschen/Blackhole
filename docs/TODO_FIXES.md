# Blackhole Backlog

**Last Updated:** 2026-01-01
**Roadmap:** See `docs/MASTER_ROADMAP.md` for consolidated execution plan
**Dependencies:** See `docs/DEPENDENCY_MATRIX.md` for version tracking

This file is a lightweight backlog only. For current state, recent changes, and
active plans, see `STATUS.md`.

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
| ISSUE-012: TSAN clang-tidy warnings in shader.cpp | MEDIUM | Mitigated | include-cleaner + non-const globals + readability/perf warnings cleaned; recheck under clang + riced-tsan after next sweep. |
| ISSUE-013: spirv_bake warnings under GCC | LOW | Scoped | -Wstack-usage warning in main (CLI11 stack use); clean up for Werror builds. |
| ISSUE-014: External dependency warnings under GCC | LOW | Scoped | fastnoise2 overflow warnings + spirv-cross deprecated lambda captures; suppress via system includes or patch recipes if Werror is enabled. |
