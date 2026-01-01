# Cleanroom Decision Log

## 2025-12-31: Shared interop includes for parity
- Decision: compute and fragment parity both include `interop_raygen.glsl` + `interop_trace.glsl`.
- Rationale: single source of truth for raygen/trace/shade reduces drift.
- Tradeoff: shared code cannot use fragment-only built-ins.

## 2025-12-31: Compare baseline toggle
- Decision: add `BLACKHOLE_COMPARE_BASELINE=1` to disable disk/noise/GRMHD/background.
- Rationale: isolate integrator parity from art/asset variability.
- Tradeoff: baseline sweeps do not reflect full-frame art output.

## 2025-12-31: Compare overrides for step size/max steps
- Decision: expose `BLACKHOLE_COMPARE_MAX_STEPS` and `BLACKHOLE_COMPARE_STEP_SIZE`.
- Rationale: allow strict parity sweeps to reduce integration error.
- Tradeoff: higher step counts increase sweep time.

## 2025-12-31: Integrator debug flags
- Decision: add `BLACKHOLE_INTEGRATOR_DEBUG_FLAGS` to flag NaN/Inf and range issues.
- Rationale: quick visual validation in compare captures.
- Tradeoff: debug overlays alter output and should not be used for parity metrics.

## 2025-12-31: Timestamped flamegraphs
- Decision: `run_flamegraph.sh` writes `flamegraph_<timestamp>.svg` and updates `flamegraph_latest.svg`.
- Rationale: preserve perf history without manual file moves.
- Tradeoff: extra files accumulate under `logs/perf/flamegraph`.

## 2025-12-31: LUT asset-only mode
- Decision: add `BLACKHOLE_LUT_ASSET_ONLY=1` to skip generated LUT fallback.
- Rationale: enforce cleanroom asset parity when validating against shipped LUTs.
- Tradeoff: missing LUT assets disable LUT shading until assets are restored.

## 2025-12-31: Optional SPIR-V shader loading
- Decision: add `BLACKHOLE_USE_SPIRV=1` to load `*.spv` when available.
- Rationale: enable offline shader compilation and align with GL 4.6 pipelines.
- Tradeoff: requires .spv artifacts alongside GLSL sources.

## 2025-12-31: DrawID probe and parallel compile toggles
- Decision: add a DrawID probe (`BLACKHOLE_DRAWID_PROBE=1`) and optional
  parallel shader compile / no-error context toggles.
- Rationale: validate gl_DrawID and 4.6 runtime toggles without refactoring
  the main render path.
- Tradeoff: probe is a debug overlay; full multi-draw integration remains TBD.
