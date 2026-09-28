# Development Status

The configured build report supplies the generation time, source sizes, CMake
options, registered tests, and the latest CTest execution record when present.
Run `cmake --build build/Release --target repo-truth` and read
`build/Release/reports/repo_truth.md`. The [report contract](repo-truth.md)
explains the recorded surfaces. Registered tests are inventory, not execution.

## Products

- **Blackhole Simulator / Workbench:** `src/main.cpp` owns the desktop loop;
  `src/render/render_state.h` owns renderer state. `RendererContract`
  (`src/render/renderer_contract.h`) defaults to fragment dispatch of the Kerr
  tracer in the raytracer scene.
  Compute, CUDA, and Blender paths have separate build and runtime gates. Shader compilation
  checks syntax and interfaces. The [rendered-output lane](../validation/rendered-output-lane.md)
  measures shipping pixels against analytic oracles: CI renders the Schwarzschild
  critical-curve scene on Mesa llvmpipe, and `BLACKHOLE_RENDER_FULL=1` adds the
  disk, Kerr, quality-tier, and backend scenes on a GL 4.6 GPU. The
  [promotion record](../validation/default-renderer-promotion.md) compares the
  default path with the legacy beauty tracer.
- **Singularity: GOROROBA:** `game::CampaignSession` drives the canonical
  campaign scenario. `game::ConstellationSession` owns the multi-system contest.
  `campaign_sim` and campaign/constellation tests exercise deterministic
  headless behavior. Save format version 1 is declared in
  `src/game/save_format.h`. A desktop game release also needs UI operation and
  screenshot review on a live display.

## Validation boundary

The [physics claims manifest](../physics/claims_evidence.json) declares the
class each test can support. The verifier checks file references, configured
CTest names, conditional applicability, and class coverage. The generated
`build/Release/reports/physics_claims.md` records conditional obligations.
Formula and synthetic tests do not establish renderer output or observational
calibration. The [release evidence summary](release-evidence.json) names
remaining product gates.

## Current work and history

The [debt ledger](debt-ledger.md) lists current findings. The [backlog](backlog.md)
tracks planned work. The [dated status snapshot](../archive/2026-09-27-status-history.md)
retains Blender, Octane, and earlier integration history; its old state and
counts are historical observations.
