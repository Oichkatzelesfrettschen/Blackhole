# Cleanroom Migration Worklist

Purpose: outline a staged, testable migration plan that keeps parity between
compute and fragment paths while incrementally adopting modern OpenGL 4.6
features.

## Phase 0: Agreement on scope
- Freeze a minimal feature set for parity sweeps (no art toggles).
- Gate all cleanroom changes behind explicit feature flags.
- Log all decisions in `docs/CLEANROOM_DECISIONS.md`.

## Phase 1: Shader compilation pipeline (selected first subsystem)
- Add optional SPIR-V loader path (GL 4.6 core, GL_ARB_gl_spirv on 4.5).
- Keep GLSL source fallback for older drivers.
- Add build pipeline step to emit .spv alongside GLSL sources.
- Cache shader variants and specializations to avoid repeated compile work.
- Track compile/link latency (GPU timing panel or log CSV).

## Phase 2: Draw submission model
- Introduce SSBO-backed per-draw data indexed by gl_DrawID.
- Add optional multi-draw indirect path for draw batching.
- Implement indirect count path when GL 4.6 or GL_ARB_indirect_parameters
  is available.

## Phase 3: State management
- Expand DSA usage to remove bind-to-edit patterns.
- Centralize state changes to a small state cache module.
- Add explicit validation for resource lifetimes in debug builds.

## Phase 4: Shader and pipeline parity
- Keep compute and fragment parity tests as a gating CI step.
- Enforce consistent uniform packing and debug flag masks across paths.
- Record per-preset divergence metrics and regressions in STATUS.md.

## Phase 5: Performance hygiene
- Enable anisotropic filtering baseline (GL 4.6 core).
- Evaluate polygon offset clamp for shadow bias stability.
- Add shader parallel compile checks when GL_KHR_parallel_shader_compile
  is present.
- Consider no-error context for release builds after validation.

## Phase 6: Cleanroom asset discipline
- Prefer LUT assets over runtime generation when `BLACKHOLE_LUT_ASSET_ONLY=1`.
- Validate LUT metadata and hash in parity runs.
- Keep test assets minimal and deterministic.

## Exit criteria
- SPIR-V path validated on at least one driver.
- gl_DrawID and indirect count path validated in a microbench.
- Parity sweep passes at default settings or tolerances are justified.

