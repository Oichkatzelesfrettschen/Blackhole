# Blackhole Rendering Next 42 Steps

This tranche focuses on three goals:

1. visual fidelity
2. mathematical correctness
3. reproducible performance and parity evidence

The scope is intentionally bounded around the actual current blocker:
CUDA/GLSL visual disparity in `showcase-orbit` / `wide-right`, plus the
broader renderer architecture work needed so later fidelity gains remain
provable.

## Phase A: Measurement And Ground Truth (1-8)

1. Freeze the current raw parity baseline for `showcase-orbit` / `wide-right`
   as a named checkpoint artifact.
2. Add a second raw parity baseline for `right-third` so parity is not judged
   on only one composition.
3. Export a compact CSV of mask-level parity metrics for every future sweep.
4. Add a verifier that rejects parity claims unless both raw artifacts and
   summary JSON exist.
5. Add a small "physics fidelity dashboard" script that prints:
   - overall mean abs
   - `bright_arc_adjacent_right` luma/chroma gaps
   - `broad_right_background` luma/chroma gaps
   - `negative_space` luma/chroma gaps
6. Add a raw-mask trend plot over commits so regressions stop hiding in prose.
7. Add a deterministic seed/control manifest for all parity captures.
8. Add a benchmark note that distinguishes:
   - raw parity
   - post-tonemap beauty
   - FPS / kernel throughput

## Phase B: Math-Correctness Envelope (9-16)

9. Write down the current image-model decomposition explicitly:
   - background sample
   - near-hole lift/shadow
   - sector contrast
   - tint contribution
   - exclusion / negative-space suppression
10. Add a tiny CPU reference script for the escaped-background shaping function.
11. Run the same scalar shaping inputs through CPU reference and CUDA path and
    compare numerically.
12. Add unit tests for monotonicity of the shaping terms with respect to:
    - `bright_sector`
    - `adjacent_sector`
    - `near_hole_weight`
13. Add a test that proves the adjacent band cannot get brighter when the
    dedicated suppression knob increases.
14. Add a test that broad-field suppression cannot increase chroma.
15. Separate "transport-like" terms from "beauty-like" terms in code comments
    and docs so future tuning does not accidentally mix them.
16. Add one doc row per shaping term with:
    - variable name
    - intended visual effect
    - measurable failure mode if overtuned

## Phase C: Near-Hole Fidelity (17-24)

17. Attack pre-tint adjacent-band excess by modulating `local_lift` locally,
    not globally.
18. Search a narrow family of adjacent-band reductions for `local_lift`, judged
    only on raw masks.
19. If that fails, repeat for `sector_contrast` instead of tint.
20. Compare whether the adjacent-band debt is more sensitive to pre-tint lift
    or to tint survival.
21. Add one mask that isolates the true bright arc core separately from the
    spill band so we stop conflating "good arc brightness" with "bad spill."
22. Tune for lower adjacent spill while preserving or improving the bright-arc
    core luma.
23. Add a ring-width proxy metric so darkening the field does not silently
    collapse the ring geometry.
24. Add an asymmetry proxy metric so the approaching-side crescent remains
    physically plausible.

## Phase D: Polarization And Transport Relevance (25-30)

25. Map current renderer terms against `Coport` and `Jipole` style transport
    terminology: what is actual transport, what is presentation.
26. Add a note on which current Blackhole image terms are placeholders rather
    than covariant transport results.
27. Add one polarized-reference image comparison workflow against a recent
    photon-ring polarimetry paper for morphology, not exact inference.
28. Define a "resolved local structure must survive" policy informed by the
    plunging-region polarization paper.
29. Keep beauty tuning from erasing small high-energy structures that later
    average out observationally.
30. Add a future hook for differentiable sensitivity maps inspired by `Jipole`,
    even if gradients are not implemented yet.

## Phase E: CUDA / GLSL / Hybrid Parity (31-36)

31. Add a parity matrix doc that names what each lane is expected to match:
    - geometry
    - raw field shape
    - ring asymmetry
    - broad-field darkness
    - beauty output
32. Add a lane-by-lane checklist for what is allowed to differ.
33. Compare raw parity for GLSL vs hybrid vs CUDA on the same exact camera and
    composition for at least two views.
34. Promote no lane by eye alone; require raw parity plus one beauty comparison.
35. Add a "parity suspect list" doc for terms still implemented differently
    between shader and CUDA paths.
36. When a parity term is fixed, record the before/after raw metrics next to
    the code change.

## Phase F: Performance Architecture (37-42)

37. Add an architecture-aware kernel/profile note inspired by
    `turboquant-pytorch/gpu_dispatch.py`:
    - Ada
    - Ampere
    - Turing
    - generic
38. Add timestamp-query instrumentation so beauty-path costs are measured on-GPU
    instead of inferred from wall-clock runs.
39. Add a microbenchmark for the escaped-background shaping path so future
    "fidelity" tweaks do not accidentally blow up register pressure or cost.
40. Evaluate whether any per-pixel shaping terms should be fused or cached using
    `steinmarder`-style ILP / cache reasoning, but only after parity improves.
41. Add a bounded cache for any expensive deterministic precomputed structures,
    borrowing the explicit cache-discipline style from `turboquant-pytorch`.
42. Revisit `openperception` only when a Blackhole still clears both bars:
    - raw parity debt is materially lower in the right-side escaped field
    - beauty still actually beats the current OpenGL source by eye

## Immediate Order Of Attack

If only the next three implementation steps are taken, they should be:

1. pre-tint adjacent-band lift suppression search
2. bright-arc-core mask and metric
3. second-view raw parity baseline (`right-third`)

Those three give the best ratio of new information to engineering effort.
