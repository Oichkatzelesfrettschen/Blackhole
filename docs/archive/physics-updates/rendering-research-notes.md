# Blackhole Rendering Research Index (2026-03-29)

This note captures the external research inputs most relevant to the current
Blackhole renderer tranche: visual fidelity, mathematical correctness,
polarized radiative transfer, and GPU implementation strategy.

It is intentionally narrow. The question is not "what is all black hole
research?" It is "which recent primary sources should inform the next
renderer-correctness and image-fidelity passes?"

## Core Physics / Imaging Sources

1. Photon ring polarimetry with next-generation black hole imaging I. M87*
   - arXiv: https://arxiv.org/abs/2410.15325
   - Date: 2024-10-20
   - Why it matters:
     - gives concrete ring, LP, and CP transition-scale reasoning
     - directly relevant to where high-energy near-ring structure should survive
     - useful for deciding what image features should remain visible versus get
       suppressed as broad-field spill

2. Coport: A New Public Code for Polarized Radiative Transfer in a Covariant Framework
   - arXiv: https://arxiv.org/abs/2407.10431
   - Date: 2024-07-15
   - Why it matters:
     - emphasizes solving coupled covariant polarized transfer directly
     - validates against analytic, thin-disk, and thick-disk cases
     - relevant to Blackhole because our parity effort keeps exposing where
       image fidelity and transport-model shortcuts diverge

3. Polarimetric Signatures of Bulk Comptonization from within the Plunging Region of Accreting Black Holes
   - arXiv: https://arxiv.org/abs/2504.15486
   - Date: 2025-04-21
   - Why it matters:
     - explicitly studies polarization and unresolved/resolved discrepancies
     - highlights how near-horizon and plunging-region physics can create large
       local polarization structure that later cancels in aggregate
     - useful warning against "fixing" images by broad smoothing that destroys
       real local contrast

4. Horizon-scale variability of M87* from 2017-2021 EHT observations
   - arXiv: https://arxiv.org/abs/2509.24593
   - Date: 2025-09-29
   - Why it matters:
     - reinforces that asymmetric rings are persistent while azimuthal
       brightness and polarization vary between epochs
     - useful for separating stable geometry constraints from astrophysical
       variability in our beauty-vs-diagnostic profiles

5. Interferometric inference of black hole spin from photon ring size and brightness
   - arXiv: https://arxiv.org/abs/2509.23628
   - Date: 2025-09-28
   - Why it matters:
     - argues that ring width and brightness structure can constrain spin
     - directly relevant to our renderer because local contrast placement and
       width are not merely cosmetic

6. First polarization study of the M87 jet and active galactic nuclei at submillimeter wavelengths with ALMA
   - arXiv: https://arxiv.org/abs/2505.10181
   - Date: 2025-05-15
   - Why it matters:
     - adds higher-frequency polarization and Faraday constraints
     - useful for deciding whether our stylized polarized structure is at least
       directionally compatible with current sub-mm observations

## Computational / Method Sources

7. Introducing APERTURE: A GPU-based General Relativistic Particle-in-Cell Simulation Framework
   - arXiv: https://arxiv.org/abs/2503.04558
   - Date: 2025-03-06
   - Why it matters:
     - modern GPU-first black-hole-adjacent code architecture
     - modular correctness-tested CUDA/HIP design
     - relevant for separating solver kernels, validation cases, and observer
       semantics more cleanly inside Blackhole

8. Jipole: A Differentiable ipole-based Code for Radiative Transfer in Curved Spacetimes
   - arXiv: https://arxiv.org/abs/2509.07065
   - Date: 2025-09-08
   - Why it matters:
     - automatic differentiation for image gradients
     - suggests a future direction for parameter-fitting and sensitivity maps
     - relevant to Blackhole if we want image-space parity checks to become
       gradient-aware instead of screenshot-only

## Local Repo Patterns Worth Stealing

### open_gororoba

Relevant patterns found in `agents.toml` and README:

- SoA/coalesced layouts as a declared optimization phase
- explicit L2 residency strategy
- pinned host memory as a first-class optimization
- multi-path verification culture: independent paths must agree
- registry / claims / evidence framing for scientific software

Most transferable ideas for Blackhole:

- make GPU optimization phases explicit and measurable
- keep mathematical claims and renderer claims tied to reproducible evidence
- adopt "three independent paths must agree" where practical

### steinmarder

Relevant patterns:

- microbenchmark-guided GPU tuning
- SASS/latency reference docs tied to real measurements
- deterministic rendering and benchmark discipline
- explicit timestamp-instrumentation advice instead of wall-clock guessing
- ILP, cache, and shared-memory discussions grounded in measured hardware behavior

Most transferable ideas for Blackhole:

- separate beauty tuning from measured low-level GPU tuning
- add timestamp-based GPU instrumentation for expensive passes
- use hardware-informed tuning, not folklore

### turboquant-pytorch

Relevant patterns:

- architecture-aware dispatch
- fused hot-path kernels
- bounded content-based cache
- explicit fallback hierarchy
- direct inheritance of optimization rules from other repos with provenance

Most transferable ideas for Blackhole:

- formalize GPU tier selection and feature flags
- document when fused paths are trustworthy and when they are not
- cache precomputed structures with explicit bounds and invalidation rules

## Synthesis

The research and local repo evidence point in the same direction:

1. Blackhole needs stricter separation between:
   - geometry/transport correctness
   - beauty presentation
   - performance specialization

2. The next real visual-fidelity wins should come from:
   - preserving physically meaningful local contrast
   - reducing false spill in the escaped field
   - validating against ring-width / brightness / polarization structure from
     current literature, not just against subjective screenshots

3. The next performance wins should come from:
   - measured memory-path improvements
   - architecture-aware dispatch
   - explicit cache/residency strategy
   - narrow fused kernels where they can be proven equivalent
