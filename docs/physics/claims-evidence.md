# Physics Claims And Evidence

This is the checked local claims inventory for Blackhole's physics stack.

## Policy

- Historical research notes can contain broad literature summaries.
- This document and `claims_evidence.json` are the current local source of
  truth for claims that the repository asserts about its implemented physics.
- Every claim lists source paths, a required evidence class, and the evidence
  class of each named test. A registered test only satisfies a claim when its
  class matches the required class.

## Verification workflow

Generate or re-check the manifest with:

```bash
cmake --build --preset docs --target verify-physics-claims
ctest --preset docs -R physics_claims_matrix --output-on-failure
```

The verifier checks that:

- each referenced file exists
- each required CTest name is present in the configured build
- an applicable registered test supplies the claim's required evidence class
- conditional test requirements match explicit BOOL values in `CMakeCache.txt`
- a report is written under `build/*/reports/physics_claims.md`

The report establishes file presence, declared evidence class, and test registration. Test execution,
numerical accuracy, rendered-image validation, and CUDA device execution require
their own test results. A CPU configuration records CUDA obligations as
`not-applicable`; the report preserves their names and the `ENABLE_CUDA=OFF`
evidence. A CUDA configuration requires every declared CUDA test registration.

Each test declares its evidence class. A conditional test also declares its
required CMake BOOL options:

```json
{"name": "cuda_stokes", "evidence_class": "formula-unit", "requires": ["ENABLE_CUDA"]}
```

All named options must be enabled for that test to apply. Missing options,
unrecognized BOOL values, malformed requirements, and failed CTest discovery
fail verification. Source files remain mandatory in every configuration. The
report records manifest and CMake-cache SHA-256 hashes, and replaces a previous
success report with an error report when discovery fails.

Evidence classes are `formula-unit`, `component-integration`,
`mock-observable`, `shader-compile`,
`shared-path-parity`, `independent-oracle`, `render-output`, and
`observational-calibration`. The verifier requires an exact class match. Class
labels are manifest assertions subject to source review, not automatic proof of
test semantics. `eht_shadow_validation` generates an analytic observable and is
classified `mock-observable`; it cannot support `render-output` or
`observational-calibration`. Its comparison with published ring diameters is
context for an analytic scale, not calibration of shipping renderer pixels.

Run the applicability and failure-path regressions with
`ctest --preset docs -R physics_claims_verifier --output-on-failure`.

## Current inventory

The canonical machine-readable manifest is:

- [claims_evidence.json](claims_evidence.json)

The initial inventory focuses on claims already backed by local code/tests:

- Kerr and related metric implementations
- Newman-Penrose curvature scalars
- Novikov-Thorne thin-disk thermodynamics
- Radiative transfer and polarization transport
- EHT-facing observables and shadow metrics
- GRMHD ingestion/streaming and GPU upload pipeline
- CUDA backend layout, orbital, RTE, and Stokes validation

Broader literature-derived claims remain candidates until they are promoted
into this manifest with explicit local evidence.
