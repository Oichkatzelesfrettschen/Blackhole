# Physics Claims And Evidence

This is the checked local claims inventory for Blackhole's physics stack.

## Policy

- Historical research notes can contain broad literature summaries.
- This document and `claims_evidence.json` are the current local source of
  truth for claims that the repository asserts about its implemented physics.
- Every claim listed here must map to concrete code/docs plus one or more local
  validation tests.

## Verification workflow

Generate or re-check the manifest with:

```bash
cmake --build --preset docs --target verify-physics-claims
ctest --preset docs -R physics_claims_matrix --output-on-failure
```

The verifier checks that:

- each referenced file exists
- each required CTest name is present in the configured build
- conditional test requirements match explicit BOOL values in `CMakeCache.txt`
- a report is written under `build/*/reports/physics_claims.md`

The report establishes file presence and test registration. Test execution,
numerical accuracy, rendered-image validation, and CUDA device execution require
their own test results. A CPU configuration records CUDA obligations as
`not-applicable`; the report preserves their names and the `ENABLE_CUDA=OFF`
evidence. A CUDA configuration requires every declared CUDA test registration.

An unconditional test is a string. A conditional test declares its required
CMake BOOL options explicitly:

```json
{"name": "cuda_stokes", "requires": ["ENABLE_CUDA"]}
```

All named options must be enabled for that test to apply. Missing options,
unrecognized BOOL values, malformed requirements, and failed CTest discovery
fail verification. Source files remain mandatory in every configuration. The
report records manifest and CMake-cache SHA-256 hashes, and replaces a previous
success report with an error report when discovery fails.

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
