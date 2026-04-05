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
- each referenced CTest name is present in the configured build
- a report is written under `build/*/reports/physics_claims.md`

## Current inventory

The canonical machine-readable manifest is:

- [claims_evidence.json](/home/eirikr/Github/Blackhole/docs/physics/claims_evidence.json)

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
