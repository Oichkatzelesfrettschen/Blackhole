# Unit System Alignment

This document defines the unit policy across CPU (C++) and GPU (GLSL)
code paths and the validation assets used to keep them consistent.

## Goals
- Single authoritative unit system for physics constants and inputs.
- Explicit CGS ↔ geometric conversion boundaries.
- Validation curves that fail fast when unit drift appears.

## CPU (C++) Units
- Base: CGS (cm, g, s, K).
- Mass inputs: grams (e.g., `M_SUN`).
- Distances: cm (`r_s = 2GM/c^2`, `r_g = GM/c^2`).
- Frequencies: Hz.

## GPU (GLSL) Units
- Shader math uses normalized radii in units of `r_s`.
- Any physical inputs passed to shaders are already normalized:
  - `schwarzschildRadius` defaults to 2.0 in geometric units.
  - `iscoRadius`, `photonSphereRadius` are normalized by `r_s`.

## GRB/LUT Units
- Time: seconds (observer frame unless metadata says source frame).
- Flux: erg/cm^2/s (bolometric) or erg/cm^2/s/Hz (spectral density).
- Frequency: Hz; Wavelength: Angstroms; Energy: keV.

## Conversion Helpers
- C++ should expose the following helpers:
  - `schwarzschild_radius(mass)` -> `r_s` in cm.
  - `kerr_isco_radius(mass, a)` -> cm, then normalize by `r_s`.
  - `kerr_photon_orbit_*` -> cm, then normalize by `r_s`.

## Validation Assets
- `assets/validation/metrics.json` stores `r_s`, `r_isco`, `r_ph` in CGS.
- `assets/validation/redshift_curve.csv` stores `r_over_rs` vs redshift.
- `assets/validation/spin_radii_curve.csv` stores spin vs `r_isco/r_s` and `r_ph/r_s`.

## Reference Curve Generation
- `scripts/generate_validation_tables.py` prefers `compact-common` when available to emit
  ISCO/photon/redshift curves; it records a metadata flag when falling back to C++ formulas.

## Runtime Checks (Future)
- Optional guardrails: clamp NaN/inf in shader parameters.
- CPU asserts for negative radii or non-finite constants.
