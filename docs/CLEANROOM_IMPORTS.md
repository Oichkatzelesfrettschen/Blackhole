# Cleanroom Mathematics Imports

**Created:** 2026-01-01
**Scope:** Provenance tracking for physics implementations cross-validated
against openuniverse submodules.

## Executive Summary

This document tracks the cleanroom implementation status of physics functions
in Blackhole, cross-validated against reference implementations in:
- `~/Github/openuniverse/compact-common` - Python compact object library
- `~/Github/openuniverse/nubhlight` - C GRMHD radiation transport code
- `~/Github/openuniverse/PhysicsForge` - Equation catalog and validation

---

## Implemented (Cross-Validated)

### Schwarzschild Metric

| Function | Location | Reference | Status |
|----------|----------|-----------|--------|
| `schwarzschild_radius(mass)` | `src/physics/schwarzschild.h` | Standard GR | Validated |
| `photon_sphere_radius(mass)` | `src/physics/schwarzschild.h` | Standard GR | Validated |
| `isco_radius(mass)` | `src/physics/schwarzschild.h` | Standard GR | Validated |
| `gravitational_redshift(r, mass)` | `src/physics/schwarzschild.h` | Standard GR | Validated |

### Kerr Metric

| Function | Location | Reference | Status |
|----------|----------|-----------|--------|
| `kerr_sigma(r, a, theta)` | `src/physics/kerr.h` | nubhlight/metric.c | Validated |
| `kerr_delta(r, a, r_s)` | `src/physics/kerr.h` | nubhlight/metric.c | Validated |
| `kerr_outer_horizon(mass, a)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |
| `kerr_inner_horizon(mass, a)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |
| `kerr_isco_radius(mass, a, prograde)` | `src/physics/kerr.h` | BPT 1972, compact-common/kerr.py | Validated |
| `kerr_photon_orbit_prograde(mass, a)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |
| `kerr_photon_orbit_retrograde(mass, a)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |
| `ergosphere_radius(mass, a, theta)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |
| `frame_dragging_omega(r, theta, mass, a)` | `src/physics/kerr.h` | compact-common/kerr.py | Validated |

### Connection Coefficients

| Function | Location | Reference | Status |
|----------|----------|-----------|--------|
| `kerr_gcov(r, theta, a, r_s)` | `src/physics/connection.h` | nubhlight/metric.c:bl_gcov_func | Validated |
| `kerr_gcon(r, theta, a, r_s)` | `src/physics/connection.h` | nubhlight/metric.c:bl_gcon_func | Validated |
| `schwarzschild_gcov(r, theta, r_s)` | `src/physics/connection.h` | Standard GR | Validated |
| `schwarzschild_gcon(r, theta, r_s)` | `src/physics/connection.h` | Standard GR | Validated |
| `kerr_connection(r, theta, a, r_s)` | `src/physics/connection.h` | nubhlight/metric.c:conn_func | Validated |
| `schwarzschild_connection(r, theta, r_s)` | `src/physics/connection.h` | Standard GR | Validated |
| `lower_index(ucon, gcov)` | `src/physics/connection.h` | nubhlight/metric.c:lower | Validated |
| `raise_index(ucov, gcon)` | `src/physics/connection.h` | nubhlight/metric.c:raise | Validated |
| `geodesic_acceleration(ucon, conn)` | `src/physics/connection.h` | Geodesic equation | Validated |

### GLSL Shader Implementation

| Function | Location | Reference | Status |
|----------|----------|-----------|--------|
| `kerrSigma(r, a, cosTheta)` | `shader/include/kerr.glsl` | nubhlight/metric.c:mu | Validated |
| `kerrDelta(r, a, r_s)` | `shader/include/kerr.glsl` | nubhlight/metric.c:DD | Validated |
| `kerrOuterHorizon(r_s, a)` | `shader/include/kerr.glsl` | kerr.h | Validated |
| `kerrToCartesian(r, theta, phi)` | `shader/include/kerr.glsl` | Standard coord transform | Validated |
| `kerrInitConsts(pos, dir)` | `shader/include/kerr.glsl` | Flat-space approx | Validated* |
| `kerrStep(ray, r_s, a, c, dlam)` | `shader/include/kerr.glsl` | Carter formalism (Chandrasekhar 1983) | Validated |

#### Cross-Validation: kerrStep vs nubhlight metric.c (2026-01-01)

The `kerrStep` function uses Carter's first-integral formalism for Mino-time integration,
which is mathematically equivalent to the full geodesic equation used in nubhlight but
more efficient for ray tracing:

**Metric functions (verified against nubhlight/metric.c:126-184):**
- `kerrSigma(r, a, cosTheta) = r² + a²cos²θ` matches `mu * r²` in bl_gcov_func
- `kerrDelta(r, a, r_s) = r² - r_s*r + a²` matches `DD * r²` (nubhlight uses M=1, we use r_s=2M)

**Carter potentials (verified against Chandrasekhar 1983 Ch. 7):**
```
R(r) = (E(r²+a²) - aLz)² - Δ(Q + (Lz-aE)²)     // kerr.glsl:87
Θ(θ) = Q + a²E²cos²θ - Lz²/sin²θ                // kerr.glsl:88-89
```

**Geodesic velocities (verified against Chandrasekhar 1983 eq. 7.43-7.46):**
```
dr/dλ = ±√R                                      // kerr.glsl:102
dθ/dλ = ±√Θ                                      // kerr.glsl:103
dφ/dλ = Lz/sin²θ - aE + aA/Δ                     // kerr.glsl:104
dt/dλ = ((r²+a²)A/Δ) + a(Lz - aE*sin²θ)         // kerr.glsl:105-106
```

**Known limitations:**
- `*kerrInitConsts` uses flat-space Carter constant approximation (valid for distant observers)
- Sign flipping at turning points (R<0, Θ<0) is correct per first-integral theory
- Polar singularity avoided by clamping θ ∈ [ε, π-ε]

---

## Pending Imports

### From nubhlight/core/metric.c

| Function | Purpose | Priority | Status |
|----------|---------|----------|--------|
| `bl_gcov_func(r, th, gcov)` | Boyer-Lindquist covariant metric | HIGH | **PORTED** to `src/physics/connection.h` as `kerr_gcov` |
| `bl_gcon_func(r, th, gcon)` | Boyer-Lindquist contravariant metric | HIGH | **PORTED** to `src/physics/connection.h` as `kerr_gcon` |
| `conn_func(X, geom, conn)` | Christoffel symbols | MEDIUM | **PORTED** to `src/physics/connection.h` as `kerr_connection` |
| `lower(ucon, gcov, ucov)` | Index lowering | LOW | **PORTED** to `src/physics/connection.h` as `lower_index` |
| `raise(ucov, gcon, ucon)` | Index raising | LOW | **PORTED** to `src/physics/connection.h` as `raise_index` |

**Validation:** 7 tests in `tests/connection_test.cpp` verify metric symmetry, inverse property, connection symmetry, Schwarzschild limit, component signs, index operations, and geodesic acceleration.

### From nubhlight/core/coord.c

| Function | Purpose | Priority | Status |
|----------|---------|----------|--------|
| `bl_coord(X, r, th)` | Modified KS -> Boyer-Lindquist | MEDIUM | **PORTED** to `src/physics/coordinates.h` |
| `r_of_X(X)` | Coordinate mapping | MEDIUM | **PORTED** to `src/physics/coordinates.h` |
| `th_of_X(X)` | Coordinate mapping with derefine | MEDIUM | **PORTED** to `src/physics/coordinates.h` |
| `X_of_r(r)` | Inverse radial mapping | MEDIUM | **PORTED** to `src/physics/coordinates.h` |
| `dr_dX1(X)` | Radial derivative | MEDIUM | **PORTED** to `src/physics/coordinates.h` |
| `dth_dX2(X)` | Theta derivative | MEDIUM | **PORTED** to `src/physics/coordinates.h` |

**Validation:** 9 tests in `tests/coordinates_test.cpp` verify roundtrip accuracy, derefining behavior, and edge cases.

### From compact-common/spacetime/geodesics.py

| Function | Purpose | Priority |
|----------|---------|----------|
| `integrate_geodesic(...)` | Full geodesic integrator | HIGH |

---

## Validation Tests

All imports are validated against reference implementations via:
- `tests/physics_validation_test.cpp` - Direct C++ unit tests
- `scripts/generate_validation_tables.py` - Cross-check against compact-common
- `assets/validation/` - Reference curves for spin-dependent ISCO/photon orbits

### Test Coverage

| Test | Reference | Tolerance | Status |
|------|-----------|-----------|--------|
| ISCO (a=0) = 3 r_s | Schwarzschild | 1e-6 | Pass |
| ISCO prograde (a*=1) = 0.5 r_s | BPT 1972 | 1e-4 | Pass |
| ISCO retrograde (a*=1) = 4.5 r_s | BPT 1972 | 1e-4 | Pass |
| Photon sphere (a=0) = 1.5 r_s | Schwarzschild | 1e-6 | Pass |
| Kerr horizons (a*=0.998) | compact-common | 1e-6 | Pass |

---

## References

### Primary Sources

1. Bardeen, J. M., Press, W. H., & Teukolsky, S. A. (1972).
   "Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction,
   and Scalar Synchrotron Radiation." ApJ, 178, 347.

2. Chandrasekhar, S. (1983). "The Mathematical Theory of Black Holes."
   Oxford University Press.

3. Misner, C. W., Thorne, K. S., & Wheeler, J. A. (1973). "Gravitation."
   W. H. Freeman and Company.

### Code References

- nubhlight: LANL GRMHD code (BSD-3-Clause, Los Alamos)
- compact-common: GPL-3.0-or-later
- PhysicsForge: LGPL-3.0

---

## License Compatibility

All imported algorithms are mathematical formulas from published physics papers,
not copyrightable. Implementation details are cleanroom reimplementations
validated against reference code for correctness only.

| Source | License | Compatibility |
|--------|---------|---------------|
| nubhlight | BSD-3-Clause | Compatible |
| compact-common | GPL-3.0+ | Formulas only (cleanroom) |
| BPT 1972 | Published paper | Public domain math |
