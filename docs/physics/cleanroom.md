# Cleanroom Implementation

This document consolidates the cleanroom implementation records: port mapping,
mathematics imports, decision log, interop notes, and migration worklist.

No source code is copied from external projects; only equations, data formats,
and behaviors are referenced. All imported algorithms are mathematical formulas
from published physics papers, not copyrightable. Implementation details are
cleanroom reimplementations validated against reference code for correctness only.

---

## Port Map

This map connects external modules to cleanroom C++23/GLSL targets.

### Compact Objects
- compact-common/spacetime -> `src/physics/kerr.*`, `src/physics/schwarzschild.*`
- compact-common/spacetime/kerr.py -> horizons, ISCO, photon orbit, frame dragging, ergosphere (CGS inputs)
- compact-common/spacetime/schwarzschild.py -> r_s, g_tt/g_rr, redshift, photon sphere (CGS inputs)
- compact-common/structure/tov -> TOV solver + pressure-density interpolation (future `src/physics/tov.*`)
- compact-common/structure/tov.py -> MeV/fm^3 to CGS conversions + RK4/solve_ivp patterns; optional numba
- compact-common/structure/tidal -> Love numbers/tidal deformability (future validation)
- CompactStar -> C++17 TOV + Hartle solvers, state/driver separation, diagnostics (design reference)
- Generation-EOS-of-Neutron-Stars -> QHD/MFA EOS pipeline + Bayesian fitting (validation only)
- rns -> rotating star validation for TOV extensions

### Accretion / Emission
- nubhlight -> HDF5 density/temp/velocity/B ingestion -> 3D textures
  (dump keys: `P` with `vnams`, `t`, `dump_cnt`, `jcon`, optional `Rmunu`, `Jrad`,
  `Nem`, `Nabs`, `Nsc`)
- tardis -> spectral response LUTs for emission weighting

### GRB / Afterglow
- grb-common -> constants, cosmology, I/O schema for LUTs
- grb-common/cosmology -> distance/redshift/time relations for flux scaling
- grb-common/io/schemas.py -> LightCurve/Spectrum units: time (s), flux (erg/cm^2/s or /Hz),
  frequency (Hz), wavelength (Angstrom), energy (keV)
- ASGARD_GRBAfterglow -> afterglow spectrum model (synchrotron + SSC + SSA; implicit PDE for electron spectra)
- JetFit -> lightcurve LUTs + parameter grids; `Table.h5` keys: `Axis` (tau/Eta0/GammaB/theta_obs),
  `f_peak`, `f_nu_c`, `f_nu_m`, optional `LogAxis`/`LogTable` for scaling
- boxfit -> HDF5 RHD tables + interpolation (afterglowlibrary box data); EDS datasets:
  `F`, `t_obs`, `z`, `dL`, `ur_min/max`, `uphi_min/max`, `R_50/75/95/99/100`, `ur_rays`, `uphi_rays`,
  `I`, `ur`, `uphi`
- PyGRB -> pulse envelopes for time modulation (FRED + nested sampling for pulse fitting)
- VAE-Jet -> anomaly tagging concepts (ML-only; use as validation reference, not runtime)

### Visualization References
- openuniverse/Blackhole -> legacy OpenGL black hole renderer + reference links

### Cosmology (validation)
- spandrel-core -> lightweight FlatLambdaCDM + distance modulus; use for LUT validation
- pantheon/xcosm/desibao -> dataset loaders + distance curves (validation only)
- desibao -> DESI Y3 BAO pipeline (validation only)

### Signals / Timing (reference)
- PsrSigSim -> pulsar timing noise models (future GW/TOA validation reference)

### Knowledgebase / Research
- knowledge -> LFS store for papers/datasets (reference only)
- MathScienceCompendium -> fact-checking patterns + bibliography management (reference only)
- Superframework -> speculative fractional-calculus framework (do not integrate into runtime)

### HEP / Data Pipelines (reference only)
- Adaptive-ParticlePhysics-Triggers -> HDF5 schema patterns + anomaly scoring pipeline
- AliceO2 + CERN-Data-Analysis-ALICE-Run3 -> ROOT-based data flows, cut/efficiency reporting
- AEGIS-Project -> real-time signal statistics + Welford-style monitoring patterns

### HUD / Performance
- MangoHud -> FPS/frametime percentiles, GPU timings, overlay layout

### Rendering Patterns
- graphics-programming (TinyGL/PortableGL/SGI): matrix + clipping + viewport transforms for
  optional CPU fallback/validation.
  - TinyGL: scanline rasterization, fixed-point edge stepping.
  - PortableGL: edge-function rasterization, per-pixel barycentric interpolation.
  - Shared math: perspective-correct interpolation formula + Sutherland-Hodgman clipping.
- Xinim: renderer concept with `draw_text` + buffer rendering (HUD overlay patterns).
- microwindows64: minimal windowing/Nano-X + input notes for HUD/input design ideas.

### Tooling Patterns
- common -> registry/units patterns for model factories
- common/units.py -> CODATA 2022 CGS constants for cross-checking
- common/validation.py -> finite/positive guards for runtime sanity checks
- common/types.py -> DatasetRef/RunResult schemas for offline pipeline metadata
- common/adapters/* -> schema hints for tardis/xcosm/torax/pantheon integration
- cern-analysis-common -> I/O/validation patterns (offline only)

### Port Sequencing (priority order)
1) compact-common (spacetime + EOS): ISCO/photon/redshift curves, validation LUTs.
2) common: schema contracts + validation guards for offline pipelines.
3) grb-common/JetFit/boxfit: GRB light-curve + spectral LUT inputs.
4) nubhlight: GRMHD HDF5 ingestion + texture packing.
5) tardis: spectral calibration LUTs (offline only).
6) spandrel/xcosm/pantheon: cosmology validation curves (offline only).

### Attribution / citation notes (cleanroom references)
- ASGARD_GRBAfterglow: README requires explicit attribution; cite Ren et al. 2024 ApJ 962:115.
- boxfit: cite Van Eerten et al. 2012 ApJ 749:44 for afterglow fits.
- nubhlight: cite Miller et al. 2019 ApJS 241:2 and Ryan et al. 2015 ApJ 807:31.
- tardis: cite Kerzendorf & Sim 2014 MNRAS 440:387; add Vogl et al. 2019 A&A 621:A29 if using Type II.
- grb-common: cite project if using its schemas/constants as validation baselines.
- compact-common/CompactStar/rns: cite original solver references if metrics/EOS curves are published.

---

## Imports

Provenance tracking for physics implementations cross-validated
against openuniverse submodules.

Cross-validated against reference implementations in:
- `~/Github/openuniverse/compact-common` - Python compact object library
- `~/Github/openuniverse/nubhlight` - C GRMHD radiation transport code
- `~/Github/openuniverse/PhysicsForge` - Equation catalog and validation

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

#### Cross-Validation: kerrStep vs nubhlight metric.c

The `kerrStep` function uses Carter's first-integral formalism for Mino-time integration,
which is mathematically equivalent to the full geodesic equation used in nubhlight but
more efficient for ray tracing:

**Metric functions (verified against nubhlight/metric.c:126-184):**
- `kerrSigma(r, a, cosTheta) = r^2 + a^2*cos^2(theta)` matches `mu * r^2` in bl_gcov_func
- `kerrDelta(r, a, r_s) = r^2 - r_s*r + a^2` matches `DD * r^2` (nubhlight uses M=1, we use r_s=2M)

**Carter potentials (verified against Chandrasekhar 1983 Ch. 7):**
```
R(r) = (E(r^2+a^2) - aLz)^2 - Delta(Q + (Lz-aE)^2)
Theta(theta) = Q + a^2*E^2*cos^2(theta) - Lz^2/sin^2(theta)
```

**Geodesic velocities (verified against Chandrasekhar 1983 eq. 7.43-7.46):**
```
dr/dlambda = +/-sqrt(R)
dtheta/dlambda = +/-sqrt(Theta)
dphi/dlambda = Lz/sin^2(theta) - aE + aA/Delta
dt/dlambda = ((r^2+a^2)A/Delta) + a(Lz - aE*sin^2(theta))
```

**Known limitations:**
- `*kerrInitConsts` uses flat-space Carter constant approximation (valid for distant observers)
- Sign flipping at turning points (R<0, Theta<0) is correct per first-integral theory
- Polar singularity avoided by clamping theta in [epsilon, pi-epsilon]

### Ported from nubhlight/core/metric.c

| Function | Purpose | Status |
|----------|---------|--------|
| `bl_gcov_func(r, th, gcov)` | Boyer-Lindquist covariant metric | **PORTED** to `src/physics/connection.h` as `kerr_gcov` |
| `bl_gcon_func(r, th, gcon)` | Boyer-Lindquist contravariant metric | **PORTED** to `src/physics/connection.h` as `kerr_gcon` |
| `conn_func(X, geom, conn)` | Christoffel symbols | **PORTED** to `src/physics/connection.h` as `kerr_connection` |
| `lower(ucon, gcov, ucov)` | Index lowering | **PORTED** to `src/physics/connection.h` as `lower_index` |
| `raise(ucov, gcon, ucon)` | Index raising | **PORTED** to `src/physics/connection.h` as `raise_index` |

Validation: 7 tests in `tests/connection_test.cpp` verify metric symmetry, inverse property,
connection symmetry, Schwarzschild limit, component signs, index operations, and geodesic acceleration.

### Ported from nubhlight/core/coord.c

| Function | Purpose | Status |
|----------|---------|--------|
| `bl_coord(X, r, th)` | Modified KS -> Boyer-Lindquist | **PORTED** to `src/physics/coordinates.h` |
| `r_of_X(X)` | Coordinate mapping | **PORTED** to `src/physics/coordinates.h` |
| `th_of_X(X)` | Coordinate mapping with derefine | **PORTED** to `src/physics/coordinates.h` |
| `X_of_r(r)` | Inverse radial mapping | **PORTED** to `src/physics/coordinates.h` |
| `dr_dX1(X)` | Radial derivative | **PORTED** to `src/physics/coordinates.h` |
| `dth_dX2(X)` | Theta derivative | **PORTED** to `src/physics/coordinates.h` |

Validation: 9 tests in `tests/coordinates_test.cpp` verify roundtrip accuracy,
derefining behavior, and edge cases.

### Validation Tests

All imports are validated against reference implementations via:
- `tests/physics_validation_test.cpp` - Direct C++ unit tests
- `scripts/generate_validation_tables.py` - Cross-check against compact-common
- `assets/validation/` - Reference curves for spin-dependent ISCO/photon orbits

| Test | Reference | Tolerance | Status |
|------|-----------|-----------|--------|
| ISCO (a=0) = 3 r_s | Schwarzschild | 1e-6 | Pass |
| ISCO prograde (a*=1) = 0.5 r_s | BPT 1972 | 1e-4 | Pass |
| ISCO retrograde (a*=1) = 4.5 r_s | BPT 1972 | 1e-4 | Pass |
| Photon sphere (a=0) = 1.5 r_s | Schwarzschild | 1e-6 | Pass |
| Kerr horizons (a*=0.998) | compact-common | 1e-6 | Pass |

### References

**Primary Sources:**

1. Bardeen, J. M., Press, W. H., & Teukolsky, S. A. (1972).
   "Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction,
   and Scalar Synchrotron Radiation." ApJ, 178, 347.
2. Chandrasekhar, S. (1983). "The Mathematical Theory of Black Holes."
   Oxford University Press.
3. Misner, C. W., Thorne, K. S., & Wheeler, J. A. (1973). "Gravitation."
   W. H. Freeman and Company.

**Code References:**
- nubhlight: LANL GRMHD code (BSD-3-Clause, Los Alamos)
- compact-common: GPL-3.0-or-later
- PhysicsForge: LGPL-3.0

### License Compatibility

| Source | License | Compatibility |
|--------|---------|---------------|
| nubhlight | BSD-3-Clause | Compatible |
| compact-common | GPL-3.0+ | Formulas only (cleanroom) |
| BPT 1972 | Published paper | Public domain math |

---

## Decision Log

### 2025-12-31: Shared interop includes for parity
- Decision: compute and fragment parity both include `interop_raygen.glsl` + `interop_trace.glsl`.
- Rationale: single source of truth for raygen/trace/shade reduces drift.
- Tradeoff: shared code cannot use fragment-only built-ins.

### 2025-12-31: Compare baseline toggle
- Decision: add `BLACKHOLE_COMPARE_BASELINE=1` to disable disk/noise/GRMHD/background.
- Rationale: isolate integrator parity from art/asset variability.
- Tradeoff: baseline sweeps do not reflect full-frame art output.

### 2025-12-31: Compare overrides for step size/max steps
- Decision: expose `BLACKHOLE_COMPARE_MAX_STEPS` and `BLACKHOLE_COMPARE_STEP_SIZE`.
- Rationale: allow strict parity sweeps to reduce integration error.
- Tradeoff: higher step counts increase sweep time.

### 2025-12-31: Integrator debug flags
- Decision: add `BLACKHOLE_INTEGRATOR_DEBUG_FLAGS` to flag NaN/Inf and range issues.
- Rationale: quick visual validation in compare captures.
- Tradeoff: debug overlays alter output and should not be used for parity metrics.

### 2025-12-31: Timestamped flamegraphs
- Decision: `run_flamegraph.sh` writes `flamegraph_<timestamp>.svg` and updates `flamegraph_latest.svg`.
- Rationale: preserve perf history without manual file moves.
- Tradeoff: extra files accumulate under `logs/perf/flamegraph`.

### 2025-12-31: LUT asset-only mode
- Decision: add `BLACKHOLE_LUT_ASSET_ONLY=1` to skip generated LUT fallback.
- Rationale: enforce cleanroom asset parity when validating against shipped LUTs.
- Tradeoff: missing LUT assets disable LUT shading until assets are restored.

### 2025-12-31: Optional SPIR-V shader loading
- Decision: add `BLACKHOLE_USE_SPIRV=1` to load `*.spv` when available.
- Rationale: enable offline shader compilation and align with GL 4.6 pipelines.
- Tradeoff: requires .spv artifacts alongside GLSL sources.

### 2025-12-31: DrawID probe and parallel compile toggles
- Decision: add a DrawID probe (`BLACKHOLE_DRAWID_PROBE=1`) and optional
  parallel shader compile / no-error context toggles.
- Rationale: validate gl_DrawID and 4.6 runtime toggles without refactoring
  the main render path.
- Tradeoff: probe is a debug overlay; full multi-draw integration remains TBD.

---

## Interop Notes

Shader parity and shared integration logic for compute/fragment paths.

### Shared shader modules
- `shader/include/interop_raygen.glsl`: pixel mapping + ray direction.
- `shader/include/interop_trace.glsl`: geodesic integration + shading.

Both compute (`shader/geodesic_trace.comp`) and fragment
(`shader/blackhole_main.frag` in parity mode) include the same
raygen/trace code to reduce divergence.

### Parity mode

Fragment parity path (compare sweeps):
- `interopParityMode` gates the parity branch in `blackhole_main.frag`.
- Uses `bhTraceGeodesic` + `bhShadeHit` from `interop_trace.glsl`.

Compute path:
- Always uses `bhTraceGeodesic` + `bhShadeHit` from `interop_trace.glsl`.

### Debug flags

`bhDebugFlags` is a bitmask used inside `interop_trace.glsl`:
- `1`: flag NaN/Inf and paint magenta.
- `2`: flag out-of-range radii and paint yellow.
- `3`: both.

Enable via:
```bash
BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=3 ./build/Release/Blackhole
```

### Parity sweep findings

Baseline compare sweeps showed sensitivity to integration step size:
- Default steps (300/0.1): 2/12 preset failures (post background LOD bias defaults).
- 600 steps + 0.05 step: 2/12 preset failures.
- 1000 steps + 0.02 step: 0/12 preset failures.

Conclusion: divergence is dominated by integration error near high curvature
rather than NaN/Inf or range issues.

### OpenGL 4.6 standardization impact
- `shader-report.md` summarizes 4.5 to 4.6 changes that affect
  cleanroom parity, notably SPIR-V ingestion and gl_DrawID availability.

---

## Migration Worklist

Staged, testable migration plan that keeps parity between compute and fragment
paths while incrementally adopting modern OpenGL 4.6 features.

### Phase 0: Agreement on scope
- Freeze a minimal feature set for parity sweeps (no art toggles).
- Gate all cleanroom changes behind explicit feature flags.
- Log all decisions in the Decision Log section above.

### Phase 1: Shader compilation pipeline (selected first subsystem)
- Add optional SPIR-V loader path (GL 4.6 core, GL_ARB_gl_spirv on 4.5).
- Keep GLSL source fallback for older drivers.
- Add build pipeline step to emit .spv alongside GLSL sources.
- Cache shader variants and specializations to avoid repeated compile work.
- Track compile/link latency (GPU timing panel or log CSV).

### Phase 2: Draw submission model
- Introduce SSBO-backed per-draw data indexed by gl_DrawID.
- Add optional multi-draw indirect path for draw batching.
- Implement indirect count path when GL 4.6 or GL_ARB_indirect_parameters
  is available.

### Phase 3: State management
- Expand DSA usage to remove bind-to-edit patterns.
- Centralize state changes to a small state cache module.
- Add explicit validation for resource lifetimes in debug builds.

### Phase 4: Shader and pipeline parity
- Keep compute and fragment parity tests as a gating CI step.
- Enforce consistent uniform packing and debug flag masks across paths.
- Record per-preset divergence metrics and regressions in status.md.

### Phase 5: Performance hygiene
- Enable anisotropic filtering baseline (GL 4.6 core).
- Evaluate polygon offset clamp for shadow bias stability.
- Add shader parallel compile checks when GL_KHR_parallel_shader_compile
  is present.
- Consider no-error context for release builds after validation.

### Phase 6: Cleanroom asset discipline
- Prefer LUT assets over runtime generation when `BLACKHOLE_LUT_ASSET_ONLY=1`.
- Validate LUT metadata and hash in parity runs.
- Keep test assets minimal and deterministic.

### Exit criteria
- SPIR-V path validated on at least one driver.
- gl_DrawID and indirect count path validated in a microbench.
- Parity sweep passes at default settings or tolerances are justified.
