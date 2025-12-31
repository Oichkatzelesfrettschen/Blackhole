# OpenUniverse Integration Scope (Cleanroom Plan)

This document scopes all openuniverse submodules and maps them to cleanroom
C++23/GLSL460 implementations inside Blackhole. No code is copied. We only
use public equations, algorithms, and data formats as references.

## Goals
- Inventory each submodule and its primary language/build system.
- Identify physics algorithms, datasets, or validation targets.
- Define cleanroom extraction targets and validation harnesses.
- Sequence work into phases with testable milestones.

## Cleanroom pipeline
1. Extract math spec: equations, inputs/outputs, units.
2. Implement C++23 core module with unit tests.
3. Add GLSL LUTs/compute paths where needed.
4. Validate vs reference outputs (python/fortran/c data) offline.
5. Benchmark and gate by warnings-as-errors.

## Submodule inventory (summary)
Module | Build | Primary files | Cleanroom target
--- | --- | --- | ---
grb-common | pyproject | Python | GRB lightcurve models -> time-varying emissivity LUTs
ASGARD_GRBAfterglow | pyproject | Python+Fortran | afterglow solver -> jet emission profiles
boxfit | pyproject + make | C/Fortran + HDF5 | afterglow fits -> parameterized jet LUTs
JetFit | pyproject | Python | structured jet fitting -> parameter priors + spectral table LUTs
PyGRB | setup.py | Python | prompt emission pulses -> time-domain modulation (FITS-driven)
CompactStar | cmake | C++/TeX | TOV/EOS reference -> C++23 TOV solver
rns | make | C | rotating NS -> frame-dragging metrics reference
nubhlight | make + python | C99 + MPI + HDF5 | GRMHD -> HDF5 disk/jet field ingestion
Blackhole | cmake+conan | C++/GLSL | baseline renderer
PsrSigSim | setup.py | Python | pulsar timing -> periodic emission profiles
Generation-EOS-of-Neutron-Stars-using-MFA-and-Bayesian-Analysis-of-them | requirements | Python | EOS tables -> LUT inputs
spandrel-core | pyproject | Python | cosmology distances -> background scaling
pantheon | pyproject | Python | supernova data -> cosmology validation
xcosm | pyproject | Python | redshift tools -> validation tables
desibao | requirements | Python | BAO distances -> validation only
CERN-Data-Analysis-ALICE-Run3 | none | Python | data pipeline patterns -> QA templates
qgp-light-ion | pyproject/make | Python/TeX | QGP references -> documentation
VAE-Jet | none | Python | ML inference -> optional parameter fitting
Higgs-Boson-Dataset | none | notebooks | data pipeline patterns
Adaptive-ParticlePhysics-Triggers | requirements | Python/TeX | realtime triggers -> frame budget heuristics
big-data-analysis-7.6-million-data-from-cern-proton-proton-collisions | none | notebooks | data pipeline patterns
AliceO2 | cmake | C++/CUDA | HPC patterns -> performance guidance only
opendata.cern.ch | none | Markdown | dataset references
MathScienceCompendium | setup.py/make | Python/TeX | equation validation -> specs
PhysicsForge | make | Python/TeX | equation references -> specs
Colorblindness | make | Python/JS | color palettes -> only if approved
tardis | pyproject | Python (>=3.13) | radiative transfer -> spectral LUTs
torax | pyproject | Python | transport solver -> reference equations
AEGIS-Project | none | Python | instrumentation -> UI guard rails
Superframework | make | Python/TeX | theoretical models -> spec only
lambda-research | make | Python/Rust/C | formal method patterns -> tooling
lambda-synthesis-experiments | none | C/Python | synthesis patterns -> tooling
Johnsons-Narrative-Spittoon-Inversion | none | Markdown | narrative references
compact-common | pyproject | Python | EOS/geodesics -> C++23 physics core
cern-analysis-common | pyproject | Python | stats/IO -> validation utilities
openuniverse-common | pyproject | Python | typed adapters -> offline LUT pipeline
openuniverse-knowledge | none | Markdown | knowledge base references

## Openuniverse top-level build map (current)
Module | Build markers | Notes
--- | --- | ---
AEGIS-Project | none | instrumentation/UI references
ASGARD_GRBAfterglow | pyproject.toml | GRB afterglow solver
Adaptive-ParticlePhysics-Triggers | requirements.txt | trigger heuristics
AliceO2 | CMakeLists.txt | HPC reference, not for runtime
Blackhole | CMakeLists.txt | legacy mirror
CERN-Data-Analysis-ALICE-Run3 | none | data analysis notes
Colorblindness | Makefile | palette research (only if approved)
CompactStar | CMakeLists.txt | TOV/EOS reference
Generation-EOS-of-Neutron-Stars-using-MFA-and-Bayesian-Analysis-of-them | requirements.txt | EOS tables
Higgs-Boson-Dataset | none | data references
JetFit | pyproject.toml | jet fitting priors
Johnsons-Narrative-Spittoon-Inversion | none | narrative references
MathScienceCompendium | setup.py, Makefile, requirements.txt | equation references
PhysicsForge | Makefile, requirements.txt | equation references
PsrSigSim | setup.py, Makefile, requirements.txt, setup.cfg | pulsar timing patterns
PyGRB | setup.py, requirements.txt | prompt emission models
Superframework | Makefile, requirements.txt | theory references
VAE-Jet | none | ML inference
big-data-analysis-7.6-million-data-from-cern-proton-proton-collisions | none | data pipeline patterns
boxfit | pyproject.toml + Makefile | afterglow fits (HDF5/MPI data)
cern-analysis-common | pyproject.toml | stats/IO helpers
compact-common | pyproject.toml | EOS/geodesic reference
demos | none | demo assets
desibao | requirements.txt | BAO validation
docs | none | documentation
domains | none | domain skeletons
grb-common | pyproject.toml | GRB core models
lambda-research | Makefile | tooling patterns
lambda-synthesis-experiments | none | tooling patterns
nubhlight | Makefile + python build scripts | GRMHD output (HDF5)
opendata.cern.ch | none | dataset references
openuniverse | none | submodule container
openuniverse-common | pyproject.toml | typed adapters
openuniverse-knowledge | none | knowledge base
pantheon | pyproject.toml, requirements.txt | cosmology data
qgp-light-ion | pyproject.toml, Makefile | QGP references
rns | none | rotating NS reference
scripts | none | utility scripts
spandrel-core | pyproject.toml | cosmology utilities
tardis | pyproject.toml | radiative transfer
taskmanager_smoke_out | none | task system tests
tests | none | test scaffolding
torax | pyproject.toml | transport solver
xcosm | pyproject.toml, Makefile | redshift tools

## Audit snapshot (2025-12-30)
- Build markers detected (depth<=2): `pyproject.toml`, `CMakeLists.txt`, `Makefile`, `setup.py`
  across modules such as `compact-common`, `grb-common`, `nubhlight`, `tardis`, `boxfit`,
  `ASGARD_GRBAfterglow`, `JetFit`, `CompactStar`, `AliceO2`.
- Confirmed module locations in monorepo:
  `openuniverse/compact-common`, `openuniverse/grb-common`, `openuniverse/nubhlight`,
  `openuniverse/tardis`.
- Separate clones outside monorepo also exist for `openuniverse-common`.

## Audit pass (2025-12-30, README scan)
- `openuniverse` root README enumerates domain clusters; priority modules for Blackhole are
  `compact-common`, `nubhlight`, `tardis`, and the GRB stack (`grb-common`, `ASGARD_GRBAfterglow`,
  `boxfit`, `JetFit`, `PyGRB`).
- `compact-common` confirms EOS/TOV/spacetime (Schwarzschild + Kerr) utilities; use as LUT/validation
  baseline for ISCO/photon/redshift curves.
- `nubhlight` README confirms C99 + MPI + parallel HDF5 + GSL; outputs HDF5 dumps to `dumps/` and
  `restarts/`, built per-problem via `python build.py`.
- `grb-common` README confirms CGS constants, cosmology distances, extinction, and HDF5/CSV schema
  utilities; use for offline LUT generation + validation.
- `tardis` README confirms supernova spectral synthesis; use offline only for spectral LUT calibration
  (heavy Python stack, forked submodule).

## Separate clones outside monorepo (~/Github)
- openuniverse-common: pyproject.toml (Python >=3.10, minimal deps)
- cern-analysis-common: pyproject.toml (not yet audited)
- openuniverse: pyproject.toml + Makefile (root)

## Blackhole internal unused assets (wire-in plan)
- src/physics/kerr.cpp: placeholder derivatives -> implement Kerr geodesic equations.
- shader/geodesic_trace.comp: wired compute path for tiled ray integration; validate vs fragment.
- src/physics/thin_disk.h: add disk emissivity LUT or CPU reference.
- src/physics/synchrotron.h: use for spectral weighting LUTs.
- src/physics/hawking.h: optional debug overlay for temperature/evaporation.
- src/physics/penrose.h: optional diagnostics for energy extraction.
- src/physics/tov.h: use EOS to add compact object presets (future).

## Unit system alignment
- Adopt geometric units in shader (G=c=1) and explicit CGS conversion in C++.
- Define reference mass scale (solar mass) and store in Settings.
- Provide validation curves: r_s, r_ph, r_isco, redshift vs r.

## LUT pipeline notes
- Runtime LUT generation uses `src/physics/lut.h` (emissivity + redshift).
- Optional offline generator: `scripts/generate_luts.py` (uses compact-common if available).
- Asset cache: `assets/luts/` with `emissivity_lut.csv`, `redshift_lut.csv`, and `lut_meta.json`.

## Dependency highlights (from pyproject/requirements)
- compact-common: numpy, scipy, astropy; optional numba, emcee/dynesty/ultranest, matplotlib/corner.
- grb-common: numpy, scipy, astropy; optional h5py/pandas, emcee/dynesty/pymultinest, matplotlib/corner, extinction.
- openuniverse-common: no runtime deps; optional hypothesis/deal/crosshair; dev uses pytest/ruff/mypy.
- ASGARD_GRBAfterglow: numpy, scipy, astropy, matplotlib, emcee, corner, extinction, schwimmbad, h5py.
- boxfit: HDF5 dev libraries; MPI optional; BOX datasets downloaded separately.
- nubhlight: C99 + MPI + (parallel) HDF5 + GSL; optional gfortran for opacities.
- tardis: Python >=3.13; large dependency stack; use offline for spectral LUT calibration only.
- JetFit: pyproject targets Python >=3.9; legacy conda env file pins py27. Uses `Table.h5` spectral LUTs.
- PyGRB: FITS download + nested sampling (bilby + nestle); setup.py pins Python <3.9.

## Additional module notes
- CompactStar (C++17): TOV + Hartle solvers, EOS pipelines, diagnostics; strong reference for structural solver
  architecture and schema-driven diagnostics.
- rns (C): rotating neutron star models with tabulated EOS + uniform rotation sequences; use for
  frame-dragging and quadrupole validation baselines.
- pantheon/spandrel: SN Ia synthesis + Pantheon+SH0ES dataset; use for validation curves only.
- desibao: DESI Y3 BAO + systematics analysis; use for validation inputs only.
- xcosm: cosmology + data loaders; reference-only for redshift/distance baselines.
- cern-analysis-common: HEP I/O + plotting utilities; patterns only (ROOT/HDF5 I/O,
  Lorentz four-vectors, clopper-pearson intervals), no runtime coupling.
- PsrSigSim: pulsar signal simulator; use only for periodic emission profile ideas.
- Generation-EOS-of-Neutron-Stars-using-MFA-and-Bayesian-Analysis-of-them: QHD/MFA EOS + M-R curves
  in natural units; use for EOS validation inputs.
- Adaptive-ParticlePhysics-Triggers: trigger-control algorithms + dataset schemas; use for frame
  budget/control heuristics only.
- VAE-Jet: ML anomaly detection (TensorFlow); not runtime, but can inform offline parameter fitting.

## GRB module notes (cleanroom targets)
- grb-common: CGS constants + cosmology distance relations + extinction curves; use for offline LUT
  generation and validation inputs (no runtime dependency).
- boxfit: afterglow hydrodynamics in precomputed HDF5 “box” files; use only as a data schema
  source for LUT generation and interpolation ranges. HDF5 outputs use datasets like `F`, `t_obs`,
  `z`, `dL`, `ur_min/max`, `uphi_min/max`, `R_50/75/95/99/100`, `I`, `ur`, `uphi`.
- JetFit: relies on `Table.h5` spectral function table; use as a spectral LUT input reference only.
- PyGRB: pulse-model fitting with nested sampling; use for prompt-emission time modulation curves.
- grb-common/io/schemas.py: LightCurve + Spectrum data classes define unit conventions for LUT I/O
  (time in seconds, flux in erg/cm^2/s or erg/cm^2/s/Hz, frequency in Hz, wavelength in Angstroms).

## GRB/afterglow submodule notes (openuniverse/*)
- ASGARD_GRBAfterglow: Fortran + OpenMP (WENO5, implicit scheme) for afterglow electron spectra,
  synchrotron + SSC + SSA + gamma-gamma; use as equation/feature checklist for LUTs only.
- ASGARD includes WENO5 and implicit solvers plus Compton cooling; use for algorithm checklist
  and regression curve generation (offline only).
- boxfit: compressed 2D jet simulations (RAM RHD) stored as HDF5 “box” data files; interpolation
  over explosion/observer parameters for light-curve synthesis. Requires external box datasets.
- JetFit: structured jet model with spectral function `Table.h5`; interpolates over axes in
  `Axis` (tau, Eta0, GammaB, theta_obs) and tables `f_peak`, `f_nu_c`, `f_nu_m`; use as
  spectral LUT reference only.
- PyGRB: BATSE FITS download + pulse models (FRED etc.) with nested sampling; use for
  time-domain modulation curves and pulse envelope LUTs.
- PyGRB backend rate_functions.py: Gaussian, FRED, and FREDx pulse shapes with parameters
  (start, scale, tau, xi, gamma, nu); use as envelope presets for LUT generation.

## Cosmology module notes (spandrel-core/xcosm/pantheon)
- spandrel-core: SN Ia likelihood + constants; use for cosmology baseline checks only.
- xcosm: data loaders (Pantheon/BAO/GW) + models; use as validation inputs, not runtime.

## Openuniverse domain package notes (openuniverse/domains/*)
- compact/spacetime/kerr.py: formula set matches BPT ISCO + photon orbit + frame-dragging; good
  cleanroom reference for equations/units (already mirrored in C++).
- compact/spacetime/geodesics.py: uses simplified/damped ODEs for pedagogical trajectories, not
  physically accurate; do not port as-is. Use only for API shape and validation harness ideas.
- compact/spacetime/schwarzschild.py: canonical CGS formulas for r_s, redshift, escape velocity;
  aligns with current C++ cleanroom constants.

## compact-common module notes (openuniverse/compact-common)
- spacetime/kerr.py: includes horizons, ISCO (Bardeen/Press/Teukolsky), photon orbit, ergosphere,
  and frame-dragging. Inputs are mass [g] and spin parameter a [cm] with a* = a/M.
  Functions: `kerr_horizons`, `kerr_isco`, `kerr_photon_orbit`, `frame_dragging`, `kerr_ergosphere`.
- structure/tov.py: TOV solver with pressure-density interpolation (linear + optional numba),
  RK4 integrator fallback, and solve_ivp reference; includes unit conversions from MeV/fm^3.
- spacetime/geodesics.py: SciPy ODE integration but uses damped dr/dlambda; not physically accurate
  and not suitable for cleanroom porting (use only for interface shape).
- spacetime/schwarzschild.py: canonical CGS definitions for r_s, r_ph, r_isco, redshift, proper
  distance, orbital period; use for LUT validation targets.
- eos/*: polytrope, sigma-omega MFA, Fermi gas, tabulated EOS; use as offline LUT generators.
- structure/*: TOV solver + tidal deformability; use as reference curves for tests, not runtime.

## openuniverse-common module notes (openuniverse/openuniverse-common)
- units.py: CODATA 2022 CGS constants + conversions; can seed C++ constants and unit helpers.
- validation.py: pre/postcondition + finite/positive guards; port as lightweight runtime validators
  to catch NaNs/infinities during physics steps.
- registry.py: simple name->factory registry pattern; useful for LUT or model registries.
- types.py: DatasetRef/ArtifactRef/RunResult protocols; useful for offline pipeline metadata.
- adapters/*: thin wrappers for tardis/spandrel/xcosm/torax/pantheon; treat as schema hints only.

## Cleanroom phases (high level)
P0. Spec extraction: read equations and units from each submodule (no code reuse).
P1. Core physics library: C++23 Schwarzschild/Kerr geodesics + EOS + orbits.
P2. LUT pipeline: generate emissivity/redshift/opacity tables offline.
P3. GPU integration: GLSL sampling paths + compute shader option.
P4. Validation: numeric tests + render regression images + performance benches.

## Data ingestion plan
- Use HDF5 reader for GRMHD outputs (nubhlight). Keep runtime optional.
- Define a common field schema: density, temperature, velocity, magnetic field.
- Add a small converter tool to transform datasets to compact textures.

## Nubhlight HDF5 ingestion (draft)
1. Inventory `core/` HDF5 schema via `core/opac_emis_hdf.c` + `core/io.c` (field names, shapes).
   - Opacity table datasets: `lrho`, `lT`, `Ye`, `lnu`, `emis`, `opac`.
   - Dimension attributes: `numRho`, `numT`, `numYe`, `numNu`.
2. Note build/output layout: per-problem `prob/*/build.py` creates binaries; runtime writes `dumps/`
   and `restarts/` directories in the output folder.
3. XDMF metadata in `core/xdmf_output.c` shows primary datasets:
   - `grid.h5`: `XFcart`, `Lambda_h2cart_con`, `Lambda_h2cart_cov`, `gcon`, `gcov`, `gdet`, `alpha`.
   - `dump_########.h5`: primitives dataset `P` plus derived fields `divb`, `jcon`, `PRESS`, `ENT`,
     `TEMP`, `CS2`, `Qvisc`, `Qcoul`, `nph`, `Jrad`, `Rmunu`.
4. Define unit conversion spec (CGS -> normalized geometric units for shader).
5. Build offline converter to pack fields into 3D textures + metadata JSON.
5. Add dataset loader in C++ with explicit versioned schema checks.
6. Validate against a small reference dump (checksum + min/max checks).

## Radiative transfer LUT plan (tardis)
1. Use TARDIS to generate spectral response curves for representative SN ejecta.
2. Extract wavelength->intensity curves and compress into 1D/2D LUTs.
3. Map LUTs into shader space (normalized wavelength or frequency bins).
4. Add C++ LUT loader and a debug overlay to compare against CPU reference.
5. Reference algorithms: `tardis/transport/montecarlo/montecarlo_main_loop.py` (packet transport),
   `tardis/transport/geometry/calculate_distances.py` (distance-to-boundary/line/scattering) for
   cleanroom algorithm guidance only.

## GRB modulation plan (grb-common / ASGARD / boxfit / JetFit / PyGRB)
1. Define a common time-domain modulation interface (flux(t, nu)).
2. Use grb-common constants/cosmology for distance and k-corrections.
3. Offline: run ASGARD/boxfit/JetFit to emit time-frequency grids -> LUTs.
4. Runtime: sample LUTs to modulate disk emissivity and background sky.
5. Validation: compare a reference light-curve snapshot to source model output.

## Unit alignment + validation harness (compact-common)
1. Fix a single unit system (CGS in C++ with explicit G=c=1 conversions).
2. Generate reference tables (r_s, r_ph, r_isco, redshift(r)) via compact-common.
3. Store CSV/JSON assets and compare in physics_test with tolerances.
4. Add optional plot script to visualize residuals for regression checks.

## Validation strategy
- Python reference scripts (offline) produce truth tables and images.
- C++ unit tests compare against reference CSV/LUTs with tolerances.
- Shader validation uses glslangValidator via `cmake/ValidateShader.cmake` + render-to-texture goldens.

## Notes and constraints
- Colorblindness assets are not UI requirements; only palette research if approved.
- Large CERN datasets are reference-only; no runtime integration planned.
- All cleanroom ports must be documented with equation sources.

## Related docs
- `docs/CLEANROOM_PORT_MAP.md`
- `docs/LUT_PIPELINE_PLAN.md`
- `docs/GRMHD_INGESTION_PLAN.md`
- `docs/GRB_MODULATION_PLAN.md`
- `docs/RADIATIVE_TRANSFER_LUT_PLAN.md`
