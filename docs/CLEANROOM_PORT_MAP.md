# Cleanroom Port Map

This map connects external modules to cleanroom C++23/GLSL targets.
No source code is copied; only equations, data formats, and behaviors.

## Compact Objects
- compact-common/spacetime -> `src/physics/kerr.*`, `src/physics/schwarzschild.*`
- compact-common/spacetime/kerr.py -> horizons, ISCO, photon orbit, frame dragging, ergosphere (CGS inputs)
- compact-common/spacetime/schwarzschild.py -> r_s, g_tt/g_rr, redshift, photon sphere (CGS inputs)
- compact-common/structure/tov -> TOV solver + pressure-density interpolation (future `src/physics/tov.*`)
- compact-common/structure/tov.py -> MeV/fm^3 to CGS conversions + RK4/solve_ivp patterns; optional numba
- compact-common/structure/tidal -> Love numbers/tidal deformability (future validation)
- CompactStar -> C++17 TOV + Hartle solvers, state/driver separation, diagnostics (design reference)
- Generation-EOS-of-Neutron-Stars -> QHD/MFA EOS pipeline + Bayesian fitting (validation only)
- rns -> rotating star validation for TOV extensions

## Accretion / Emission
- nubhlight -> HDF5 density/temp/velocity/B ingestion -> 3D textures
  (dump keys: `P` with `vnams`, `t`, `dump_cnt`, `jcon`, optional `Rmunu`, `Jrad`,
  `Nem`, `Nabs`, `Nsc`)
- tardis -> spectral response LUTs for emission weighting

## GRB / Afterglow
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

## Visualization References
- openuniverse/Blackhole -> legacy OpenGL black hole renderer + reference links

## Cosmology (validation)
- spandrel-core -> lightweight FlatLambdaCDM + distance modulus; use for LUT validation
- pantheon/xcosm/desibao -> dataset loaders + distance curves (validation only)
- desibao -> DESI Y3 BAO pipeline (validation only)

## Signals / Timing (reference)
- PsrSigSim -> pulsar timing noise models (future GW/TOA validation reference)

## Knowledgebase / Research
- knowledge -> LFS store for papers/datasets (reference only)
- MathScienceCompendium -> fact-checking patterns + bibliography management (reference only)
- Superframework -> speculative fractional-calculus framework (do not integrate into runtime)

## HEP / Data Pipelines (reference only)
- Adaptive-ParticlePhysics-Triggers -> HDF5 schema patterns + anomaly scoring pipeline
- AliceO2 + CERN-Data-Analysis-ALICE-Run3 -> ROOT-based data flows, cut/efficiency reporting
- AEGIS-Project -> real-time signal statistics + Welford-style monitoring patterns

## HUD / Performance
- MangoHud -> FPS/frametime percentiles, GPU timings, overlay layout

## Rendering Patterns
- graphics-programming (TinyGL/PortableGL/SGI): matrix + clipping + viewport transforms for
  optional CPU fallback/validation.
  - TinyGL: scanline rasterization, fixed-point edge stepping.
  - PortableGL: edge-function rasterization, per-pixel barycentric interpolation.
  - Shared math: perspective-correct interpolation formula + Sutherland-Hodgman clipping.
- Xinim: renderer concept with `draw_text` + buffer rendering (HUD overlay patterns).
- microwindows64: minimal windowing/Nano-X + input notes for HUD/input design ideas.

## Tooling Patterns
- common -> registry/units patterns for model factories
- common/units.py -> CODATA 2022 CGS constants for cross-checking
- common/validation.py -> finite/positive guards for runtime sanity checks
- common/types.py -> DatasetRef/RunResult schemas for offline pipeline metadata
- common/adapters/* -> schema hints for tardis/xcosm/torax/pantheon integration
- cern-analysis-common -> I/O/validation patterns (offline only)

## Port Sequencing (priority order)
1) compact-common (spacetime + EOS): ISCO/photon/redshift curves, validation LUTs.
2) common: schema contracts + validation guards for offline pipelines.
3) grb-common/JetFit/boxfit: GRB light-curve + spectral LUT inputs.
4) nubhlight: GRMHD HDF5 ingestion + texture packing.
5) tardis: spectral calibration LUTs (offline only).
6) spandrel/xcosm/pantheon: cosmology validation curves (offline only).

## Attribution / citation notes (cleanroom references)
- ASGARD_GRBAfterglow: README requires explicit attribution; cite Ren et al. 2024 ApJ 962:115.
- boxfit: cite Van Eerten et al. 2012 ApJ 749:44 for afterglow fits.
- nubhlight: cite Miller et al. 2019 ApJS 241:2 and Ryan et al. 2015 ApJ 807:31.
- tardis: cite Kerzendorf & Sim 2014 MNRAS 440:387; add Vogl et al. 2019 A&A 621:A29 if using Type II.
- grb-common: cite project if using its schemas/constants as validation baselines.
- compact-common/CompactStar/rns: cite original solver references if metrics/EOS curves are published.
