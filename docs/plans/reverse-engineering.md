# Reverse Engineering Plan (Pure C++23/GLSL460)

Scope and granular TODOs to port advanced physics into Blackhole without code reuse.

1) GRMHD / Kerr BH Rendering
- Derive Kerr geodesics via Hamilton-Jacobi separation (E, Lz, Q), Mino time lambda.
- Implement radial/latitudinal potentials R(r), Theta(theta); root finding; turning-point handling.
- Photon ring and ISCO: compute r_ph(a), r_ISCO(a) (prograde/retrograde) from Bardeen-Press-Teukolsky.
- Redshift g = nu_obs/nu_emit from k*u; include Doppler and beaming, aberration.
- Polarized synchrotron emissivity j_nu ~ n_e B^alpha; Stokes IQUV options; precompute LUTs.
- Magnetic field models: toroidal/poloidal, MAD/SANE parameterizations; user controls.
- GLSL integration kernel: per-fragment Kerr ray-march with adaptive stepping, bailout, caustic-aware refinement.
- Validation: reproduce known photon ring thickness vs spin, ISCO shifts, g-factor histograms.

2) GRB Afterglow / Jet Microphysics
- Shock params: eps_e, eps_B, p; compute gamma_m, B, n_e.
- Spectral breaks: nu_a, nu_m, nu_c with temporal evolution; piecewise synchrotron spectrum.
- Jet geometry: top-hat/structured Gaussian core; off-axis viewing; lateral expansion.
- Lightcurves: F_nu(t, nu) using boxfit-like scalings; microphysical parameter sweeps.
- Coupling: transient hotspots in accretion disk, lensing flares, time-dependent uniforms.
- Validation: reproduce canonical afterglow slopes and break times for benchmark bursts.

3) EOS / Compact Objects
- TOV solver (static spherically symmetric) with tabulated EOS (rho, P, eps); RK4 + causal checks.
- Generate M-R curves and compactness; presets for soft/stiff EOS.
- Comparative lensing scenes: NS vs BH, deflection angle maps.
- Kerr vs Schwarzschild toggles; spin-dependent caustic visualization.

4) Cosmology / Radiative Transport
- Cosmological redshift z, luminosity distance D_L(z) and K-corrections.
- Radiative transfer: I_nu along geodesics with absorption/emission; thin/thick regimes.
- Physically based tone mapping: integrate L_nu to scene exposure; ACES + scientific calibration.

5) Data/Analysis Cores
- GPU histogramming of g-factor, impact parameters; prefix-sum based bins.
- Vectorized kernels for uniform packing; uncertainty overlays from propagated errors.
- Debug panels: parameter posteriors, confidence bands, sensitivity.

Practical Milestones
- M1: Kerr geodesic integrator (CPU C++), tests; shader hooks.
- M2: Synchrotron LUTs + emissivity shader; magnetic field UI.
- M3: GRB transient system + time uniforms; benchmark lightcurves.
- M4: TOV + EOS presets; scene toggles.
- M5: Radiative transport exposure; histogram/overlay tooling.

All derivations will reference primary literature and be unit-tested; no external code copied.
