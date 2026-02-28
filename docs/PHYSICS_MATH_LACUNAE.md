# Physics, Mathematics, and Performance Lacunae

**Date:** 2026-02-27
**Scope:** Structured gap analysis of the Blackhole simulation -- physics fidelity,
mathematical constructs (4D slicing, hyperwaves, Newman-Penrose), and GPU/algorithmic
performance. This is a reference document; no code changes are proposed here.

---

## Table of Contents

1. [What Is Fully Implemented (Baseline)](#1-what-is-fully-implemented-baseline)
2. [Physics Lacunae](#2-physics-lacunae)
   - [2.1 GRMHD Solver (CRITICAL)](#21-grmhd-solver-critical--0-implemented)
   - [2.2 Radiative Transfer Equation (HIGH)](#22-radiative-transfer-equation-high--0-solved)
   - [2.3 4D Slicing and Hyperboloidal Constructs (ABSENT)](#23-4d-slicing--hyperboloidal-constructs-absent)
   - [2.4 Gravitational Wave Physics Gaps](#24-gravitational-wave-physics-gaps)
   - [2.5 Cauchy Horizon and Strong Cosmic Censorship](#25-cauchy-horizon-and-strong-cosmic-censorship)
   - [2.6 Integration Method Gaps](#26-integration-method-gaps)
   - [2.7 Float32 GPU Precision Near Horizon](#27-float32-gpu-precision-near-horizon)
   - [2.8 Newman-Penrose Formalism (ABSENT)](#28-tetradnewman-penrose-formalism-absent)
   - [2.9 Equation of State and Matter Fields (ABSENT)](#29-equation-of-state-and-matter-fields-absent)
3. [Performance Lacunae](#3-performance-lacunae)
4. [Summary Table by Priority](#4-summary-table-by-priority)
5. [Conan / C++ Library Scope for Future Buildout](#5-conan--c-library-scope-for-future-buildout)

---

## 1. What Is Fully Implemented (Baseline)

| Domain                           | Status | Key Files / Symbols                                      |
|----------------------------------|--------|----------------------------------------------------------|
| Schwarzschild metric + geodesics | 100%   | schwarzschild.h, geodesics.h                             |
| Kerr metric (Boyer-Lindquist)    | 100%   | kerr.h, verified/kerr.h                                  |
| Kerr geodesics (Mino-time RK4)   | 100%   | kerr.cpp, verified/rk4.h                                 |
| Ergosphere, horizons, ISCO       | 100%   | kerr.h:129,147,183,215-238                               |
| Frame dragging (Lense-Thirring)  | 100%   | kerr.h:314, frame_dragging_test.cpp                      |
| Carter constant conservation     | 100%   | verified/energy_conserving_geodesic.hpp:66-125           |
| Penrose process + BZ mechanism   | 100%   | penrose.h:67-289                                         |
| Novikov-Thorne accretion disk    | 100%   | novikov_thorne.h, disk_profile.glsl                      |
| Synchrotron spectrum (formulas)  | 95%    | synchrotron.h, synchrotron_emission.glsl                 |
| Hawking radiation (formulas)     | 30%    | hawking.h (no thermodynamic coupling)                    |
| Doppler beaming                  | 100%   | doppler.h                                                |
| GW inspiral (3.5PN + ringdown)   | 100%   | gravitational_waves.h (344 LOC)                          |
| GPU RK4 geodesic integrator      | 95%    | integrator.glsl, verified/rk4.glsl                       |

---

## 2. Physics Lacunae

### 2.1 GRMHD Solver (CRITICAL -- 0% implemented)

**What is missing:** The 3D general-relativistic magnetohydrodynamics equations in
conservative form. The codebase has tile streaming infrastructure (grmhd_streaming.h)
and a nubhlight HDF5 ingestion tool (~80% complete), but NO native solver.

**Mathematical gap:**

The conservative GRMHD evolution equations are:

```
partial_t(sqrt(-g) U) + partial_i(sqrt(-g) F^i) = S
```

where `U = [rho u^t, T^t_nu, B^k]` are conserved variables (rest mass density flux,
stress-energy tensor components, magnetic field components in coordinate basis).

Key absent physics:

- **Magnetorotational instability (MRI):** The primary mechanism driving angular
  momentum transport in accretion disks. MRI channel modes have wavelength
  `lambda_MRI ~ 2*pi * sqrt(16/15) * v_A / Omega` where `v_A` is the Alfven speed
  and `Omega` is the orbital angular velocity. Without MRI the accretion is
  physically unmotivated (alpha-disk prescription only).

- **Magnetic reconnection:** Fast reconnection in current sheets (Sweet-Parker
  vs Petschek regimes) drives particle acceleration and jet launching. The
  Blandford-Znajek jet power formula `P_BZ = (kappa/4pi) * Omega_H^2 * Phi_BH^2`
  is present in penrose.h as a formula, but the magnetic flux `Phi_BH` has no
  computed value from a real MHD solution. The formula is cosmetic.

- **3D pressure and density volume:** The disk is Novikov-Thorne (zero thickness)
  or procedural noise. A real GRMHD volume is a 4D dataset (r, theta, phi, t).

**Architectural note:** A real-time 3D GRMHD solver is ~50k-100k LOC and requires
adaptive mesh refinement (AMR). The tile streaming pipeline is intentionally designed
to INGEST pre-computed simulation output (e.g., from nubhlight/HARM/KORAL), not to
solve in situ. This is the correct architectural choice for a real-time renderer.

---

### 2.2 Radiative Transfer Equation (HIGH -- 0% solved)

**What is missing:** The formal solution of the radiative transfer equation (RTE):

```
dI_nu/ds = j_nu - alpha_nu * I_nu
```

along each geodesic ray. The simulation uses LUT-backed emissivity and redshift but
does NOT march through a volumetric opacity field.

**Mathematical gaps:**

- **Optical depth integration:** `tau_nu = integral(alpha_nu ds)` along the geodesic.
  Without this, all emitting regions are treated as optically thin.

- **Frequency redistribution (Comptonization):** Photon frequencies shift when
  scattering off hot electrons in the corona. The Klein-Nishina cross section is
  present in scattering_models.h but is NOT called during ray marching.

- **Polarized radiative transfer:** The Stokes vector `(I, Q, U, V)` transport
  requires a 4x4 Mueller matrix propagated along each geodesic (Broderick & Blandford
  2004). This is completely absent. It matters critically for EHT polarimetry and
  spin measurements via linear polarization.

- **Fe K-alpha line at 6.4 keV:** The relativistically broadened iron emission line
  from the disk corona is a primary spin measurement observable. Listed as a Phase 6.3
  future task; not yet started.

---

### 2.3 4D Slicing / Hyperboloidal Constructs (ABSENT)

The simulation works entirely in Boyer-Lindquist (BL) coordinates -- a spacelike
`t = const` foliation. There is no hyperboloidal or null-adapted coordinate system.

#### a) Hyperboloidal foliations

Hyperboloidal coordinates reach future null infinity (scri+) without compactification
artifacts. They are essential for:

- Clean gravitational wave extraction at null infinity (Cauchy-characteristic
  extraction, CCE). Without this, GW waveforms extracted at finite radius carry
  systematic near-zone errors.
- Avoiding the Gibbs phenomenon from coordinate singularities at the horizon.
- Computing the Bondi mass aspect and news function (the radiative degrees of freedom
  that characterize outgoing gravitational radiation).

The simulation's `gravitational_waves.h` uses the quadrupole formula and 3.5PN
approximants -- it does NOT extract waveforms from a numerical spacetime at scri+.

#### b) Penrose diagrams / conformal compactification

The causal structure of Kerr spacetime (two horizons, ring singularity, Cauchy
horizon instability, timelike singularity, distinct asymptotic regions) is not
visualized conformally. The ergosphere boundary is shown in the wiregrid shader,
but the interior causal structure is unrepresented.

#### c) Cauchy horizon (inner horizon) dynamics

`r_- = M - sqrt(M^2 - a^2)` is computed (kerr.h:147) but its physics is absent:

- **Misner-Sharp mass inflation:** Infalling observers see infinite blueshift of
  outgoing radiation at `r_-`. This is a classical instability (Dafermos-Luk 2017
  on strong cosmic censorship): energy density diverges at the Cauchy horizon even
  for regular initial data.

- **BKL oscillations near the spacelike singularity** (Schwarzschild case):
  Chaotic mixmaster (Belinskii-Khalatnikov-Lifshitz) dynamics govern the approach
  to the singularity. Not present.

#### d) 3+1 ADM decomposition

The simulation integrates geodesics in BL coordinates but does NOT decompose
spacetime into spatial slices + lapse function + shift vector. ADM decomposition is
required for:

- BSSN/Z4c evolution equations for numerical relativity output.
- Apparent horizon finding: the surface where the null expansion `Theta = 0`.
- Trapped surface detection (needed for horizon finders in NR codes).

#### e) Null slicing / characteristic formulation

Bondi-Sachs coordinates are adapted to outgoing null cones. Used in
Cauchy-characteristic extraction (CCE) for GW waveforms at scri+. The GW output
uses quadrupole + 3.5PN -- it does not extract from a numerical spacetime.

---

### 2.4 Gravitational Wave Physics Gaps

`gravitational_waves.h` is substantive (344 LOC), implementing:
- Chirp mass, frequency evolution (Peters 1964)
- 3.5PN phase (Blanchet 2014, `gw_phase_3p5pn`)
- Plus/cross polarizations
- Schwarzschild QNM ringdown
- GW luminosity and energy radiated (NR fit, Jimenez-Forteza 2017)
- Binary inspiral waveform generation

**Remaining gaps:**

#### a) Spin-orbit and spin-spin coupling in PN phase

The current `gw_phase_3p5pn` (gravitational_waves.h:284) includes:
- 1.5PN tail: `-16*pi*v^3` (correct)

Missing:
- Spin-orbit (1.5PN): `delta_psi_SO = (25/336 + 11*eta/12) * chi_eff * v^3`
  (Kidder 1995; Blanchet 2014 Table 3)
- Spin-spin (2PN): `delta_psi_SS = -50*eta*chi1*chi2*v^4`
  (Cutler-Flanagan 1994)
- These corrections are O(10%) for dimensionless spins `a* > 0.3`.

#### b) Precessing binaries (generic spins)

The current model assumes aligned spins (no orbital precession). For generic spin
orientations, the orbital plane precesses and produces characteristic amplitude and
phase modulation (the "windmill" waveform). This requires the SpinTaylorT4
approximant (Buonanno-Chen-Vallisneri 2003). Absent.

#### c) Kerr QNM ringdown

`qnm_frequency_schwarzschild` (gravitational_waves.h:413) uses the scalar fit
`omega_22 = 0.3737/M`. The Kerr QNM frequencies depend on spin:

```
omega_22(a*) = omega_R(a*) + i/tau(a*)
```

where `omega_R` and `tau` are tabulated in Berti, Cardoso, Starinets (2009). The
code itself documents this: "For Kerr, depends on spin (Berti et al. 2009)."
The Kerr branch is unimplemented.

#### d) Gravitational wave memory effect

After the GW passes, the metric permanently shifts by a nonzero amount:

```
delta h_ij = (4G/c^4 r) * integral_{-inf}^{+inf} (dE_GW/d Omega) n_i n_j d Omega dt
```

This Christodoulou (1991) memory is not computed. It is a DC shift observable by
LISA for massive binaries and by pulsar timing arrays (PTAs) for SMBH mergers.

#### e) Higher multipoles (l > 2)

Only the dominant (l=2, m=2) mode is implemented. For unequal-mass mergers
(q != 1), subdominant modes carry significant power:
- (3,3): ~10% of flux for q = 0.5
- (4,4): ~3% for q = 0.5
- (2,1): ~2% (associated with center-of-mass recoil, GW kick)

---

### 2.5 Cauchy Horizon and Strong Cosmic Censorship

`r_-` is computed (kerr.h:147) but:

- **Strong Cosmic Censorship (SCC):** Penrose (1969) conjectured that generic
  initial data should not produce a Cauchy horizon that is globally hyperbolic
  extendible. Dafermos-Luk (2017) proved that the Kerr Cauchy horizon is C^0
  but NOT C^1 inextendible for a massive scalar field. This means GR breaks down
  at `r_-` in a precise mathematical sense. The simulation treats `r_-` as a
  boundary without flagging this.

- **Mass inflation (Poisson-Israel 1990):** The energy density of infalling matter
  diverges at `r_-` due to the blueshift of outgoing perturbations. This requires a
  nonlinear perturbation solver. Not present.

- **Geodesic completeness warning:** The simulation does not warn when an integrated
  null geodesic crosses `r_-` into a region where deterministic GR evolution fails.

---

### 2.6 Integration Method Gaps

**Current state:** RK4 (4th order) with adaptive step (h*1.2 growth / h*0.5
reduction), Mino-time stepping for Kerr geodesics.

#### a) Not symplectic

The integrator preserves the null constraint `g_mu_nu u^mu u^nu = 0` by
RESCALING the 4-velocity after each step. This is NOT a symplectic integrator.
Consequences:
- Phase space volume is not exactly preserved.
- Energy errors can drift secularly (bounded only by the rescaling).

A Yoshida (1990) 4th-order symplectic integrator or implicit midpoint rule would
preserve the symplectic structure exactly, eliminating secular drift.

#### b) No dense output / event detection

The integrator cannot accurately locate the moment a ray crosses the photon sphere
or horizon. It checks `r < r_s + epsilon` after each full step, which can miss or
mis-locate the crossing by up to one full step size. An event-detection scheme
(bisection or Illinois algorithm on the zero-crossing condition) is absent.

#### c) Simplified adaptive step control

The adaptive step heuristic is `h *= 1.2` (grow) / `h *= 0.5` (shrink). A proper
Dormand-Prince RK45 with embedded O(h^4) error estimate gives guaranteed local
accuracy with a principled step size controller (e.g., PI controller as in
Hairer-Norsett-Wanner). This gives the same accuracy with fewer function evaluations.

#### d) No analytic Kerr geodesic (elliptic functions)

For Kerr, the geodesic equations are exactly separable and the orbit integrals can
be expressed in closed form via Jacobi elliptic functions (Fujita-Hikida 2009;
Gralla-Lupsasca 2020). An analytic solution would replace the RK4 integration loop
for non-captured rays with O(1) cost per geodesic (one elliptic function evaluation),
compared to O(N_steps) for RK4. This is especially impactful for near-photon-sphere
orbits where RK4 requires hundreds of steps.

---

### 2.7 Float32 GPU Precision Near Horizon

The GPU uses float32. Near the horizon `r ~ r_+`, the Boyer-Lindquist metric
component:

```
g_rr = Sigma / Delta = (r^2 + a^2 cos^2(theta)) / (r^2 - r_s*r + a^2)
```

diverges as `r -> r_+` (coordinate singularity). Float32 has ~7 decimal digits of
precision; `Sigma/Delta` can reach `10^4 - 10^6` near the horizon, losing 4-6 digits
of mantissa. The 1e-6 relative error documented in shader headers is likely optimistic
for rays that pass within `1.01 * r_+` of the horizon.

**Fix:** Switching to Kerr-Schild (horizon-penetrating) coordinates eliminates this
divergence. In Kerr-Schild coords the metric is analytic across the horizon:

```
g_mu_nu = eta_mu_nu + 2H * l_mu * l_nu
```

where `H = Mr/Sigma` and `l_mu` is an ingoing null covector. Both are O(1) at the
horizon. Estimated effort: ~200 LOC in integrator.glsl + verified/kerr.glsl.

---

### 2.8 Tetrad/Newman-Penrose Formalism (ABSENT)

The Newman-Penrose (NP) null tetrad formalism `(l^mu, n^mu, m^mu, mbar^mu)` and
the Weyl scalars `(Psi_0 ... Psi_4)` are completely absent.

Why this matters:

- **GW extraction:** `Psi_4 = -d^2 h / dt^2` at scri+ gives the outgoing
  gravitational radiation in a gauge-invariant form. This is the standard extraction
  method in numerical relativity (NR).

- **Teukolsky equation:** Governs perturbations of Kerr spacetime (scalar, vector,
  tensor modes). The Teukolsky (1972) equation in BL coords is separable:

  ```
  [(r^2+a^2)^2/Delta - a^2 sin^2(theta)] partial_{tt} Psi
  + 4Mar/Delta partial_{t phi} Psi + ... = 0
  ```

  Solving it gives QNM spectra with arbitrary spin `a*`, not the scalar fit
  `omega_22 = 0.3737/M` currently used.

- **Gravitational self-force / EMRI:** Metric perturbation theory in the
  Regge-Wheeler-Zerilli or Lorenz gauge is required for extreme-mass-ratio inspirals
  (EMRIs) relevant to LISA. Not in scope for this renderer but architecturally
  adjacent to the Teukolsky machinery.

---

### 2.9 Equation of State and Matter Fields (ABSENT)

- **3D EOS:** The accretion disk uses Novikov-Thorne (zero-thickness) or procedural
  noise. No 3D density/pressure/temperature volume exists. A gamma-law EOS
  `p = (gamma-1)*u` or tabulated EOS (neos, SRO) for neutron star matter is absent.

- **Pair production / QED effects:** Near the magnetosphere, the electric field
  can approach the Schwinger critical field `E_crit ~ 1.3e18 V/m` for
  ultra-magnetized black holes (magnetar-like regime). Pair cascades alter the
  magnetospheric structure. Not present and likely out of scope.

---

## 3. Performance Lacunae

### 3.1 Float32 Near Horizon (see Section 2.7)

Switching to Kerr-Schild coordinates on the GPU path eliminates the BL coordinate
singularity at the horizon. Estimated effort: ~200 LOC in integrator.glsl.

### 3.2 Analytic Kerr Geodesic (Elliptic Functions)

The Gralla-Lupsasca (2020) analytic solution via Jacobi elliptic functions and
Mino-time integrals replaces the RK4 loop for non-captured rays with O(1) cost
per geodesic. Boost.Math 1.90.0 (already present) provides `boost::math::jacobi_sn`,
`jacobi_cn`, `jacobi_dn`. Estimated effort: ~500-800 LOC in CPU path.

### 3.3 Compute Raytracer Parity (Issue-008, ACTIVE)

The compute path has FP arithmetic differences from the fragment path due to
FMA (fused multiply-add) contraction ordering. Only 11/12 presets pass at current
tolerance. Root cause is documented but not eliminated. The fix requires either
disabling FMA contraction (`-ffp-contract=off` or `precise` GLSL pragma) uniformly,
or tightening the tolerance accounting for FMA-induced divergence.

### 3.4 Async GRMHD Tile Streaming (NOT IMPLEMENTED)

`grmhd_streaming.cpp` contains 7 TODO comments (lines 112-176) for async loading.
The LRU cache architecture is designed but the binary read / decompression /
OpenGL PBO upload pipeline is not wired. This blocks GRMHD playback entirely.

The path to completion:
1. Wire HighFive HDF5 reader (already in conanfile.py) to tile cache.
2. Implement OpenGL PBO double-buffering for async GPU upload.
3. Use TaskFlow (already in conanfile.py) for background decompression threads.
4. Wire playback_control.h timeline to tile eviction.

Estimated effort: ~800 LOC.

### 3.5 No AMR Sampling Along Geodesic

The RK4 adaptive step size reacts to local integration error but does NOT refine
near physics boundaries (photon sphere, horizon, disk midplane). An
AMR-style refinement triggered by curvature invariants (Kretschmer scalar
`K = R_abcd R^abcd`, which diverges toward the singularity) would give better
accuracy where it matters with fewer steps elsewhere.

---

## 4. Summary Table by Priority

| Gap                                       | Type      | Priority | Effort (LOC est.) |
|-------------------------------------------|-----------|----------|--------------------|
| GRMHD solver (native)                     | Physics   | CRITICAL | 50k+ (out of scope)|
| Radiative transfer (volumetric RTE)       | Physics   | HIGH     | ~10k               |
| Polarized radiative transfer (Stokes)     | Physics   | HIGH     | ~5k                |
| Kerr QNM (spin-dependent, Berti 2009)     | Physics   | HIGH     | ~200               |
| Spin-orbit/spin-spin GW phase coupling    | Physics   | MEDIUM   | ~100               |
| Async GRMHD tile streaming               | Perf      | HIGH     | ~800               |
| Analytic Kerr geodesic (elliptic fns)    | Perf      | HIGH     | ~800               |
| Kerr-Schild coords on GPU               | Perf      | HIGH     | ~200               |
| Compute/fragment FMA parity (Issue-008)  | Perf      | HIGH     | ~50                |
| 3+1 ADM / BSSN decomposition             | Math      | MEDIUM   | N/A (research)     |
| Hyperboloidal foliation / CCE            | Math      | MEDIUM   | N/A (research)     |
| Newman-Penrose / Teukolsky equation      | Math      | MEDIUM   | N/A (research)     |
| Dormand-Prince RK45 + event detection    | Perf      | MEDIUM   | ~200               |
| Symplectic integrator (Yoshida)          | Math+Perf | MEDIUM   | ~300               |
| AMR step refinement near boundaries      | Perf      | MEDIUM   | ~200               |
| GW precessing binary (SpinTaylorT4)      | Physics   | MEDIUM   | ~300               |
| Cauchy horizon dynamics / mass inflation  | Math      | LOW      | N/A (research)     |
| GW memory effect (Christodoulou)         | Physics   | LOW      | ~50                |
| Higher GW multipoles (l>2)               | Physics   | LOW      | ~200               |
| EOS / matter field coupling              | Physics   | LOW      | N/A (research)     |
| QED pair production / Schwinger limit    | Physics   | LOW      | N/A (research)     |

---

## 5. Conan / C++ Library Scope for Future Buildout

### 5.1 Already in conanfile.py (no new packages needed for core gaps)

| Package         | Version | Relevant Physics Use                                                    |
|-----------------|---------|-------------------------------------------------------------------------|
| `boost`         | 1.90.0  | Jacobi sn/cn/dn (analytic geodesic); Bessel K_{5/3} (synchrotron); elliptic K/E; Boost.Numeric.Odeint (RK45, symplectic steppers) |
| `eigen`         | 3.4.0   | Sparse matrix solver for Teukolsky ODE; batch geodesic linear algebra  |
| `hdf5`          | 1.14.6  | GRMHD HDF5 tile ingestion                                               |
| `highfive`      | 3.1.1   | C++11 HDF5 wrapper for GRMHD tile reader                               |
| `gmp`           | 6.3.0   | Arbitrary precision (available; unused in physics hotpath)              |
| `mpfr`          | 4.2.2   | Multi-precision float (useful near singularities for validation)        |
| `xsimd`         | 13.2.0  | SIMD in physics batch kernels (batch.h)                                |
| `highway`       | 1.2.0   | Portable SIMD dispatch (highway_eval.h)                                |
| `sleef`         | 3.9.0   | 1-ULP vectorized transcendentals (batch.h SLEEF path)                 |
| `taskflow`      | 3.10.0  | Async tile decompression; parallel LUT generation                       |
| `nlohmann_json` | latest  | GRMHD metadata JSON parsing (wired but incomplete)                     |

### 5.2 Missing from conanfile.py -- Candidates

| Package       | ConanCenter? | Use Case                                             | Priority |
|---------------|--------------|------------------------------------------------------|----------|
| `fftw/3.3.10` | NO           | Spectral synthesis for RTE; Compton kernel convolution | MEDIUM  |
| `pffft/0.0.3` | CHECK        | Single-precision FFT fallback                        | LOW      |
| `gsl/2.7`     | NO           | Modified Bessel K_{5/3}; cross-validation of Boost   | LOW      |

**FFTW / GSL workaround:** Both are absent from ConanCenter as of 2026.

- `fftw`: Vendor via `CMakeLists.txt` FetchContent or `pacman -S fftw`. Add a
  `find_package(FFTW3 QUIET)` guard so it is optional.
- `gsl`: Use `boost::math::cyl_bessel_k` and `boost::math::ellint_1` instead.
  Boost 1.90.0 covers the same Bessel/elliptic function domain. Use system GSL
  only if Boost accuracy proves insufficient for a specific case.

### 5.3 Library-to-Gap Mapping

| Physics Gap                               | Library                  | Action Required                                                    |
|-------------------------------------------|--------------------------|--------------------------------------------------------------------|
| Analytic Kerr geodesic (Jacobi sn/cn/dn)  | `boost` (Math)           | `boost::math::jacobi_sn/cn/dn`; Boost already linked              |
| Symplectic integrator                     | `boost` (Odeint)         | `boost::numeric::odeint::symplectic_rkn_sb3a_mclachlan` or ~100 LOC custom |
| Dormand-Prince RK45 + event detection     | `boost` (Odeint)         | `boost::numeric::odeint::runge_kutta_dopri5` with observer callbacks |
| Synchrotron Bessel K_{5/3} accuracy       | `boost` (Math)           | Replace polynomial fit (synchrotron.h:195-214) with `cyl_bessel_k` |
| Teukolsky sparse ODE system               | `eigen`                  | Enable `-DENABLE_EIGEN=ON`; `Eigen::SparseMatrix + SparseLU`       |
| Radiative transfer spectral convolution   | fftw (FetchContent)      | Optional; defer until Phase 6.3 RTE work begins                    |
| Async GRMHD tile streaming               | `highfive` + `taskflow` + PBO | No new packages; wire existing libraries                     |
| Multi-precision near-singularity validation | `mpfr`                 | Available; activate in test/validation builds                      |
| Kerr QNM (Berti 2009 tables)             | None (inline fit)        | Polynomial fits from Berti (2009) Table VIII; ~50 LOC              |
| GW spin-orbit/spin-spin phase            | None                     | Closed-form PN coefficients from Blanchet (2014); ~100 LOC         |

### 5.4 Build Impact Summary

- **0 new Conan packages required** for the HIGH-priority gaps (Kerr QNM, analytic
  geodesic, symplectic integrator, Dormand-Prince, Bessel accuracy, Eigen sparse).
  All rely on `boost/1.90.0` (already present) and `eigen/3.4.0` (already optional).
- **1 potential FetchContent addition** (`fftw`) for spectral radiative transfer;
  deferred until Phase 6.3 RTE work begins.
- **No Conan recipe changes** needed for the core buildout plan.

---

## References

- Blanchet, L. (2014). *Gravitational Radiation from Post-Newtonian Sources and
  Inspiralling Compact Binaries.* Living Reviews in Relativity, 17, 2.
- Berti, E., Cardoso, V., Starinets, A.O. (2009). *Quasinormal modes of black holes
  and black branes.* Class. Quant. Grav. 26, 163001.
- Broderick, A., Blandford, R. (2004). *Covariant magnetoionic theory I.* MNRAS 342.
- Dafermos, M., Luk, J. (2017). *The interior of dynamical vacuum black holes I.*
  arXiv:1710.01722.
- Fujita, R., Hikida, W. (2009). *Analytical solutions of bound timelike geodesic
  orbits in Kerr spacetime.* Class. Quant. Grav. 26, 135002.
- Gralla, S.E., Lupsasca, A. (2020). *Lensing by Kerr black holes.* Phys. Rev. D 101.
- Jimenez-Forteza, X. et al. (2017). *Hierarchical data-driven approach to fitting
  numerical relativity data.* Phys. Rev. D 95, 064024.
- Peters, P.C. (1964). *Gravitational Radiation and the Motion of Two Point Masses.*
  Phys. Rev. 136, B1224.
- Poisson, E., Israel, W. (1990). *Internal structure of black holes.* Phys. Rev. D 41.
- Teukolsky, S.A. (1972). *Rotating black holes: separable wave equations.*
  Phys. Rev. Lett. 29, 1114.
- Yoshida, H. (1990). *Construction of higher order symplectic integrators.*
  Phys. Lett. A 150, 262.
