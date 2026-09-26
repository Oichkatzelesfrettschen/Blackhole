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
6. [Research Frontiers 2024-2026](#6-research-frontiers-2024-2026)

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

along each geodesic ray, in affine parameter with Kirchhoff-consistent j_nu and
alpha_nu and the invariant I_nu / nu^3. The default path uses LUT-backed emissivity
and redshift. The GPU volumetric path (GLSL D2/D3, CUDA `d_trace_geodesic_rte()`)
marches an opacity field as a shading model: its path length is the Mino-time
increment and its absorption is `alpha = k * j`. The CPU `rte_integrator.h` step is
the exact flat-slab formal solution, tested against analytic slabs.

**Mathematical gaps:**

- **Optical depth integration:** `tau_nu = integral(alpha_nu ds)` along the geodesic.
  Without this, all emitting regions are treated as optically thin.

- **Frequency redistribution (Comptonization):** Photon frequencies shift when
  scattering off hot electrons in the corona. The Klein-Nishina cross section is
  present in scattering_models.h but is NOT called during ray marching.

- **Polarized radiative transfer:** The Stokes vector `(I, Q, U, V)` transport
  requires a 4x4 Mueller matrix propagated along each geodesic with the polarization
  frame parallel-transported (Broderick & Blandford 2004). The GPU "Stokes IQUV" path
  (GLSL D4, CUDA `d_trace_geodesic_stokes()`) is a shading model: it uses the Mino-time
  increment as path length, sets `alpha = k * j`, applies one global sky-plane EVPA,
  and transports no polarization frame (no Walker-Penrose constant, no emitter
  tetrad). The CPU `stokes_transport.h` step is a flat-slab solver. Covariant
  polarized transport is absent; it matters for EHT polarimetry and spin
  measurements via linear polarization.

- **Fe K-alpha line at 6.4 keV:** The relativistically broadened iron emission line
  from the disk corona is a primary spin measurement observable. Listed as a Phase 6.3
  future task; not yet started.

> **[2024 UPDATE -- EHT Sgr A* Paper VIII, DOI:10.3847/2041-8213/ad2df1]**
> EHT Collaboration, "First Sagittarius A* Event Horizon Telescope Results. VIII.
> Physical Interpretation of the Polarized Ring", ApJL 964, L26 (2024), interprets the
> Sgr A* polarized ring. Only the paper's metadata was checked, so no polarization
> fraction or field topology is quoted here. The paper sets an observational target for polarized radiative
> transfer: Stokes I, Q, U, V transported covariantly along geodesics (4x4 Mueller
> propagator, Broderick-Blandford 2004). The GPU Stokes path is a shading model, so
> the renderer cannot yet produce synthetic polarimetric maps for that comparison.

> **[2024 UPDATE -- IPOLE/PATOKA two-temperature synchrotron (AFD Illinois)]**
> The IPOLE polarized GRRT code (Illinois group, 2024) uses MAD GRMHD simulations with
> two-temperature (2T) electron thermodynamics, where T_e != T_i in the disk. Single-
> temperature models overestimate T_e in the disk midplane and give ~30% excess 230 GHz
> flux relative to EHT observations. The 2T approach uses a heat ratio prescription
> R = Q_i/Q_e that varies with plasma beta.
>
> The IPOLE synchrotron function G(x) = x * K_{2/3}(x) uses a numerically stable
> approximation that avoids the instability in the polynomial fit currently in
> synchrotron.h. Our test failures (tests 3 and 8: G(x)/F(x) > 1 for x in [1,10],
> which is physically impossible since G(x) <= F(x) everywhere) arise from polynomial
> coefficient error in this regime. The IPOLE code at github.com/AFD-Illinois/ipole
> is the reference implementation for the fix (~30 LOC, replacing the polynomial).
> See also: synchrotron.h G(x) gap in the Section 4 summary table.

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

#### a) Spin-orbit and spin-spin coupling in PN phase -- IMPLEMENTED (Phase 6, 2026-02-27)

`gw_phase_3p5pn` (gravitational_waves.h) now includes:
- 1.5PN tail: `-16*pi*v^3`
- 1.5PN spin-orbit (Kidder 1995): `(113/12 + 25*eta/4) * chi_eff * v^3 / 12`
- 2PN spin-spin (Cutler-Flanagan 1994): `-50*eta*chi1*chi2*v^4`
- Parameters `chi_eff`, `chi1`, `chi2` added with defaults 0 (backward-compatible).
- Corrections are O(10%) for dimensionless spins `a* > 0.3`; now accounted for.

#### b) Precessing binaries (generic spins)

The current model assumes aligned spins (no orbital precession). For generic spin
orientations, the orbital plane precesses and produces characteristic amplitude and
phase modulation (the "windmill" waveform). This requires the SpinTaylorT4
approximant (Buonanno-Chen-Vallisneri 2003). Absent.

#### c) Kerr QNM ringdown -- IMPLEMENTED (Phase 6, 2026-02-27)

`qnm_frequency_kerr` and `qnm_damping_time_kerr` in gravitational_waves.h now
implement the Berti-Cardoso-Starinets (2009) Table VIII polynomial fits:

```
omega_22(a*) = f1 + f2*(1-a*)^f3     [real part]
tau_22(a*) = q1 + q2*(1-a*)^q3       [damping time]
```

6/6 unit tests pass in kerr_qnm_spin_validation. The pre-existing scalar-only
path `qnm_frequency_schwarzschild` is retained for backward compatibility.

#### d) Higher-order PN phase and spin corrections

The current `gw_phase_3p5pn` (gravitational_waves.h) includes:
- 1.5PN tail: `-16*pi*v^3`
- 1.5PN spin-orbit (Kidder 1995): `(113/12 + 25*eta/4) * chi_eff * v^3 / 12` (IMPLEMENTED Phase 6)
- 2PN spin-spin (Cutler-Flanagan 1994): `-50*eta*chi1*chi2*v^4` (IMPLEMENTED Phase 6)

Missing (future work):

> **[2024 UPDATE -- Blanchet Living Review 2024 + arXiv:2304.11185]**
> Blanchet et al. (Living Reviews in Relativity, July 2024) complete the 4PN equations
> of motion and derive the 4.5PN GW phase for quasi-circular spinless orbits in the
> MPM-PN formalism. arXiv:2304.11185 (Blanchet, Faye, Henry, Larrouturou, Trestini,
> "Gravitational-Wave Phasing of Quasi-Circular Compact Binary Systems to the
> Fourth-and-a-Half post-Newtonian Order", PRL 131, 121402, 2023) gives that phasing.
>
> Beyond 3.5PN, the next gaps in our implementation are:
> - NNLO spin-orbit at 3.5PN: ~8 additional PN coefficient terms (Blanchet 2011,
>   arXiv:1104.5659); estimated ~150 LOC in gw_phase_3p5pn extension.
>   This is a concrete near-term item because it corrects O(10%) errors for a* > 0.5.
> - 4PN spin-orbit (Marsat 2015, arXiv:1411.4118): the next-to-NNLO level.
> - 4.5PN phase for spinless case: closed-form coefficients now available.
> These corrections matter for LISA parameter estimation of high-spin MBH mergers.

#### e) Gravitational wave memory effect

After the GW passes, the metric permanently shifts by a nonzero amount:

```
delta h_ij = (4G/c^4 r) * integral_{-inf}^{+inf} (dE_GW/d Omega) n_i n_j d Omega dt
```

This Christodoulou (1991) memory is not computed. It is a DC shift observable by
LISA for massive binaries and by pulsar timing arrays (PTAs) for SMBH mergers.

#### f) Higher multipoles (l > 2)

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

> **[2023 UPDATE -- Dyson and van de Meent, arXiv:2302.03704]**
> Dyson and van de Meent, "Kerr-fully Diving into the Abyss: Analytic Solutions to
> Plunging Geodesics in Kerr" (2023), give closed-form solutions for TIMELIKE plunging
> geodesics. They cover infalling matter, not photons, so they do not change the
> effort estimate for analytic photon ray tracing. Reference implementation:
> KerrGeodesics package in the Black Hole Perturbation Toolkit (BHPT),
> https://bhptoolkit.org/KerrGeodesics.

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

**Fix (PARTIAL -- 2026-03-21):** The dphi and dt equations in `shader/include/kerr.glsl`
`kerrStep()` have been upgraded from the pure Boyer-Lindquist form (which accumulated large
errors near the horizon via `deltaSafe = max(Delta, 1e-6)`) to outgoing Kerr-Schild
equivalents that cancel the Delta pole for ingoing photons at r_+:

```
dphi_KS = Lz/sin^2 - aE + a*(A + dr_dlam) / Delta   [numerator -> 0 at r_+]
dt_KS   = [(r^2+a^2)*A + rs*r*dr_dlam] / Delta + ...
```

The (r, theta) equations are identical in BL and KS and were already regular.
The `deltaSafe` clamp is still present as a float32 guard; the residual error is
O(deltaSafe/A) per step, negligible for the integration step sizes used.
The CUDA path (`d_kerr_step()` in `src/cuda/device_physics.cuh`) uses the same
KS formulas and was the parity target for this fix.

**Fully resolved (2026-03-21):** The rationalized form `a*Q_eff/(A+sqrtR)` is
now implemented for the ingoing branch (sign_r < 0) in both `kerr.glsl`
`kerrStep()` and `device_physics.cuh` `d_kerr_step()`.  No Delta in the
denominator for ingoing rays -- exact float32 regularity at the horizon.
Outgoing rays (post-turning-point) use the standard KS form with guarded
inv_delta, which is numerically safe since Delta is bounded away from 0
for outgoing rays.  Both branches agree at turning points (sqrtR = 0).

> **[2023 UPDATE -- arXiv:2310.02321]**
> Bozzola, Chan, and Paschalidis, "Not All Spacetime Coordinates for
> General-Relativistic Ray Tracing Are Created Equal", PRD 108, 084004 (2023), report
> that rays whose momentum points toward or away from the horizon lead to different
> solutions near it, and that different coordinate systems give the same images up to
> numerical errors. The paper sets no coordinate requirement for backward ray
> tracing.

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
`jacobi_cn`, `jacobi_dn`. Estimated effort: ~500 LOC in CPU path.

### 3.3 Compute Raytracer Parity (Issue-008, ACTIVE)

The compute path has FP arithmetic differences from the fragment path due to
FMA (fused multiply-add) contraction ordering. One preset (preset 0,
horizon-grazing rays) fails the default tolerance with 2-4 outlier pixels of
2M; the strict sweep (1000 steps, 0.02) passes 12/12 -- `backlog.md`
ISSUE-009 owns the residual figure. Root cause is documented but not
eliminated. The fix requires either
disabling FMA contraction (`-ffp-contract=off` or `precise` GLSL pragma) uniformly,
or tightening the tolerance accounting for FMA-induced divergence.

### 3.4 Async GRMHD Tile Streaming -- CPU PATH COMPLETE (Phase 6, 2026-02-27)

`grmhd_streaming.cpp` had 9 TODO items; all are now filled (Phase 6B). The CPU
streaming path is implemented: nlohmann_json metadata parsing, seekg binary frame
reads, LRU cache eviction, condition_variable background thread, and prefetch logic.

Remaining gap: OpenGL PBO double-buffering for async GPU upload (~200 LOC).
Without PBO, each tile is copied synchronously on the render thread when first
accessed. The cache hit path is already zero-copy.

> **[2025 UPDATE -- AsterX GPU-GRMHD, APS Global Physics Summit 2025]**
> AsterX (2025) establishes AMReX block-structured AMR brick caching as the emerging
> standard for exascale GPU GRMHD rendering. AsterX uses multi-resolution LOD bricks
> (level-of-detail) to serve the GPU at different resolutions depending on camera
> distance, reducing GPU memory pressure by ~4x for 50GB+ datasets.
> Our current grmhd_streaming.cpp uses flat RGBA32F + single-LOD LRU cache.
> AMReX-style multi-resolution LOD is a future upgrade once the PBO path is validated.
> Flag as Phase 7+ work; do not preemptively complicate the single-LOD design.

### 3.5 No AMR Sampling Along Geodesic

The RK4 adaptive step size reacts to local integration error but does NOT refine
near physics boundaries (photon sphere, horizon, disk midplane). An
AMR-style refinement triggered by curvature invariants (Kretschmer scalar
`K = R_abcd R^abcd`, which diverges toward the singularity) would give better
accuracy where it matters with fewer steps elsewhere.

---

## 4. Summary Table by Priority

| Gap                                       | Type      | Priority | Effort (LOC est.) | Status |
|-------------------------------------------|-----------|----------|--------------------|--------|
| GRMHD solver (native)                     | Physics   | CRITICAL | 50k+ (out of scope)| Out of scope |
| Radiative transfer (volumetric RTE)       | Physics   | HIGH     | ~10k               | **SHADING MODEL** -- GLSL D2/D3 + CUDA d_trace_geodesic_rte() march Mino time with alpha = k*j; covariant transport (affine path, Kirchhoff j/alpha) absent; CPU rte_integrator.h slab step tested |
| Polarized radiative transfer (Stokes)     | Physics   | HIGH     | ~5k                | **SHADING MODEL** -- GLSL D4 + CUDA d_trace_geodesic_stokes() use a global EVPA and no frame transport; covariant polarized transport absent |
| synchrotron G(x) fix (x~1-10 regime)     | Physics   | HIGH     | ~30                | **COMPLETE** -- CPU K_{2/3} Bessel + GPU 256-entry LUT (commits 0c17b69/a5ba31f) |
| NNLO spin-orbit PN phase (3.5PN)         | Physics   | HIGH     | ~150               | **COMPLETE** -- Blanchet 2011 TaylorF2; 3PN+3.5PN (commit fb532d5) |
| OpenGL PBO GPU upload for GRMHD           | Perf      | HIGH     | ~200               | **COMPLETE** -- GrmhdPBOUploader + GRMHDGpuUploader; 6.2.4 |
| Analytic Kerr geodesic (elliptic fns)    | Perf      | HIGH     | ~500               | **COMPLETE** -- analytic_kerr_geodesic.h 460 LOC; 15/15 C++ + 6/6 CUDA tests |
| Outgoing Kerr-Schild coords on GPU       | Perf      | HIGH     | ~200               | **COMPLETE** -- kerr_schild.glsl + rationalized kerrStep/d_kerr_step; 8/8 tests |
| Exact Kerr Carter constants init         | Perf+Phys | HIGH     | ~80                | **COMPLETE (corrected)** -- kerrInitGeodesic/d_kerr_init_geodesic solve the null condition for k^t and read E/Lz from the metric; Q=ptheta^2-a^2*cos^2+Lz^2*cot^2 (Carter). The earlier Lz^2/sin^2 form shortened R by Delta*Lz^2; gated by kerr_null_geodesic_validation and kerr_shader_capture |
| Compute/fragment FMA parity (Issue-009)  | Perf      | HIGH     | ~50                | Root-caused; 0.0002% residual at horizon-grazing rays; strict sweep passes 12/12 |
| Kerr QNM (spin-dependent, Berti 2009)    | Physics   | DONE     | ~200               | COMPLETE Phase 6 |
| Spin-orbit/spin-spin GW phase coupling   | Physics   | DONE     | ~100               | COMPLETE Phase 6 |
| GRMHD CPU async tile streaming           | Perf      | DONE     | ~800               | COMPLETE Phase 6 |
| Dormand-Prince RK45 step control         | Perf      | DONE     | ~200               | COMPLETE Phase 6 |
| Newman-Penrose null tetrad (Weyl Psi_2)  | Math      | DONE     | ~200               | COMPLETE -- newman_penrose.h; 12/12 tests |
| Yoshida 4th-order symplectic integrator  | Math+Perf | DONE     | ~334               | COMPLETE -- symplectic_integrator.h; Yoshida 1990; tests pass |
| GW memory effect (Christodoulou 1991)    | Physics   | DONE     | ~50                | COMPLETE -- gwMemoryStrain/gwMemoryDelta; 8/17 tests (D7) |
| GW precessing binary (chi_p, D8)         | Physics   | DONE     | ~200               | COMPLETE -- chiP/precessingOpeningAngle/simplePrecessionPhase; 9/17 tests (D8) |
| Higher GW multipoles h_lm (l=2,3,4)     | Physics   | DONE     | ~200               | COMPLETE -- gwInspiralStrainMultimode; 13/13 tests (gw_multipole) |
| Fe K-alpha relativistic line (Laor 1991) | Physics   | DONE     | ~300               | COMPLETE -- ironKLineProfile; 10/10 tests |
| 3+1 ADM / BSSN decomposition             | Math      | MEDIUM   | N/A (research)     | Not started -- research-only |
| Hyperboloidal foliation / CCE            | Math      | MEDIUM   | N/A (research)     | Not started -- research-only |
| Teukolsky equation (QNM Psi_4)          | Math      | MEDIUM   | N/A (research)     | Not started -- research-only |
| AMR step refinement near boundaries      | Perf      | MEDIUM   | ~200               | Partial -- bhAdaptiveStep halves step near horizon; full curvature-based AMR pending |
| SpinTaylorT4 time-domain waveform        | Physics   | MEDIUM   | ~300               | Partial -- simple precession (Apostolatos 1994) done; full coupled ODE not integrated |
| AMReX-style LOD GRMHD streaming         | Perf      | LOW      | ~1k                | Future (AsterX 2025) |
| Cauchy horizon dynamics / mass inflation  | Math      | LOW      | N/A (research)     | Not started -- research-only |
| EOS / matter field coupling              | Physics   | LOW      | N/A (research)     | Not started -- research-only |
| QED pair production / Schwinger limit    | Physics   | LOW      | N/A (research)     | Not started -- research-only |

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

---

## 6. Research Frontiers 2024-2026

This section consolidates the six actionable research findings incorporated into this
document on 2026-02-27. Each item updates an earlier gap analysis with current
literature and affects implementation estimates or coordinate choices.

### 6.1 Dyson and van de Meent 2023 -- Plunging Kerr Geodesics (arXiv:2302.03704)

**Relevance:** Section 2.6d, Section 3.2.

Dyson and van de Meent, "Kerr-fully Diving into the Abyss: Analytic Solutions to
Plunging Geodesics in Kerr" (2023), solve TIMELIKE plunging geodesics in closed form.
The Black Hole Perturbation Toolkit (BHPT) hosts a reference implementation in
KerrGeodesics: https://bhptoolkit.org/KerrGeodesics.

Impact on LACUNAE estimate: none for the photon ray tracer. The paper treats massive
particles, so it does not bear on the analytic photon-geodesic effort in Section 3.2.

### 6.2 Ray-Tracing Coordinates 2023 (arXiv:2310.02321)

**Relevance:** Section 2.7, Item F in the roadmap (`../developer-guide/roadmap.md`).

Bozzola, Chan, and Paschalidis, "Not All Spacetime Coordinates for
General-Relativistic Ray Tracing Are Created Equal", PRD 108, 084004 (2023), report
that rays whose momentum points toward or away from the horizon lead to different
solutions, and that different coordinates give the same images up to numerical
errors. The coordinate choice for Item F is therefore a numerical-accuracy decision
to be measured, not a correctness constraint set by this paper.

### 6.3 EHT Sgr A* Paper VIII 2024 (DOI:10.3847/2041-8213/ad2df1)

**Relevance:** Section 2.2.

EHT Collaboration, "First Sagittarius A* Event Horizon Telescope Results. VIII.
Physical Interpretation of the Polarized Ring", ApJL 964, L26 (2024). Only the
paper's metadata was checked; no polarization fraction is quoted.

The paper sets an observational validation target: polarized radiative transfer
(Stokes I, Q, U, V transport via 4x4 Mueller matrix along geodesics). Without
covariant transport the renderer cannot produce synthetic polarimetric maps for
direct comparison to EHT data.

Current status: the GPU Stokes path is a shading model (Section 2.2); covariant
polarized transport is absent. The Broderick-Blandford (2004) formalism, or a
Walker-Penrose/tetrad transport as in ipole, is the starting point.

### 6.4 IPOLE/PATOKA Two-Temperature Synchrotron (AFD Illinois, 2024)

**Relevance:** Section 2.2, synchrotron.h.

The IPOLE (Illinois Polarized One-zone Line Emission) GRRT code uses MAD GRMHD
simulations with two-temperature electron thermodynamics. Key findings:

- Single-temperature models overestimate disk T_e and give ~30% excess 230 GHz flux.
- G(x) = x * K_{2/3}(x) is computed in IPOLE using a numerically stable piecewise
  approximation that avoids polynomial coefficient sensitivity in the x~1-10 regime.
- Our synchrotron.h tests 3 and 8 fail because our G(x) polynomial gives G(x) > F(x)
  for x in [1, 10], which is physically impossible (G(x) <= F(x) for all x > 0).

Near-term action: replace the G(x) polynomial in synchrotron.h with either the
IPOLE piecewise approach or `boost::math::cyl_bessel_k(2.0/3.0, x) * x`. Estimated
effort: ~30 LOC. This will fix the 2 pre-existing test failures.

Reference: https://github.com/AFD-Illinois/ipole

### 6.5 Blanchet Living Review 2024 and arXiv:2304.11185

**Relevance:** Section 2.4d.

Blanchet et al. (Living Reviews in Relativity, July 2024) completes the 4PN equations
of motion for two-body compact binaries in the Multipolar Post-Minkowskian (MPM-PN)
formalism. arXiv:2304.11185 (Blanchet, Faye, Henry, Larrouturou, Trestini, PRL 131,
121402, 2023) gives the 4.5PN gravitational wave phasing for quasi-circular orbits.

Near-term actionable item: NNLO spin-orbit correction at 3.5PN (Blanchet et al. 2011,
arXiv:1104.5659). This adds ~8 additional PN coefficient terms to gw_phase_3p5pn
and corrects O(10%) phase errors for a* > 0.5. Estimated effort: ~150 LOC.

Longer-term: 4PN spin-orbit (Marsat 2015, arXiv:1411.4118) and the 4.5PN spinless
phase. These are primarily relevant for LISA science with massive black hole binaries.

### 6.6 AsterX GPU-GRMHD 2025 (APS Global Physics Summit)

**Relevance:** Section 3.4.

AsterX (2025) is a GPU-accelerated GRMHD code using AMReX block-structured AMR.
The AMReX LOD (level-of-detail) brick caching system serves the GPU at variable
resolution based on camera distance and local curvature, reducing GPU memory pressure
by ~4x for 50GB+ datasets relative to flat-LOD approaches.

Our grmhd_streaming.cpp uses flat RGBA32F + single-LOD LRU cache. The AsterX
approach is the emerging best practice for exascale GRMHD visualization.
This is flagged as a Phase 7+ upgrade after the PBO GPU upload path is validated.
Do not preemptively add LOD complexity to the single-resolution implementation.

---

## References

- Berti, E., Cardoso, V., Starinets, A.O. (2009). *Quasinormal modes of black holes
  and black branes.* Class. Quant. Grav. 26, 163001.
- Blanchet, L. (2014). *Gravitational Radiation from Post-Newtonian Sources and
  Inspiralling Compact Binaries.* Living Reviews in Relativity, 17, 2.
- Blanchet, L. (2024). *Gravitational Radiation from Post-Newtonian Sources and
  Inspiralling Compact Binaries.* Living Reviews in Relativity, updated July 2024.
- Blanchet, L., Faye, G., Henry, Q., Larrouturou, F., Trestini, D. (2023).
  *Gravitational-Wave Phasing of Quasi-Circular Compact Binary Systems to the
  Fourth-and-a-Half post-Newtonian Order.* Phys. Rev. Lett. 131, 121402.
  arXiv:2304.11185.
- Blanchet, L. et al. (2011). *Gravitational-wave phasing of spinning compact
  binaries at 3.5 post-Newtonian order.* arXiv:1104.5659.
- Bozzola, G., Chan, C.-K., Paschalidis, V. (2023). *Not All Spacetime Coordinates for
  General-Relativistic Ray Tracing Are Created Equal.* Phys. Rev. D 108, 084004.
  arXiv:2310.02321.
- Broderick, A., Blandford, R. (2004). *Covariant magnetoionic theory I.* MNRAS 342.
- Cutler, C., Flanagan, E. (1994). *Gravitational waves from merging compact
  binaries: How accurately can one extract the binary's parameters.* Phys. Rev. D 49.
- Dafermos, M., Luk, J. (2017). *The interior of dynamical vacuum black holes I.*
  arXiv:1710.01722.
- Dyson, C., van de Meent, M. (2023). *Kerr-fully Diving into the Abyss: Analytic
  Solutions to Plunging Geodesics in Kerr.* arXiv:2302.03704.
- EHT Collaboration (2024). *First Sagittarius A* Event Horizon Telescope Results.
  VIII. Physical Interpretation of the Polarized Ring.* ApJL 964, L26.
  DOI:10.3847/2041-8213/ad2df1.
- Fujita, R., Hikida, W. (2009). *Analytical solutions of bound timelike geodesic
  orbits in Kerr spacetime.* Class. Quant. Grav. 26, 135002.
- Gralla, S.E., Lupsasca, A. (2020). *Lensing by Kerr black holes.* Phys. Rev. D 101.
- Jimenez-Forteza, X. et al. (2017). *Hierarchical data-driven approach to fitting
  numerical relativity data.* Phys. Rev. D 95, 064024.
- Kidder, L.E. (1995). *Coalescing binary systems of compact objects to (post)^5/2-
  Newtonian order.* Phys. Rev. D 52.
- Marsat, S. (2015). *Cubic-order spin-orbit effects in the dynamics and gravitational
  wave energy flux of compact binaries.* arXiv:1411.4118.
- Moscibrodzka, M. et al. (2017). *IPOLE -- semi-analytic scheme for relativistic
  polarized radiative transport.* MNRAS 468. github.com/AFD-Illinois/ipole.
- Peters, P.C. (1964). *Gravitational Radiation and the Motion of Two Point Masses.*
  Phys. Rev. 136, B1224.
- Poisson, E., Israel, W. (1990). *Internal structure of black holes.* Phys. Rev. D 41.
- Teukolsky, S.A. (1972). *Rotating black holes: separable wave equations.*
  Phys. Rev. Lett. 29, 1114.
- Yoshida, H. (1990). *Construction of higher order symplectic integrators.*
  Phys. Lett. A 150, 262.
