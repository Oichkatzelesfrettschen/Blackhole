# open_gororoba physics and rendering crates: granular port inventory

Pinned baselines: open_gororoba `2b90fe66` (2026-09-27, working tree adds only
`.gitignore` and `.ignore`); Blackhole `29fe8ec` (main). Every open_gororoba
statement is a source reading; no cargo build or test ran (`not run`, read-only
task). Blackhole statements come from greps of the pinned checkout. Sibling
reports: [01-rocq-proofs.md](01-rocq-proofs.md). Earlier work this report
extends and does not repeat:
[audit 02 crate triage](../physics-and-game-engine/02-open-gororoba-crossref.md),
[audit 05 numerics](../physics-and-game-engine/05-open-gororoba-novel-numerics.md),
[decomposition](../../physics/open-gororoba-decomposition.md), and the
[adaptation survey](../../plans/open-gororoba-adaptation-survey.md) (items A1-A6,
B1-B7, D1-D8). The audit implementation plan is cited by tranche name only.

Classification tags: ALREADY-IN-BLACKHOLE (file cited), IN-PLAN (audit plan
tranche, still missing at the pin), NEW-PORT (absent from both), SKIP (reason).

## 1. Summary: top NEW-PORT items by visible payoff

Top NEW-PORT items (classes NEW-PORT unless stated), by visible payoff:

1. NP-1 Kerr constant-l torus generator (`src/physics/fm_torus.h` plus a snapshot
   tool): Blackhole has no torus and no synthetic GRMHD volume; accretion-flow R2
   (thick RIAF torus) stays open. gr_core labels its constant `-u_phi/u_t` torus
   "Fishbone-Moncrief" and uses a Schwarzschild `l`; port with the Kerr `l`.
2. NP-2 MKS/KS-to-BL resampler with the closed-form azimuth term in
   `src/physics/coordinates.h`: `blCoord` returns `bl.phi = x3`; the true offset is
   26 degrees at r = 3, a = 0.9. The packed loader reads `r_min`/`r_max` in BL
   units, so its axis mapping (untraced) decides how much of an imported snapshot is wrong.
3. NP-4 brick-occupancy max-mip pyramid for GRMHD empty-space skipping (GL and
   CUDA, no RT cores), with the D7 ceil fix; oracle: pixel-identical to the full march.
4. NP-5 OptiX brick-AABB BVH accelerator with refit cadence and RT/SM stream
   concurrency; gated on the 20 percent intersection-share falsifier.
5. NP-6 Lomb-Scargle + Baluev false-alarm and Welch PSD tool for light-curve QPO
   validation (serves G5).
6. NP-7 Sersic profile and Abel deprojection sprite; NFW/DC14 overlay (low payoff).
7. NP-8 per-kernel FMA control in CUDA parity builds (no pixels).
8. Precondition, no open_gororoba source: NP-3 wires the GRMHD volume into the
   default Kerr interop path (`grmhdTexture` is read only in `blackhole_main.frag`).
9. Remaining IN-PLAN: exact-Stokes GLSL/CUDA twins and the emission-factor series
   (audit plan T5, items 1 and 2).
10. Absent in open_gororoba, nothing to port: jets (BZ power only), tone mapping,
    color and spectral rendering, polarization visuals, photon rings, lensing.

Headline finding: open_gororoba is thin on rendering. Its value to Blackhole is
one torus generator, one coordinate identity, one OptiX pattern, and defect
reports that keep Blackhole from copying errors.

## 2. What changed since the earlier reports

open_gororoba fixed on 2026-09-27 (commit, observed in source):

| Earlier verdict | Now | Commit |
|---|---|---|
| `sqrt_neg_g` volume form wrong (decomposition) | `metric.rs` returns Sigma abs(sin theta) | b4cab7e3 |
| HLL bounds ignored B (`va^2 = 0`) | `flux.rs` `wave_speeds_from_prims` builds `va^2 = b^2/(rho h + b^2)`; test `test_magnetic_field_widens_bounded_wave_speeds` | ddac2319 |
| CUDA inverse-metric sign, module compile | kernel keeps the determinant sign (`kernels_grmhd.cu` 78-80) | 785f4970 |
| Magnetic stress dropped from momentum | full b^2 contraction on every backend | 5b7f3e1f |
| Log-radius flux and source Jacobian | `inverse_coordinate_jacobian_at_face`; CUDA `sqrt_g = Sigma abs(sin) r` matches the CPU face factor | 05e826c3 |
| Torus identities | constant-l and polytropic-enthalpy identities restored | 05e826c3 |
| Adaptive integrator was RK4 + RK2 estimate | `DormandPrinceRK45` runs the 5(4) tableau | 5a8d6abc |
| `cr_transport` diffused along x only | y and z tensor diagonals, shared face diffusivities, mass conservation | f9ebbbc6, 4942ae79, cb538e2f |

The decomposition's GRMHD table describes the pre-fix tree; its verdict column
is stale for the first five rows. The CUDA-vs-CPU `r` factor question closes:
the CPU applies the `r` Jacobian at faces, the CUDA cache carries it in `sqrt_g`.
Commit 05e826c3 records a stationary-torus radial residual of 9.22, 5.03, 2.31 on
24, 48, 96 radial cells (about first order; taken from the message, not re-run).

Still defective at this pin (spot-checked in source): gr_core KN ISCO adds
`q^2/(2 m^2)` (`kerr_newman.rs:167`); KdS `delta` is quadratic
(`kerr_de_sitter.rs:41`); Fouka-Ouichaoui F intermediate branch
(`synchrotron.rs:135`); free-free `k_ff = 3.68e8` with `T^-3/2 nu^-2`
(`absorption.rs:64-73`, D3); the torus `l` is Schwarzschild-only
(`grmhd_core/src/torus.rs:38`). Unchanged since 2026-06-10: `absorption.rs`,
`doppler.rs`, `novikov_thorne.rs`. Landed in Blackhole since the audit: #27 Kerr
Carter/Mino, #29 KN/KdS/null-norm/lapse, #30 Page-Thorne + g-factor + toggle, #31
clocks, #32 exact Stokes + Carlson + Lyapunov, #38 observer sky, #28 tesseract,
#67 Boost-free special functions, #70 Doppler convention and Rayleigh-Jeans, #74
elliptic complement and GLSL F/G tables, #83 `RayTerminal`, #102 turbulent disk emissivity, #103 volumetric disk, #108 sharp volumetric default.

## 3. Per-crate decomposition

### 3.1 gr_core (34.3k lines, MIT declared)

Modules by cluster, what each computes, oracle, method, classification.

| Module | Physics and method | Reference values in tests | Class |
|---|---|---|---|
| `kerr.rs` (1850) | Kerr metric, exact Christoffels, Carter-separated null geodesics in Mino time with `u = 1/r`, DOPRI5; `shadow_boundary` (Bardeen), `shadow_ray_traced`; `Kerr` struct (horizons, ISCO, photon orbit, surface gravity) | photon sphere 3 (1e-6); shadow radius sqrt(27) on 100 points (1e-6); vacuum Einstein and Kretschmann checks; polar test tautological | ALREADY-IN-BLACKHOLE: `kerr.cpp`, `kerr_observer.h`, `analytic_kerr_geodesic.h`, `observer_sky_map.h`; second-order Mino landed #27 |
| `schwarzschild.rs` (762) | closed-form Christoffels, potentials, weak-field deflection, Shapiro delay, turning point | photon sphere, ISCO 6, b_c = sqrt(27) | ALREADY-IN-BLACKHOLE: `schwarzschild.h`; game delay uses the exact radial integral, not `shapiro_delay` |
| `metric.rs` (507) | generic `SpacetimeMetric` trait; finite-difference Christoffel, Riemann, Ricci, Kretschmann | Ricci = 0 to tolerance for Kerr | ALREADY-IN-BLACKHOLE as an idea: `tests/support/ricci_oracle.h` (used by KN/KdS tests) |
| `coordinates.rs` (364) | MKS `r = exp(x1)`, `th = pi x2 + (1-h)/2 sin(2 pi x2)`, KS<->BL radius; `ks_phi_correction` is a stub returning 0 (D6) | round trips, Jacobians | ALREADY-IN-BLACKHOLE (`coordinates.h`, same D6 defect): see NEW-PORT 2 |
| `kerr_newman.rs`, `kerr_de_sitter.rs` | wrong ISCO, `g_tphi`, KdS Delta | pins the bugs | SKIP (Blackhole fixed in #29; open_gororoba unchanged) |
| `novikov_thorne.rs` (770) | Newtonian zero-torque flux with peak fixed at 1.5 r_isco; `disk_redshift_factor = sqrt(1 - 3/r)` (correct face-on, a = 0 only); efficiency `1 - sqrt(1 - 2/(3 r_isco))` | eta(0) = 0.05719; ISCO g = 0.7071 | ALREADY-IN-BLACKHOLE, superseded: `page_thorne.h`, `disk_transfer.h`, `disk_transfer.glsl` (#30) |
| `doppler.rs` (586) | Doppler, beaming, aberration, k-correction, superluminal motion, `disk_doppler_boost` | approach/recede factors, `gamma beta` superluminal maximum | ALREADY-IN-BLACKHOLE: `doppler.h`; sign convention fixed in #70, gr_core still on the old one |
| `absorption.rs` (495) | SSA, free-free, Compton absorption, Planck function, plasma frequency, transfer step | scaling checks only | SKIP: D3, D4, D5 (Kirchhoff j/B_nu is the authority; `absorption_models.h`, `rte_integrator.h`) |
| `scattering.rs` (590) | Thomson (KN, hot plasma), Rayleigh, Mie efficiency, albedo, asymmetry | Rayleigh nu^4, Mie geometric limit | ALREADY-IN-BLACKHOLE: `scattering_models.h` |
| `synchrotron.rs` (384) | gyro quantities, F(x), G(x) via asymptotes and a "fit" | x = 1 wrong (audit F10) | ALREADY-IN-BLACKHOLE, correct there: #67 Bessel K kernel, #74 CPU tables in GLSL |
| `spectral_bands.rs` (398) | EHT 230 GHz, ALMA 100 GHz, Johnson V, Chandra 0.5-10 keV bands, Gaussian/rect filters, magnitudes, band integration | 5 mag = 100x; V zero point 3.64e-20 cgs | ALREADY-IN-BLACKHOLE: `spectral_channels.h` (same bands; lineage) |
| `hawking.rs`, `penrose.rs` | T_H, evaporation, Page time; Penrose efficiency, BZ power, superradiance | T_H(1 Msun) = 6.2e-8 K | ALREADY-IN-BLACKHOLE: `hawking.h`, `penrose.h`, `jet_physics.h` |
| `gravitational_waves.rs` | strain, chirp mass, TaylorF2 (missing 1/eta, audit F9) | monotonicity | SKIP: Blackhole 4.5PN `gravitational_waves.h` |
| `null_constraint.rs`, `energy_conserving.rs` | null renormalization; RK4 + additive norm projection | norm 3.6e-15 (audit 02) | ALREADY-IN-BLACKHOLE: additive projection in `verified/energy_conserving_geodesic.hpp` (#29) |
| `lyapunov.rs` | generic Benettin accumulator | 3 tests | ALREADY-IN-BLACKHOLE, better: `photon_ring.h` closed form (#32) |
| `forces/abm8_integrator.rs`, `adaptive_integrator.rs` | ABM8 multistep; DOPRI45 (fixed 2026-09-27) | ABM8 exact through degree 7 | SKIP: multistep fails under adaptive steps and horizon events (survey, Rejected); DOPRI exists on the CPU |
| `warp_metric.rs` (654) | Alcubierre shape function `f(r_s)`, White 2025 nacelle metric, shift vector, energy density, York time | f(0) ~ 1, f(100) ~ 0, wall gating | SKIP: needs a non-Kerr geodesic tracer; a labeled-speculative scene is possible after `so4`/tesseract precedent, no payoff plan |
| `acoustic_metric.rs`, `lattice_hawking.rs`, `fractal_metric.rs`, `nanograv_cd_fit.rs`, `sedenion_geodesic.rs`, `spacetime_algebra.rs`, `chingon_*`, `cd_ladder_force.rs`, `adm_algebra_bridge.rs`, `cosmology_algebra_bridge.rs` | analog gravity, Cayley-Dickson speculative couplings | self-referential | SKIP: no GR reduction (audit 02 falsifiers) |
| `adm.rs`, `spatial.rs`, `ppn_constraints.rs`, `scalar_tensor.rs`, `quantum_inequalities.rs`, `area_quantization.rs` | 3+1, PPN, Brans-Dicke, Ford-Roman, LQG area | present | SKIP: no 3+1 path in Blackhole; Brans-Dicke PPN proofs in sibling 01 |
| `photon_graviton/*`, `photon_graviton_tcmt/*` (about 10k lines) | worldline QFT photon-graviton amplitudes, Ward identities | Ward residuals | SKIP: not rendering |
| `nbody_integration.rs` | complex-time N-body | none | SKIP |

Precision: f64 throughout; no fast-math; Mino integration in `u = 1/r`; no GPU
kernels in gr_core.

### 3.2 grmhd_core (7.6k lines, workspace license)

- Physics: fixed-Kerr BL ideal GRMHD, `logr-theta-phi` grid (`grid.rs`), gamma-law
  EOS (`eos.rs`), HARM-style `cons.rs`/`prims.rs`, PLM-minmod (`recon.rs`), HLL
  (`riemann.rs`), Kastaun-style Brent con2prim (`con2prim.rs`), constrained
  transport (`ct.rs`, 2-D r-theta), geometric source (`source.rs`), RK2 (`evolve.rs`),
  Fishbone-Moncrief torus (`torus.rs`).
- Oracles: FM torus `measured_l == torus.l` and enthalpy identity to 1e-12
  (`torus.rs` tests); magnetic widening of wave speeds (`flux.rs:1450`); GPU
  advance finiteness only (`tests/grmhd_cubecl_parity.rs`); CUDA-vs-CPU prim2con and
  flux parity in `gpu.rs` tests (`assert_cuda_fp64_parity`); metric-inverse
  exactness on the exterior grid. The crate header states "NOT intended as a
  production astrophysical code".
- Precision: FP64 CPU (`wide::f64x4` SIMD in flux loops) and CUDA; FP32 in
  Vulkan and CubeCL, so their parity tolerance is looser.
- GPU kernels: `kernels_grmhd.cu` (366 lines, five kernels: `precompute_metric_kernel`,
  `compute_flux_kernel`, `prim2con_kernel`, `euler_update_kernel`,
  `flux_divergence_kernel`; SoA layout, NVRTC-compiled), `vulkan.rs` (1352),
  `cubecl.rs` (932). Advance only; no ray transport.

| Item | Class |
|---|---|
| Evolution solver (HLL/PLM/CT/RK2, CUDA/Vulkan/CubeCL) | SKIP: Blackhole streams precomputed dumps (`grmhd_streaming.*`, `grmhd_hdf5_loader.*`); a native solver contradicts the data-driven scope and the crate itself disclaims production use |
| Fishbone-Moncrief torus initializer | NEW-PORT 1 (Kerr `l`, no evolution) |
| Kastaun con2prim, CT | SKIP (evolution only) |
| Vulkan/CubeCL GRMHD advance | SKIP: GL-primary architecture names Vulkan only for a named need |
| Block-quantization of `rho`/`u` tiles | ALREADY-CHARACTERIZED: audit 05 M6 (4 bits per value is an 8x cut from RGBA32F); not implemented |

### 3.3 optics_core (18k lines, MIT)

- Physics: gradient-index ray equation `dT/ds = (grad n - (T.grad n) T)/n` with RK4
  (`grin.rs`), complex-index Beer-Lambert, TCMT and Kerr-nonlinear bistability
  (`tcmt.rs`, `fano_tcmt.rs`), Mie cylinder (`mie_cylinder.rs`, `mie_poles.rs`),
  Gerchberg-Saxton phase retrieval, Zernike aberrations, SFWM quantum optics.
- GPU: `algebraic_lensing_grin.cu` (173 lines: CUDA GRIN ray marcher, manual
  trilinear density fetch with periodic wrap, SM89), plus Vulkan WGSL and CubeCL
  kernels of the same march (`algebraic_lensing_gpu.rs`, 2251 lines, CPU-vs-GPU
  parity tests).
- Oracle relevant to Blackhole: isotropic-coordinate `n(rho) = (1 + M/(2 rho))^3/(1 - M/(2 rho))`
  reproduces `b_c = 5.191 M` (0.1 percent from `3 sqrt(3) M`) and the weak-field
  deflection (survey B6).
- Class: GRIN oracle SKIP (redundant, Schwarzschild only, survey B6); TCMT, Mie,
  phase retrieval, SFWM SKIP (analogue optics, not GR transport); GRIN volume
  marcher SKIP for the black-hole scene (no lensing medium exists; the tesseract
  fog is not a refractive medium).

### 3.4 cosmology_core (17.7k lines, MIT)

- Modules: `flrw.rs` (`FlatLCDM`: E(z), distances, lookback, age), `distances.rs`
  (comoving distance, Macquart DM-z), `tov.rs`/`eos.rs` (polytropes, SLy4/APR4
  presets, Love number k2, tidal deformability, mass-radius, TOV maximum),
  `gravastar*.rs`, `bounce.rs`, `sersic.rs`, `halo*.rs`/`nfw_utils.rs`
  (NFW, Dutton-Maccio c(M,z), DC14 cored profile), `galaxy_pipeline.rs`,
  `euclid_morphology.rs`, `frb_calibration.rs` (split conformal), `observational.rs`.
- Oracles: Sersic `b_4 = 7.6693`, `b_1 = 1.6783` (0.01); total luminosity; Abel
  deprojection nonnegative and axisymmetric to 1e-6; planck2018 defaults.
- Numerics: Gauss-Legendre composite quadrature; Ciotti-Bertin third-order `b_n`.
- Class:
  - `flrw`, `distances`, `tov`, `eos`: ALREADY-IN-BLACKHOLE (`cosmology.h`, `tov.h`
    with the same SLy4/APR4 presets and k2).
  - Sersic + Abel: NEW-PORT 7. Docstring defect: "for n = 1, exp(b_1)/b_1^2 = 1"
    is false (5.356/2.816 = 1.90); the formula `2 pi n I_e R_e^2 e^b Gamma(2n)/b^(2n)`
    is correct, so port the formula and test against numerical quadrature.
  - NFW/DC14/Dutton-Maccio: NEW-PORT 7b, lensing-mass overlay; needs an analytic NFW
    deflection that open_gororoba does not provide.
  - `gravastar`, `bounce`, `frb_calibration`, `harmonic_*`, `orthoplex_*`, `manga_*`: SKIP.

### 3.5 cr_transport, casimir_core, tensor_core, snia_core

| Crate | Content | Class |
|---|---|---|
| `cr_transport` (1.7k) | Parker transport, Strang split, ADI diffusion; fixed 2026-09-27 | SKIP: heliosphere |
| `casimir_core` (1.2k, GPL-2.0+) | worldline v-loop Monte Carlo Casimir energy; oracle `-pi^2/(720 a^3)` per area | SKIP |
| `tensor_core` (0.3k) | rank-1/2 TT-cross | SKIP (survey B7) |
| `snia_core` (2.6k) | white-dwarf EOS, 1-D hydro, carbon burning, Arnett-like light curve (`lightcurve.rs`: Ni decay 8.8 d, Co 111.3 d, gamma escape 42 d) | SKIP for the renderer; optional game flavor (supernova beacon events). Inference, not run: the coefficients are Nadyozhin 1994 values (pure-exponential Co) combined with a Bateman term, so L(0) = 6.45e43 against 7.9e43; recompute before use |

### 3.6 spectral_core (9.1k lines, MIT)

- Modules: fractional Laplacian 1-D/2-D/3-D periodic and Dirichlet, N-D FFT to 4-D and
  power spectra (`ndfft.rs`), Haar DWT and Ricker CWT (`wavelet.rs`), DPSS
  multitaper and Thomson F-test (`multitaper.rs`), Lomb-Scargle with Baluev
  false-alarm (`lomb_scargle.rs`), Welch PSD/coherence (`coherence.rs`), IAAFT and
  phase-randomized surrogates (`surrogates.rs`), spectral Navier-Stokes
  (`navier_stokes.rs`, ABC/Beltrami fixtures), change-point detection.
- Oracles: Lomb-Scargle peak within 0.01 of the true frequency with power above
  0.9 and false alarm below 1e-5 (`lomb_scargle.rs` tests 234-242); ABC field
  curl identity (`navier_stokes.rs`); IAAFT rank step only (survey B2).
- Class: FFT/spectrum for texture gates SKIP-with-note (survey B3 owns it);
  IAAFT baked texture is survey B2; ABC/4-D fog survey A5-A6; Lomb-Scargle,
  Welch: NEW-PORT 6; `dpss`/multitaper: SKIP (Lomb-Scargle suffices for uneven
  disk-clock samples); wavelet reservoir "negative-dimension": SKIP.

### 3.7 GPU infrastructure crates

| Crate | Content | Class |
|---|---|---|
| `gororoba_optix` (418 lines, GPL-2.0+) | `dlopen` of the driver library, `optixQueryFunctionTable`, hand-mirrored `#[repr(C)]` option structs, context create/destroy; tests for handle sizes and SBT header alignment; no programs, SBT, or BVH | NEW-PORT (not in T0-T10; `docs/plans/gl-cuda-render-architecture.md` section 0.3 adopts the pattern); port by reading the SDK header at build time, never by copying its layouts (section 5) |
| `gororoba_gpu_cuda` (1.4k) | `DeviceProbe` (sm arch string, VRAM), `CompileOptions` (arch, lineinfo, fast_math, `prec_div`, `prec_sqrt`, `ftz`, `fmad`), `ModuleRegistry` with SHA-256 `ModuleProvenance`, `ManagedBuffer` (unified memory plus prefetch), launch-config helpers | Provenance hash: survey B4 (not landed). Per-kernel `fmad`/`ftz` control: NEW-PORT 8 (parity only). Managed memory: SKIP (tile streaming uses GL PBOs) |
| `gororoba_gpu_cubecl` (156), `gororoba_gpu_vulkan` (2.0k) | runtime probes; ash instance/device/pipeline/descriptor/allocator | SKIP: Vulkan is a named-need port only (architecture doc 0.4 step 6) |
| `gororoba_gpu_bridge`, `gororoba_gpu_readback` | CPU/GPU backend chooser by problem size; descriptor-only readback contracts | SKIP |
| `gororoba_view_core`, `gororoba_view_raster` (0.5k) | ARGB slice rasterizer, RGBA blit, particle raster; crude polynomial Viridis/Inferno and mislabeled "Turbo" (survey) | SKIP |
| `lbm_3d_cuda` OptiX files (`optix_brick_scan.cu` 94, `optix_tracer.cu` 232, `optix_pipeline.rs` 402, `optix_orchestrator.rs` 346) | 8^3 brick max-density scan to AABB list (atomic compaction), custom-primitive GAS, raygen per particle, closest-hit with trilinear SoA fetch through zero-copy SBT pointers, rebuild every 20 steps with `optixAccelRefit` between | NEW-PORT 4, 5 |
| `lbm_3d_cuda` low-bit SoA kernels (fp16/bf16/fp8/int8/int4), `kernel_selector.rs` | static Ada table (MLUPS per tier) from profiling | SKIP: table is hardware-static, not workload-measured; Blackhole's registry lesson (FP16_H2 slower than FP32 on escaped rays) needs a measured selector, not this table |
| `lbm_vulkan` `render.wgsl`, `lbm_3d`, `lbm_core`, `fixed_point_lbm` | volume render (double attenuation, step-dependent opacity), LBM | SKIP (survey) |

### 3.8 Engine, pipeline, verification crates

`gororoba_engine` (3.9k), `gororoba_pipeline` (0.25k): six-layer trait pipeline
(Bit, Parity, Topology, Dynamics, Correction, Verification) and thesis harnesses;
SKIP. `verified_core` (6.9k, GPL-2.0+): `x87_math.rs` (inline-asm FP80 Jacobi,
ties the oracle to one ISA; survey Rejected), `coupler_manifold.rs` (QEC),
monograph book text, Rocq bridges (sibling 01 covers the proofs); SKIP.
Other crates (`data_core` registry mirrors, `lbm_*`, `materials_core`,
`quantum_core`, `navier_stokes_verify`, CLI crates, algebra crates): no
geodesic, transport, disk, lensing, or rendering content beyond what is listed;
SKIP.

## 4. Visual and GPU areas the request singles out

| Area | open_gororoba holds | Blackhole state | Verdict |
|---|---|---|---|
| Disk emission and turbulence | Newtonian NT (`novikov_thorne.rs`); IAAFT and ABC field candidates (survey) | `page_thorne.h`, `disk_turbulence.glsl` (log-normal value-noise fbm, float `fract` hash), volumetric disk #103 | nothing new; B1/B2/B3 remain unlanded survey items |
| Jets | BZ power only | `jet_physics.h` (physics), no jet emission in `shader/` (only a `delta^3` beaming note in `redshift.glsl`) | no port; design task |
| Photon rings, lensing | `shadow_ray_traced`, GRIN | `photon_ring.h`, Mino tracer, observer sky | none |
| Background lensing | none | JWST/star-field sky | none; Sersic sprite is decoration |
| Spectral rendering, tone mapping | bands and filters only | `spectral_channels.h`, `dtBlackbodyChroma`, ACES in `tonemapping.frag` | none |
| GRMHD data | evolution solver, FM torus | loader + streaming; volume sampled only in the legacy tracer | NEW-PORT 1-4 |
| Polarization | none | `stokes_exact.h` (CPU); GLSL `stokesStep` keeps a first-order branch below `tauL = 1e-4`, no series to 0.03 | exact twins and series IN-PLAN (T5 items 1, 2) |
| GPU perf | OptiX brick BVH, NVRTC options, CubeCL/Vulkan advance kernels | GL primary, CUDA optional, OptiX planned | NEW-PORT 4, 5, 8 |

## 5. NEW-PORT specifications

Each entry: target, oracle, payoff, cost, falsifier. Reimplement from the cited
literature; no open_gororoba code is copied.

### NP-1. Kerr constant-l torus generator (Kozlowski-Jaroszynski-Abramowicz 1978)

- Target: `src/physics/fm_torus.h` (header-only, `noexcept`, M = 1), a tool
  `src/tools/fm_torus_snapshot_main.cpp` writing the packed volume that
  `grmhd_packed_loader` consumes (format and axis convention to be read from the loader first; it carries BL `r_min`/`r_max`), and
  `tests/fm_torus_test.cpp`.
- Naming caveat: Fishbone and Moncrief 1976 hold `u^t u_phi` constant (HARM
  `lfish_calc`); holding `-u_phi/u_t` constant with `h u_t` constant is the
  constant-l torus of Kozlowski et al. 1978. gr_core implements the second and
  calls it Fishbone-Moncrief. Recalled, not checked against the paper or HARM
  `init.c` (not fetched); confirm before choosing. Either variant needs its own
  oracle; the formulas below are for constant `-u_phi/u_t`.
- Method: constant `l = -u_phi/u_t`; `l(r_max) = (r^2 - 2 a sqrt(r) + a^2)/(r^(3/2) - 2 sqrt(r) + a)`
  (prograde Kerr circular orbit, Bardeen-Press-Teukolsky 1972; reduces to
  `r^(3/2)/(r-2)` at a = 0). Potential `W = -ln(-u_t)` from the full
  inverse metric `u_t^2 (g^tt - 2 l g^tphi + l^2 g^phiphi) = -1`; enthalpy
  `h = u_t(r_in)/u_t`; polytropic `rho = ((h-1)(gamma-1)/(gamma K))^(1/(gamma-1))`;
  `Omega = -(g_tphi + l g_tt)/(g_phiphi + l g_tphi)`. gr_core has this structure
  and its identities, and uses the Schwarzschild `l` for every spin.
- Oracle (falsifier stated first): (1) `l` equals the mpmath BPT value to 1e-12 for
  a in {0, 0.5, 0.9, 0.998}; (2) pressure maximum on the equator sits at r_max to
  the grid step; (3) `h = u_t(r_in)/u_t` reproduced to 1e-12 at sampled points;
  (4) hydrostatic residual `d_i p/(rho h) + d_i ln(-u_t) ...` decreases under grid
  refinement; gr_core reports 9.22, 5.03, 2.31 on 24, 48, 96 cells as a
  convergence shape to match, not a value to import. A generator that passes with
  gr_core's Schwarzschild `l` at a = 0.9 fails (1).
- Payoff: a thick optically thin RIAF/torus volume on screen with no HDF5 dump;
  closes the "torus appearance" item of accretion-flow R2 once NP-3 lands.
- Cost: about 200 lines plus tool; CPU only.

### NP-2. KS-to-BL azimuth and MKS resampler

- Target: `src/physics/coordinates.h` (`blCoord` and a new `ksPhiOffset(r, a)`), test
  in `tests/coordinates_test.cpp`; header comment for `MKSParams::hslope` states
  `hslope = 1` uniform (McKinney and Gammie 2004), fixing the current "0 = uniform".
- Method: `phi_KS = phi_BL + (a/(r+ - r-)) ln((r - r+)/(r - r-))`, offset zero at
  infinity; `dphi_KS = dphi_BL + (a/Delta) dr`. Numeric check: r = 3, a = 0.9 gives
  -0.458 rad (-26.2 degrees).
- Oracle: quadrature of `a/Delta` to 1e-12 for r in (1.05 r+, 100); `x1` round trip;
  `dth/dx2` against finite differences for hslope in {0.3, 1}.
- Payoff: spiral handedness and phase of resampled MKS data near the hole. Whether
  the packed loader maps cells to texture axes natively was not traced: it carries BL
  `r_min`/`r_max` (`grmhd_packed_loader.cpp:225`), the HDF5 loader skips the Grid
  group, and `blackhole_main.frag` samples an axis-aligned Cartesian box. If native
  MKS arrays reach that texture, the geometry is wrong beyond the azimuth term and
  NP-2 becomes a full MKS-to-Cartesian resampler.
- Cost: under 60 lines.

### NP-3. GRMHD in the default Kerr interop path (renderer work)

`grmhdTexture` is read at `blackhole_main.frag:283-290` as
`clamp((pos - grmhdBoundsMin)/size, 0, 1)` and multiplies disk density by `rho*u`
(`grmhd_dense_emission.glsl`). `interop_trace.glsl`, `rte_step.glsl`, and the CUDA
kernels never sample it. Add a `bhGrmhdSample` in `interop_trace.glsl` behind the
`RayTerminal` seam (#83). Oracle: a uniform-density torus reproduces the analytic
optical depth along a chord to 1e-3. Falsifier: pixels identical with the volume
enabled and disabled means the sampling is not reached.

### NP-4. Brick-occupancy max-mip pyramid

- Target: `src/render/grmhd_tile_upload.cpp` builds an occupancy 3-D `R8` texture
  (max over 8^3 bricks) beside each tile; `shader/include/` gains
  `bhBrickSkip` used by the volumetric march in GLSL and CUDA.
- Fix carried over from D7: brick counts use `ceil(n/8)`; open_gororoba floors and
  never scans trailing partial bricks.
- Oracle: skipped and full marches agree pixel-for-pixel below a threshold that
  scales with the occupancy cut (`rho_max_brick > threshold`); ratio test that
  march step count drops with occupancy instead of wall time (repository rule).
- Payoff: GRMHD frame-rate headroom; no RT cores required, so it works on every
  vendor in the GL-primary architecture.

### NP-5. OptiX brick-AABB accelerator

- Target: `src/cuda/optix_runtime.{h,cpp}` (driver `dlopen` and function table, as
  `gororoba_optix`), `src/cuda/optix_bricks.cu` (scan, AABB compaction, GAS build and
  refit, raygen per chord with `tmax` = chord length, any-hit to list brick
  intervals), `tests/cuda_optix_bricks_test.cu` under `-L cuda`.
- Method transferred from `lbm_3d_cuda`: scan bricks, atomic-compact AABBs, GAS over
  about 2k of 4096 bricks at 128^3, rebuild on a cadence and `optixAccelRefit`
  between, RT on a separate stream so SMs continue Kerr stepping.
- Oracle: hit set per chord equals a CPU slab test on random chords; marched image
  pixel-identical to the non-OptiX CUDA path.
- Gate: measure intersection share of kernel time first; below 20 percent, OptiX
  gains at most 1.25x (architecture doc falsifier). NP-4 is the cheaper first step.
- Not portable from open_gororoba: any SBT layout, since it is LBM-specific.

### NP-6. Lomb-Scargle and Welch light-curve diagnostics

- Target: `src/tools/lightcurve_psd_main.cpp` and `tests/lightcurve_psd_test.cpp`.
- Oracle: a sine of known frequency recovered within 1 percent with false-alarm
  below 1e-5 (open_gororoba's own test shape); a hot spot at r = 6, a = 0
  yields a cyclic-frequency peak at `f = Omega_K/(2 pi) = 6^(-3/2)/(2 pi) = 0.0108` per M.
- Payoff: numeric validation of `diskTimeScale`, hot-spot and Lense-Thirring
  modulation (G5); no pixels.

### NP-7. Sersic sprite and NFW overlay

Sersic `I(R)/I_e = exp(-b_n((R/R_e)^(1/n) - 1))`, `b_n` third-order Ciotti-Bertin,
oracles `b_4 = 7.6693`, `b_1 = 1.6783` (epsilon 0.01 in open_gororoba; tighten to
1e-4 against the incomplete-gamma root). Target `src/render/procedural_galaxy.h`,
star-field sky layer. Payoff cosmetic; hold behind the observer-sky work.

### NP-8. Per-kernel FMA control in CUDA parity builds

Expose `--fmad=false` and `--prec-div=true` for the twin-test binaries only, as
open_gororoba's `CompileOptions` exposes per-module flags. Payoff: removes the
FMA-contraction explanation for ISSUE-009 style outliers when the strict sweep is
run; no image change. Blackhole ships `--use_fast_math`; keep it for production.

## 6. Numeric disagreements and referee

| Quantity | Blackhole (pin) | open_gororoba (pin) | Referee |
|---|---|---|---|
| FM torus `l` for a != 0 | none (no torus) | Schwarzschild `l` (`torus.rs:38`) | BPT 1972 circular-orbit `l`, above |
| KS azimuth vs BL | `bl.phi = x3` | stub returns 0 | closed form in NP-2 |
| MKS `hslope` comment | "0 = uniform" (`coordinates.h:49`) | `test_th_uniform_hslope_1` | McKinney and Gammie 2004: h = 1 uniform |
| GRMHD volume form, HLL bounds, inverse metric sign | n/a | fixed 2026-09-27 | Gammie et al. 2003; determinant of the assembled metric |
| KN ISCO | root-found (#29) | `+q^2/(2 m^2)`, wrong | RN cubic 4.514 at Q = 0.9 (audit 02) |
| Beaming convention | delta^(3+alpha) with sign fixed (#70) | old convention | Liouville invariant I/nu^3 |
| Synchrotron F(x=1) | CPU tables (#74) | 1.5667 | 0.651423 (Rybicki and Lightman 6.31) |
| Torus label | n/a | constant `-u_phi/u_t` torus named Fishbone-Moncrief (`torus.rs`) | FM 1976 is `u^t u_phi` constant; constant-l is KJA 1978 (recalled) |
| Free-free absorption | Kirchhoff j/B_nu | 2.0e10 x textbook at 1e4 K, 1 GHz (D3) | Rybicki and Lightman 5.18a |
| NT flux peak | Page-Thorne (#30) | 1.5 r_isco | Page and Thorne 1974 |
| Sersic n = 1 luminosity note | n/a | docstring claims `e^b/b^2 = 1` | 1.90; formula correct |
| Ni-56 light curve | n/a | Nadyozhin-style coefficients 6.45e43, 1.45e43 erg/s/Msun combined with the Bateman term `exp(-t/tCo) - exp(-t/tNi)` (`lightcurve.rs`) | Nadyozhin 1994 (ApJS 92, 527) coefficients assume a pure-exponential Co term; the combination gives L(0) = 6.45e43 against 7.9e43 (inference, not run) |

## 7. Licensing

Licenses from `Cargo.toml` at the pin: `gr_core`, `optics_core`, `cosmology_core`,
`spectral_core`, `tensor_core`, `lbm_core` MIT; `lbm_3d_cuda` MIT OR Apache-2.0;
`casimir_core`, `gororoba_optix`, `gororoba_gpu_cuda`, `gororoba_gpu_cubecl`,
`gororoba_gpu_vulkan`, `gororoba_view_core`, `gororoba_engine`,
`gororoba_pipeline`, `verified_core`, `lbm_vulkan`, `lbm_3d` GPL-2.0-or-later;
`grmhd_core`, `cr_transport`, `snia_core`, `gororoba_view_raster` inherit the
workspace GPL-2.0-or-later. "Or later" admits Blackhole's GPL-3.0; MIT admits it.
The ported modules in gr_core originated in Blackhole (audit 02 lineage finding).

Flags for a port:

- OptiX SDK headers (`optix.h`, `optix_host.h`, `optix_device.h`,
  `optix_function_table.h`, function-table stubs) carry
  `SPDX-License-Identifier: LicenseRef-NvidiaProprietary` with a redistribution
  prohibition absent an NVIDIA license agreement (read from the installed
  `optix.h` header block). Blackhole includes the SDK from the system install,
  never vendors it, and gates the OptiX target on its presence at configure time.
  `gororoba_optix` hand-mirrors these structs; its own license does not cleanse
  the layouts, so NP-5 reads them from the installed headers instead.
- `optix_tracer.cu` includes `<optix.h>`; its device code is open_gororoba's
  (MIT OR Apache-2.0) and is reimplemented, not copied.
- PCG hash (survey B1), Fishbone-Moncrief 1976, Ciotti-Bertin 1999, Baluev 2008,
  Landi Degl'Innocenti 1985: published algorithms, cited in headers.
- Rust dependencies (`cudarc`, `ash`, `cubecl`, `wide`, `nalgebra`) are not ported.

## 8. Not run and uncertainty

- No cargo build or test; every "test asserts" line is a source reading.
- Not run: the r = 3 azimuth arithmetic (hand calculation, high confidence, about
  90 percent); the BPT `l` formula against mpmath; the Ni-56 coefficient
  recomputation (medium, about 65 percent); whether Blackhole's packed loader
  applies any KS/BL conversion (unread).
- Not read in depth: `photon_graviton*`, `nanograv_cd_fit`, `orthoplex_*`,
  `manga_*`, SFWM and Mie modules; classified from module headers and audit 02.
- Whether NP-5 gains anything is undecided until the intersection-share
  measurement runs; NP-4 could make it moot.
- Raise confidence in NP-1 by running the mpmath `l` check and the refinement
  residual; lower it if the packed loader cannot represent a torus volume at the
  needed resolution.
