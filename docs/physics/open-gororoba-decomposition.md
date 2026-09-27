# open_gororoba Decomposition

open_gororoba is a Rust workspace whose `gr_core`, `grmhd_core`, `lbm_*`, and
`cr_transport` crates overlap Blackhole's physics. Parts of `gr_core` were
ported from Blackhole, so matching code in the two trees is shared lineage,
not independent confirmation; mpmath or a cited paper is the referee for
both. This page maps each governing principle to its discretization in both
trees and gives a verdict. Paths name open_gororoba `crates/...` and
Blackhole repository-relative files; symbols are preferred to line numbers.

## Special functions

- open_gororoba has no modified Bessel K evaluator. `optics_core/src/bessel.rs`
  implements integer-order complex J_n and Y_n for Mie scattering.
- `gr_core/src/synchrotron.rs` `synchrotron_f` and `synchrotron_g` switch
  at x = 0.01 and x = 10 between asymptotes and a Fouka-Ouichaoui fit, the
  same seams Blackhole removed (see [Special Functions](special-functions.md)).
- `grmhd_core/src/eos.rs` is a gamma-law closure p = (gamma - 1) u. It has no
  Synge K_3/K_2 Maxwell-Juttner enthalpy, so nothing in it consumes K.

The Boost-free kernel therefore takes nothing from open_gororoba.

## Motion and observation

| Principle | open_gororoba | Blackhole | Verdict | Falsifier |
|---|---|---|---|---|
| Kerr null geodesics, Carter separation in Mino time | `gr_core/src/kerr.rs`: separated potentials in u = 1/r, DOPRI5, negative initial potentials clamped to zero; Kerr shadow test checks only that shadow pixels exist | second-order Mino stepping in `observer_sky_map.h` and the Kerr tracers | Blackhole's form stands; reject negative initial potentials rather than clamp | turning radii and critical curve vs Bardeen closed form under step halving |
| Null constraint g(v, v) = 0 | `gr_core/src/null_constraint.rs` solves for v^t with a root choice that assumes g_tt < 0 | `src/physics/verified/null_constraint.hpp` | adapt root selection to future orientation inside the ergoregion | equatorial point with g_tt > 0: residual zero and conserved E > 0 for the chosen root |
| Norm projection | `gr_core/src/energy_conserving.rs`: RK4 plus radial/polar rescale; returns early when the current norm is near zero, before applying a nonzero target | additive projection in `verified/energy_conserving_geodesic.hpp` | skip; projection holds the norm, not E and L | track E and L over a Kerr orbit with projection every step |
| Adaptive force integrator | `gr_core/src/forces/adaptive_integrator.rs` is named Dormand-Prince but steps RK4 with an RK2 error estimate, and returns `t + new_dt` instead of the step it took | none | skip | y' = y with a forced step change: returned time and state disagree |
| Beaming, Liouville I_nu / nu^3 | `gr_core/src/doppler.rs` and `src/physics/doppler.h` both document F_nu ~ nu^alpha and apply delta^(3 + alpha), which matches the opposite sign convention F_nu ~ nu^-alpha | GLSL `redshift.glsl` uses delta^3 or delta^4 with no alpha | fix the documented convention in `doppler.h` | transform a signed power law and check I_nu / nu^3 at matched frequencies |
| Thin-disk flux | `gr_core/src/novikov_thorne.rs`: Newtonian zero-torque factor with the peak fixed at 1.5 r_ISCO | `src/physics/page_thorne.h`, tested against quadrature | Blackhole's form stands | flux peak radius vs mpmath Page-Thorne quadrature across spin |
| Carlson R_F, R_D, R_J | `pathion_ellip/src/carlson.rs`: complex Carlson over 32-dimensional pathion values, 1e-10 tolerance | real forms in `elliptic_integrals.h`, 1e-15 against mpmath | skip | not applicable to real Kerr roots |

## GRMHD (`grmhd_core`)

| Principle | Discretization | Verdict | Falsifier |
|---|---|---|---|
| Volume form sqrt(-g) = Sigma abs(sin theta) in Boyer-Lindquist | `metric.rs` `sqrt_neg_g` returns sqrt(Sigma) abs(sin theta); the CUDA kernel uses Sigma abs(sin theta) | defect in the CPU path | determinant of the assembled 4-metric at generic (r, theta, a) |
| Inverse metric, t-phi block | `kernels_grmhd.cu` divides by `fabs(det)`; the block determinant is negative, so g^tt takes the wrong sign | defect | g^{mu alpha} g_{alpha nu} = delta over the exterior |
| Conservation d_t(sqrt(-g) U) + d_i(sqrt(-g) F^i) = sqrt(-g) S | `cons.rs` includes magnetic stress terms; the CUDA kernel drops them from momentum | reconcile CUDA to CPU | all eight conserved components CPU vs CUDA on magnetized moving states |
| HLL flux with fast magnetosonic bounds | `riemann.rs` `wave_speeds` takes va^2, but every call in `flux.rs` passes 0.0, so the bounds ignore B | defect | raise B at fixed fluid state: bounds must widen |
| Primitive recovery (Kastaun, Kalinani, Ciolfi 2021) | `con2prim.rs` Brent root with floors; the moving-state round-trip test allows 15% density error | adapt only with a tight round-trip gate | property-generated primitives reproduce conserved state to a stated tolerance |
| PLM reconstruction, minmod | `recon.rs`, with exact-linear and step tests | reusable component | convergence order on smooth advection |
| Constrained transport, div B = 0 | `ct.rs`, 2-D r-theta layout; test uses a static torus and allows 1% growth | adapt before 3-D use | divergence under a time-varying field in all directions |
| Geometric source S_j = T^mu_nu (1/2) d_j g_mu_nu | `source.rs` with simplified stress; the caller passes `dx1` as dr while r = exp(x1) | defect | stationary Fishbone-Moncrief residual under refinement |
| Fishbone-Moncrief torus initial data | `torus.rs`; tests check nonzero density and field only | adopt as initial data after a force-balance gate | force-balance residual across the torus |

Blackhole has no GRMHD evolution; it streams precomputed iharm3d, KORAL, or
BHAC snapshots. These rows become relevant only if a native solver is
planned.

## Lattice fluids and transport

| Principle | Discretization | Verdict | Falsifier |
|---|---|---|---|
| D2Q9 BGK, viscosity (tau - 1/2) / 3 | `lbm_core/src/lib.rs`, mass and Poiseuille tests | separate component | shear-wave decay vs viscosity across tau |
| Guo body force | D2Q9 `apply_force` adds 3 w_i c_ix F rho without the velocity terms or the (1 - 1/(2 tau)) prefactor; D3Q19 in `lbm_3d/src/solver.rs` carries both | use the D3Q19 form | one-step momentum change equals F dt at nonzero velocity |
| Induction dB/dt = curl(v x B) + eta lap B | `lbm_3d/src/mhd.rs` centered curl with forward Euler | skip as an ideal-MHD solver | Fourier-mode growth under uniform advection |
| Fixed-point storage | `fixed_point_lbm`: Q16.16/Q32.32 with wrapping arithmetic, f32 collision | skip | moving-equilibrium moment drift vs f64 |
| Parker cosmic-ray transport | `cr_transport/src/solver.rs` documents ADI diffusion but sweeps x only with K_xx of an anisotropic tensor; first-order upwind advection | defect | rotated-field manufactured solution exercising every tensor component |

## Status of the defects

The open_gororoba defects above belong to that repository. Blackhole
defects found alongside them are tracked as Blackhole issues: the
`doppler.h` sign convention, the Rayleigh-Jeans factor in
`electron_temperature.h` `thermalSynchrotronAbsorptivity`, and the CUDA
elliptic threshold near m = 1.
