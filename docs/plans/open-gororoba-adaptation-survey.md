# open_gororoba: techniques adaptable to the renderer and the tesseract

Status: survey note. No code changes. It extends
[open_gororoba Decomposition](../physics/open-gororoba-decomposition.md), which
judged `gr_core`, `grmhd_core`, `lbm_*`, `cr_transport`, special functions,
Kerr geodesics, the null constraint, and norm projection, and it feeds
[Projection and Rendering of Four- and Higher-Dimensional Structures](hyperdimensional-projection-research.md)
(tesseract) and the disk research on the `docs/accretion-disk-appearance`
branch (Page-Thorne taper, RIAF mode, spiral GRF turbulence, blackbody color).
open_gororoba paths are written `crates/<crate>/src/<file>` plus the symbol.

## 1. Findings

1. open_gororoba is thin where Blackhole needs depth. Nothing in it implements
   a hyperplane-slice raymarch, an SDF, a Hopf map, a quasicrystal or
   cut-and-project construction, a stereographic projection, polarized
   transfer, CIE or blackbody-to-sRGB color, Kerr Mino-time integration, or a
   real adaptive integrator. `crates/verified_core/src/monograph/icosian_projection.rs`
   is 43 lines of prose, "Hopf" appears only in a comment in
   `crates/gororoba_algebra/src/construction/octonion_geometry.rs`, and
   `crates/gororoba_algebra/src/construction/e8_root_system.rs` is a 3-line
   re-export. Each is a claim without an implementation.
2. Few items are adoptable, and none is certain to change pixels. The 120
   unit icosians (600-cell) are the one lane-A kernel worth porting. An IAAFT
   baked texture is a candidate replacement for the value-noise fbm in
   `shader/include/disk_turbulence.glsl`, with unmeasured benefit. An integer
   PCG hash would make that texture reproducible across drivers. The rest are
   test vectors, oracles, and defect reports.
3. open_gororoba's proofs are real but narrow. C-876, C-911, and C-912
   (`proofs/verified/C876_QuaternionRotation.v`, `C911_RotationPreservesNorm.v`,
   `C912_RotationComposition.v`) are kernel-checked `Qed` proofs over exact
   reals with no `Admitted`. They cover the SO(3) sandwich q v conj(q), which
   is the case q_R = conj(q_L). They do not cover the general left-right
   SO(4) pair in `src/render/tesseract/so4.h`, and they say nothing about
   float rounding.
4. Eight open_gororoba defects turned up beyond those already in the
   decomposition (section 4). Three were reproduced by a standalone replica
   (D1 Clifford product, D2 double-double precision, D5 Planck cancellation),
   one by arithmetic (D3), and four by reading. Blackhole-side inconsistencies
   met on the way are kept apart, as in the decomposition.
5. Blackhole already holds the counterpart of most lane-B candidates: zoned
   adaptive Mino steps in `shader/include/interop_trace.glsl`
   (`bhAdaptiveStep`), exact Stokes steps (`stokesStep`, `stokesCompositeStep`),
   chord-segment disk integration (`bhDiskSegment`), and the CUDA mirror in
   `src/cuda/device_physics.cuh` (`d_adaptive_step`, `d_kerr_step`).

## 2. Method and evidence labels

Each candidate carries five labels.

- **Where**: crate, file, symbol.
- **Evidence in open_gororoba**: `tests` (unit tests), `Rocq` (proof file),
  `bench` (measured performance), or `none`. "Read" means the test source was
  read and not executed; no cargo build was run anywhere.
- **Checked here**: what a standalone numpy/mpmath replica confirmed. A
  replica reproduces the algorithm from the Rust source, so it tests the
  algorithm and not the compiled binary.
- **Port**: target file in Blackhole, sketch, cost.
- **Falsifier**: the observation that would kill the candidate.

Provenance tags follow the tesseract note: [math], [pub], [design].

## 3. Lane A: tesseract and hyperdimensional visuals

### A1. Icosians as a 600-cell vertex set

- Where: `crates/gororoba_algebra/src/construction/icosians.rs`,
  `generate_icosians` and `verify_icosian_group_closure`.
- What: the 120 unit quaternions of the binary icosahedral group 2I: 8
  axis units, 16 half-integer sign vectors, and 96 even permutations of
  (phi/2, 1/2, 1/(2 phi), 0) with all sign choices on the three nonzero slots.
  They are the vertices of the 600-cell. The even-permutation filter is an
  inversion count over 24 permutations, so the generator is plain, and the
  interesting property is closure of the set under Hamilton multiplication.
- Evidence: `tests` (`test_icosian_count`, `test_icosian_closure`; read).
- Checked here: a replica gives 120 distinct elements, 0 closure misses over
  all 14,400 products, 12 neighbors per vertex at dot = phi/2 (nearest
  distance 0.618034 = 1/phi), 720 edges, and 9 distinct pairwise dot values.
  All of it matches the 600-cell.
- Defect: none in the generator. The surrounding claims are unsupported: the
  E8-to-icosian-to-quasicrystal chain in `icosian_projection.rs` has no code.
- Port: `src/render/tesseract/tesseract_geometry.cpp` gains a `polytope600Cell()`
  that emits 120 vertices and 720 edges (edge test: dot > 0.7, since the next dot value is 0.5, or
  a constexpr adjacency table). About 40 lines, no shader change; the existing
  perspective and stereographic projection paths draw it.
- Second use: the 120 vertices are a near-optimal spherical code on S^3
  (minimum separation 36 degrees). Pick slice-frame keyframes for the
  isoclinic animation from them and interpolate with the two-slerp form of
  `so4FromPair`. Any 2I element q used as q_L gives a rotation whose orbit
  closes, so a camera tour built from icosians repeats exactly and loops
  without a seam. [design]
- Payoff: a second structure shot (R5 in the tesseract note) with 5-fold
  symmetry that the tesseract lacks, plus loopable orbits. Visual only.
- Falsifier: a `tests/` gate that asserts count 120, closure, degree 12, and
  edge count 720; a render where any vertex has fewer than 12 incident edges.

### A2. Rocq-checked sedenion sign table as a test vector

- Where: `crates/cd_kernel/src/cayley_dickson/signs.rs`
  (`cd_basis_mul_sign`, `cd_basis_mul_sign_iter`, `SignTable`);
  `proofs/verified/C1467_XORSignCocycle.v`.
- What: `e_p e_q = s(p,q) e_(p xor q)` with s from a top-bit recursion; the
  iterative form swaps operands in the (0,1) case and negates in the (1,0)
  case, the same branch structure as the sign function in the tesseract note.
- Evidence: `Rocq` (`sed_sign_table_correct` by `vm_compute` over all 256
  pairs, no `Admitted`; read, not compiled here). The unit tests in
  `cayley_dickson/tests.rs` were not read.
- Checked here: their recursion and their iterative loop agree with the
  doubling product (a,b)(c,d) = (ac - conj(d) b, da + b conj(c)) on every basis
  pair for n = 2, 4, 8, 16, 32 (0 mismatches). This is an independent
  confirmation of the tesseract note's oracle, not a new technique.
- Scope limit: the Rocq theorem shows the literal 16x16 table equals the
  bounded recurrence. It does not show the recurrence equals the doubling
  product; that is a separate file (`C034_CDDoublingIdentity`), which was not
  read.
- Port: copy the 16x16 table (256 entries) into a test in `tests/` as a
  reference vector for whichever sign function `so4.h` or a shader adopts.
  About 30 lines. No runtime use, since quaternion algebra is the only layer the
  scene needs (tesseract note R6).
- Payoff: catches a transcription or convention slip at zero runtime cost.
- Falsifier: any single sign disagreeing at n = 4 or 16 against the doubling
  product implemented in the test itself.

### A3. C-876 as the spec for one so4.h test

- Where: `proofs/verified/C876_QuaternionRotation.v`
  (`C876_quat_rotation_eq_matrix`), mirrored by `quat_rotate_vector` in
  `crates/gororoba_algebra/src/physics/quat_rotation.rs`.
- What: for unit q, Im(q (0,v) conj(q)) = R(q) v, with R written using the
  entries 1 - 2(y^2 + z^2). The proof substitutes 1 = w^2 + x^2 + y^2 + z^2 and
  closes by `ring`, so the identity is an unconditional polynomial identity
  once the matrix is written in the homogeneous form w^2 + x^2 - y^2 - z^2.
- Evidence: `Rocq` (read; `Qed`, no `Admitted`) and `tests`.
- Checked here: not re-run; the identity is textbook.
- Port: one unit test asserting `so4FromPair(q, conj(q))` restricted to the
  spatial block equals R(q), and that the w axis is fixed. In shader code the
  homogeneous form turns a norm drift into a uniform |q|^2 scale, which a
  division by |q|^2 removes exactly, where the unit form leaves a shear. [design]
- Payoff: small. The general SO(4) case, which is what the scene uses, gains
  no proof from C-876.
- Falsifier: a random q of norm 1 +- 1e-3 where the homogeneous and unit forms
  differ in the shader by more than the drift they are meant to absorb.

### A4. Correct Clifford basis product, and Cl(4,0) rotors

- Where: `crates/gororoba_algebra/src/construction/clifford.rs`,
  `clifford_basis_product`. Defective; see section 4, D1.
- What (the correct kernel, standard from Dorst, Fontijne, and Mann): for
  blade bitmasks a and b, the sign is (-1)^s with
  s = sum over k >= 1 of popcount((a >> k) & b), times the product of e_k^2
  over the common bits; the result mask is a xor b. In GLSL:

  ```
  int reorderSign(uint a, uint b) {
    a >>= 1; int s = 0;
    while (a != 0u) { s += bitCount(a & b); a >>= 1; }
    return ((s & 1) == 0) ? 1 : -1;
  }
  ```

- Checked here: the reference form is associative on all 4096 triples of
  Cl(3,1) basis blades, gives e_k^2 = (+1, +1, +1, -1) for Cl(3,1), and gives
  I^2 = +1 for the pseudoscalar I = e1234 of Cl(4,0) with I central in the even
  subalgebra. The last two facts give the split 1/2 (1 +- I) of the even
  subalgebra into H + H, which is the (q_L, q_R) pair of `so4FromPair`. This
  is the geometric-algebra form of the isoclinic split already in `so4.h`.
- Port: tests only. The kernel confirms that `so4.h` and a Cl(4,0) even-rotor
  formulation agree; it adds no rendering capability.
- Payoff: low. Recorded because open_gororoba's own version is wrong and a
  future GA path would copy it.
- Falsifier: the rotor R = (1/2)(1 + I) q_L + (1/2)(1 - I) q_R acting on a
  vector differs from `applyMatrix(so4FromPair(qL, qR), v)` by more than 1e-6.

### A5. Periodic 4D fog by spectral synthesis, checked against fft_4d

- Where: `crates/spectral_core/src/ndfft.rs` (`fft_4d`, `ifft_4d`,
  `power_spectrum_3d`) and `crates/spectral_core/src/lib.rs`
  (`fractional_laplacian_periodic_3d`, multiplier |k|^(2s)).
- What: a Gaussian random field on the torus T^4 with power spectrum |k|^(-p)
  is a sum of cosines over integer wavevectors, exactly periodic in the lattice
  cell that the beam field already uses. A shader evaluates
  sum_i a_i cos(2 pi k_i . x + phi_i) with about 8 modes and needs no 4D texture
  (a 64^4 float volume is 64 MB). open_gororoba contributes only the reference
  transform and spectrum estimator.
- Evidence: the fractional-Laplacian function body was read (Nyquist handling
  is correct because the multiplier is even in k); its tests were not read; none
  exist for noise synthesis.
- Port: `shader/tesseract.frag`, a `fog4(vec4 p)` term that modulates the fog
  extinction along the ray. Cost: 8 cosines per march step, about 8 x 20 ALU on
  the fog path only. The cost is an estimate, not a measurement. [design]
- Payoff: breaks the uniform haze into cloudlike structure that stays coherent
  under the SO(4) animation, because it lives in 4D coordinates.
- Falsifier: the radial power spectrum of a baked 3D slice of the shader field
  (via `fft_4d` or numpy) deviates from |k|^(-p) by more than the mode-count
  sampling noise, or the field shows seams at the period boundary.

### A6. ABC (Beltrami) displacement for woven strands

- Where: `crates/spectral_core/src/navier_stokes.rs`, test fixture `abc()` and
  `abc_has_unit_curl_zero_projected_convection_and_exact_viscous_decay`.
- What: u = (A sin z + C cos y, B sin x + A cos z, C sin y + B cos x) satisfies
  curl u = u, so it is divergence-free and smooth. The fixture is a test input
  in open_gororoba, and using it for strand weaving is this note's design.
- Evidence: `tests` (read; asserts the curl identity exactly in Fourier space).
- Checked here: finite-difference curl(u) - u = 7e-11 at a random point for
  A = B = C = 1 and 1e-10 for (sqrt 3, sqrt 2, 1). Streamline separation from a
  1e-9 offset grew to 1.9e-8 and 1.2e-7 over t = 40, which supports smooth
  braiding and does not support any chaos claim.
- Port: `shader/tesseract.frag`, replace or add to the quaternion twist warp of
  tesseract note R3: offset the transverse strand coordinates by
  eps (u_x, u_y)(x, y, w). Six trig calls per evaluation. [design]
- Payoff: strands that braid without self-intersection when
  eps < 1 / max|grad u|, a bound the quaternion twist lacks in closed form.
- Falsifier: a render where two strands of one family cross at eps below the
  bound, or where the twist warp already produces the same braid visually at
  lower cost.

## 4. Defects in open_gororoba

The decomposition holds the earlier list. New entries:

| ID | Where | Defect | How found |
|---|---|---|---|
| D1 | `gororoba_algebra/src/construction/clifford.rs` `clifford_basis_product` | Sums +-1 per common generator instead of multiplying, and returns mask 0 whenever any generator is shared. e1e2 * e2 returns (-1, 0) instead of (+1, e1). Wrong on 176 of 256 Cl(3,1) basis pairs against the reference in A4. | Python replica of the Rust logic plus the reference kernel |
| D2 | `algebra_analysis/src/double_double.rs` `sin`, `cos`, `add` | Documented as ~31 digits; the series loop exits when `hi` stops changing, which leaves a residual near ulp(hi). Measured relative error 1e-20 to 5e-19 at x = 0.5 to 3 against mpmath at 50 digits. The one test read (`test_dd_sincos_pi4`) tolerates 1e-15, so it cannot see this. `add` is the sloppy variant that loses accuracy under cancellation. | Python replica against mpmath |
| D3 | `gr_core/src/absorption.rs` `free_free_absorption` | Pairs the prefactor 3.68e8 of the exact form (T^-1/2 nu^-3 (1 - e^(-h nu/kT))) with the Rayleigh-Jeans exponents (T^-3/2 nu^-2). The Rayleigh-Jeans prefactor is about 0.018 (3.7e8 h/k = 0.0178). At T = 1e4 K, nu = 1 GHz the result is 2.0e10 times the textbook value. | Arithmetic against Rybicki-Lightman 5.18a and 5.19b, constants recalled and not re-fetched |
| D4 | `gr_core/src/absorption.rs` `synchrotron_self_absorption` | alpha = (n_e sigma_T / 2)(nu_c / nu)^2 (1 + 2.4 theta) is a scaling estimate, not j_nu / B_nu. Kirchhoff's law fixes the absorption coefficient once the emissivity is known, so this form has no derivation behind it. | Read |
| D5 | `gr_core/src/absorption.rs` `planck_function` | `exp(x) - 1` cancels for small x: in f64 it returns 0 for x < 1.1e-16, and in f32 it returns 0 for x < 6e-8, with relative error 1.2e-4 at x = 1e-4. At optical frequencies x is about 24000 / T[K], so the f32 error is near 1e-5 at 1e7 K and invisible; the defect matters for radio-band or hot-plasma callers only. | Replica in f32 |
| D6 | `gr_core/src/coordinates.rs` `ks_phi_correction`, `mks_to_bl` | The comment says the KS-to-BL azimuth correction "requires the geodesic history". It does not: dphi_KS = dphi_BL + (a / Delta) dr, a function of r only, with closed form (a / (r+ - r-)) ln((r - r+) / (r - r-)). The function returns 0.0 unconditionally, and `mks_to_bl` labels the KS azimuth as BL phi. | Read |
| D7 | `lbm_3d_cuda/src/optix_brick_scan.cu` `scan_brick_occupancy` | `nx / brick_size` floors the brick count, so trailing partial bricks are never scanned when a dimension is not a multiple of 8, although the inner loop guards `ix < nx`. | Read |
| D8 | `cd_kernel/src/turboquant/e8_rotation.rs`, `rotation.rs` | Block rotation multiplies each 16D block by a vector in the octonion subalgebra, a norm-preserving octonion left/right pair. The claim of 8 x 15 = 120 free parameters is wrong: each block is chosen from 240 discrete roots. `rotation.rs` quotes a WHT 3-bit MSE of 1.444 and `e8_rotation.rs` quotes 0.0339 for the same rotation, so the two comments measure different quantities. | Read |

Blackhole-side items met while checking, tracked separately from the table:
`src/physics/coordinates.h` `blCoord` carries the D6 label (`bl.phi = x3`, the
KS azimuth returned as BL); the `MKSParams` comment says hslope 0 is uniform
while the function body treats hslope = 1 as uniform; and
`thermalSynchrotronAbsorptivity` keeps the defect already tracked in the
decomposition. The Kirchhoff route j_nu / B_nu is the authority for
absorption, and Blackhole follows it.

Lower-severity notes: `lbm_vulkan/shaders/render.wgsl` attenuates twice
(`shadow = exp(-opacity * 3)` on top of `opacity += (1 - opacity) * dens`) and
its opacity does not scale with step length. `gororoba_view_raster` labels a
neon ramp "Turbo" and its Viridis/Inferno are crude polynomial fits, not the
published maps. `lbm_vulkan/src/besag_clifford_cubecl.rs` `pcg_shuffle_kernel`
draws with replacement and is not a permutation (its doc says so).

## 5. Lane B: black hole renderer

`shader/include/disk_turbulence.glsl` is on `main` (PR #102, commit 02d4694).
It multiplies the disk emissivity by exp(sigma g - sigma^2/2), with g a
four-octave trilinear value-noise fbm scaled to unit variance, orbiting at
Omega = 1 / (r^1.5 + a), and it bounds the shear winding with two cross-faded
copies of period 240 M. That file is the target for B1 and B2. The worktree
this note lives in predates the PR.

### B1. Integer PCG hash for the disk texture

- Where: `crates/lbm_vulkan/shaders/besag_clifford.wgsl`, `pcg_hash`
  (state = x * 747796405 + 2891336453; word = ((state >> ((state >> 28) + 4)) ^
  state) * 277803737; result = (word >> 22) ^ word), the published PCG hash
  (Jarzynski and Olano 2020).
- What: an integer hash is bit-exact on every GPU and on the CPU. `dtbHash`
  in `disk_turbulence.glsl` is a float `fract` hash whose result depends on
  fp32 rounding of `p * 17` products, so two drivers can differ, and the CUDA
  path uses a different integer hash (`d_hash` in
  `src/cuda/device_physics.cuh`).
- Evidence: `none` in open_gororoba for hash quality (used, not tested). The
  hash itself is published, and this note did not measure quality.
- Port: `dtbHash(vec3 cell)` becomes three chained PCG rounds over `uvec3(ivec3(cell))`
  (the cell coordinates are already integers after `floor`). About 25 integer
  ops per hash against about 12 flops now; the value noise takes 8 hashes per
  octave, 4 octaves, 2 copies, so the texture cost roughly doubles on the
  hash portion. The cost is an estimate, not a measurement. The
  `disk_turbulence_shader_test` replica then becomes exact.
- Payoff: the pattern becomes identical across vendors and against the test
  replica; no visual change intended.
- Falsifier: the sampled texture differs between two GPUs or from the CPU
  replica by any bit; or the profiled cost of the integer path exceeds the
  frame budget.

### B2. IAAFT surrogate as a baked replacement for the value-noise fbm

- Where: `crates/spectral_core/src/surrogates.rs`, `iaaft_surrogate` (1D) and
  `phase_randomize`.
- What: the Schreiber-Schmitz iteration alternates a rank-order step that
  imposes a target one-point distribution with a Fourier step that imposes a
  target amplitude spectrum, and finishes on the rank step so the marginal is
  exact. The source matches the published algorithm.
- What it changes against the shipped fbm: four octaves of value noise sum to
  a near-Gaussian marginal by construction (the file scales it by 1/0.213),
  so the log-normal factor is already well matched and the marginal is not the
  gap. The gaps are the lattice-aligned structure of trilinear value noise and
  a spectrum that is a sum of four band-limited humps, not a chosen power law.
  A baked field with a chosen slope removes both. Whether that is visible under
  the exposure rule is unmeasured, so this is a design bet. [design]
- Evidence: `tests` (`test_iaaft_preserves_distribution` was read: it feeds a
  5-sample signal and asserts the sorted output equals the sorted input to
  1e-10, which checks the final rank step only and never the spectrum).
- Checked here: a 2D replica on a 128 x 128 torus, target = a log-normal
  transform (sigma 0.8) of a k^-1.5 amplitude field, 60 iterations from white
  noise: the radial power spectrum matches within 1.4e-3 in log10 over
  k = 2..39, and the marginal is exact by construction. The spectrum target came
  from the same field, so the check shows convergence and not that the target is
  physical.
- Defects: 1D only; `partial_cmp(...).unwrap()` panics on NaN input; two sorts
  per iteration.
- Port: an offline baker writes a tileable R16F texture, periodic in azimuth
  and clamped in ln r. Keep the aging and cross-fade of `bhDiskTurbulenceFactor`
  unchanged and replace only `dtbFbm(q)` with a fetch at (phase, ln r). The
  winding problem stays with the two cross-faded copies, which need two
  different texture offsets. Cost: one fetch per copy in place of 32 hashes.
- Falsifier: an A/B capture of a face-on disk where the baked texture is
  indistinguishable from the fbm after exposure and tone mapping (the bet
  fails), or where a seam appears at the azimuth wrap or the cross-fade shows
  stripes (the port fails).

### B3. Spectrum and box-counting metrics as a texture regression gate

- Where: `crates/spectral_core/src/ndfft.rs` (`power_spectrum_2d`,
  `power_spectrum_3d`), `crates/lbm_vulkan/src/box_counting_cubecl.rs`
  (`box_counting_kernel`).
- What: a radial power spectrum and a box-counting dimension of an iso-level
  of the texture, computed offline in numpy, give two scalar summaries that a
  test can bound. The shipped `disk_turbulence_shader_test` bounds only the
  mean factor within 5 percent.
- Evidence: tests for these functions were not read.
- Port: a Python or C++ test under `tests/` that samples the shader replica on
  a grid and asserts a spectral slope band. About 60 lines.
- Falsifier: the slope drifts across a change to the noise (that is the gate
  working), or the metric fails to distinguish the value-noise fbm from a
  white field.

### B4. Kernel identity in the run manifest

- Where: `crates/gororoba_gpu_cuda/src/module.rs`, `ModuleProvenance`,
  `KernelProvenance` (SHA-256 over source and canonical compile options).
- What: a stable identity for a compiled module. `src/physics/reproducibility.h`
  is Blackhole's manifest home; recording a source hash for the CUDA
  translation unit and the nvcc option set there is about 20 lines.
- Evidence: tests not read.
- Payoff: bookkeeping for CUDA/GLSL parity runs; no pixels.

### B5. Compensated accumulation: only the time accumulator, measure first

- Where: `crates/algebra_analysis/src/double_double.rs` (`two_sum`,
  `two_product`); tests `test_dd_two_sum_exact` (one case:
  (1 + eps) + eps, tolerance 1e-30) and `test_dd_two_product_exact` were read
  at that depth.
- What Blackhole accumulates: read from `kerrStep` in `shader/include/kerr.glsl`
  and `d_kerr_step` in `src/cuda/device_physics.cuh`. The angular state is a unit
  vector n with tangent w on S^2, renormalized and re-projected onto the
  Carter shell every step, so no scalar phi accumulates and drift in the
  angles is bounded by the projection. The scalars that accumulate are
  `ray.t` (`ray.t += dlam * dt`, or an `fmaf`) and the affine parameter, and
  neither enters a right-hand side; `ray.r` accumulates and does feed back, and
  `rNew` and `vrHalf` already carry `precise`.
- Checked here: 200,000 f32 increments of 1e-3 (true sum 200): naive error
  0.451, Kahan error 1.5e-5. That confirms the mechanism for a long scalar sum.
  It does not show that `ray.t` error is visible: `t` drives time-of-flight
  delay, not the image at fixed frame time. Uncertainty: about 75 percent that
  no image change results.
- Port constraint: reassociation removes compensation silently. GLSL needs
  `precise` on the accumulator statements; CUDA needs `__fadd_rn` and
  `__fsub_rn` because `--use_fast_math` is on; host code under `ci-release`
  needs the per-target `-fno-fast-math` override.
- Falsifier: trace 1000 rays with impact parameter within 1e-3 of the critical
  value in f32 with and without compensation on `ray.t` and compare terminal t
  against the f64 CPU tracer; no reduction in error slope kills it. Not run.

### B6. Isotropic-optical-metric ray equation as an independent oracle

- Where: `crates/optics_core/src/grin.rs`, `rk4_step` (dT/ds =
  (grad n - (T . grad n) T) / n).
- What: for static Schwarzschild in isotropic coordinates the exact null rays
  are rays in a medium with n(rho) = (1 + M/(2 rho))^3 / (1 - M/(2 rho)).
- Checked here: RK4 on this n gave a critical impact parameter of 5.191 M
  against 3 sqrt(3) M = 5.196 M (0.1 percent), and a deflection at b = 100 M of
  0.041172 against the weak-field series 0.041178 (1.5e-4 relative).
- Verdict: Schwarzschild only; Kerr needs a Randers term. Blackhole pins the
  critical impact parameter to the closed form and has Carlson-based
  deflection, so this adds no independent referee. Rejected as redundant.

### B7. Not provided or not suited

- Nothing in open_gororoba covers polarized transfer (Blackhole has
  `stokesStep`), CIE color (Blackhole uses the Kim et al. cubic fit to the
  Planckian locus in `dtBlackbodyChroma`, so D5 does not reach it), symplectic
  or Mino-time Kerr stepping, or a real adaptive integrator.
- LUT compression. `crates/tensor_core/src/tt_cross.rs` is a rank-1 and rank-2
  symmetry-adapted TT-cross for sharply peaked configurational integrals, not
  a general table compressor. The TurboQuant crates quantize LLM key-value
  caches: WHT rotation, Lloyd-Max codebooks, sign packing. A replica of the
  codebook step on a log-normal field (sigma 0.8, 8 bits) gave relative MSE
  4.6e-3 for a uniform linear quantizer, 4.6e-3 for Lloyd-Max in the linear
  domain, and 2.1e-4 for a uniform quantizer in the log domain. A log-domain
  uniform quantizer beats a fitted codebook here by 20x, so the codebook
  machinery adds nothing for log-normal fields. (The Lloyd-Max code itself
  reproduces theory: 3-bit Gaussian MSE 0.03448 against the tabulated 0.03454.)
- `crates/lbm_3d_cuda/src/kernels_fp32_soa_cs.cu` is a cache-policy variant
  (`__stcs` streaming stores) of an LBM kernel, with an expected 5 to 15
  percent gain stated in its own comment and not measured here. It is not a
  compensated-sum kernel. Streaming stores suit bandwidth-bound LBM; a
  compute-bound ray tracer with a write-once framebuffer gains nothing worth a
  port.

## 6. Precision note for every float port

Compensated sums, TwoSum, and TwoProduct are removed by compiler reassociation
and contraction. The lanes are: GLSL `precise`; CUDA `__fadd_rn` / `__fmul_rn`
(and `__fmaf_rn` for the product error); host C++ built with
`-fno-fast-math` per target under `ENABLE_FAST_MATH`. Without them, the
0.45-to-1.5e-5 improvement measured above disappears with no diagnostic. A gate
belongs next to any port: a GLSL and CUDA unit test that feeds TwoSum a case
whose exact error is nonzero and asserts the error term is nonzero.

## 7. Ranked adoption

### Tesseract, top 5

| Rank | Item | Cost | Why this rank |
|---|---|---|---|
| 1 | A1 icosians and 600-cell, plus icosian camera tour | ~40 lines geometry, no shader | Only lane-A kernel with a verified count, closure, and edge structure; adds a second structure shot and seamless loops |
| 2 | A6 ABC displacement for strands, against the R3 twist warp | ~6 trig calls, shader | Bounded, divergence-free braid; a design bet, cheap to A/B against the twist |
| 3 | A5 spectral-synthesis 4D fog with an `fft_4d` oracle | ~8 cosines on the fog path | Coherent 4D haze with no 4D texture; validation is external and easy |
| 4 | A2 Rocq-checked 16x16 sign table as a test vector | ~30 lines test | Free cross-check of the sign function |
| 5 | A3 C-876 as an so4.h unit test, homogeneous rotation form | ~20 lines test | Cheap consistency test; proof scope is SO(3) only |

A4 (Clifford kernel) is a test-only item and ranks just below A3; its value is
that open_gororoba's own version is wrong.

### Black hole, top 5

| Rank | Item | Cost | Why this rank |
|---|---|---|---|
| 1 | B2 IAAFT baked texture replacing the fbm | offline tool plus two fetches | Only candidate with a possible visible gain; the benefit over the shipped fbm is unmeasured and the A/B capture decides it |
| 2 | B1 integer PCG hash in `disk_turbulence.glsl` | ~25 integer ops per hash | Bit-exact texture across vendors and against the test replica; roughly doubles hash cost |
| 3 | B3 spectrum and box-counting regression gate for the texture | ~60 lines test | The shipped test bounds only the mean factor; a slope gate protects B2 and any later noise change |
| 4 | B4 kernel identity in the run manifest | ~20 lines | Reproducibility bookkeeping for CUDA/GLSL parity runs |
| 5 | B5 compensated `ray.t`, after measurement | 4 flops per step | Mechanism confirmed, benefit doubtful; adopt only if the photon-ring measurement shows an error slope |

Fewer than five items change pixels, because open_gororoba has few: no entry
in this list is a strong adoption. D3 (never port `free_free_absorption`) and
the D6 closed form for the KS azimuth are defect reports that protect
Blackhole from copying open_gororoba.

### Rejected

- **Adams-Bashforth-Moulton 8** (`crates/gr_core/src/forces/abm8_integrator.rs`):
  the coefficients are correct (exact through polynomial degree 7, verified
  with rational arithmetic), but a multistep method needs a fixed-step history
  and fails under adaptive steps and horizon or disk-crossing termination events.
- **x87 FP80 accumulation** (`crates/cd_kernel/src/x87_primitives.rs`): no GPU
  equivalent, and it ties the CPU oracle to one ISA. The double-double fallback
  carries D2.
- **TurboQuant, Lloyd-Max codebooks, WHT rotation, E8 block rotation, `fwht`,
  `tt_cross`**: see B7 for the LUT-compression numbers. At d = 4, a WHT with
  Rademacher diagonals yields a finite set of signed Hadamard maps, not the
  rotation group. D8 applies.
- **Cariow factorizations** (`cariow_factorization.rs`): sedenion product
  schedules (122 multiplies at 16D, Rocq-proved equal to the product); the
  tesseract needs the quaternion layer only, and the 32D count is a target.
- **`lbm_vulkan/shaders/render.wgsl`**: double attenuation and step-dependent
  opacity; Blackhole's Beer-Lambert segment integration is correct already.
- **The "Turbo" colormap and polynomial Viridis/Inferno in `gororoba_view_raster`**.
- **`ks_phi_correction`** (D6): stub returning 0.
- **B6 GRIN oracle**: redundant with the closed-form critical b and Carlson
  deflection; Schwarzschild only.
- **`__stcs` streaming stores**: see B7.
- **Leray field synthesis, brick-occupancy scan (D7, OptiX BVH-specific), LBM
  for disk texture, Fishbone-Moncrief and MRT solvers**: the decomposition and
  section 5 give the reasons.
- **E8 to 4D quasicrystal projection, Hopf fibration, cut-and-project, SDF
  work**: no implementation exists. A hyperplane slice of the periodic 4D beam
  field at an irrational orientation is already a cut-and-project structure, and
  the isoclinic rotation in `so4.h` is already the Hopf flow on S^3.

## 8. Uncertainty and checks not run

- Not run: any cargo build or test. Every "read" result is a source reading.
- Not run: B5 on Blackhole (needs a build and a photon-ring ray set); A5 and A6
  frame cost and visual comparison; B1 cost; the B2 A/B capture.
- Not read: `C034_CDDoublingIdentity.v`; `cayley_dickson/tests.rs`; the tests
  behind the box-counting, spectrum, and module-provenance items; the
  fractional-Laplacian tests; `crates/gororoba_algebra/src/lie/e8/root_system.rs`
  beyond its root generator (which matches the textbook 112 + 128 form).
- Constants in D3 come from recall of Rybicki-Lightman 5.18a and 5.19b, with an
  internal consistency check: 3.7e8 h/k = 0.0178 reproduces the tabulated 0.018.
- The crate walk covered `cd_kernel`, `fwht`, `gororoba_algebra` (Clifford,
  icosians, E8, octonion geometry, quaternion rotation), `algebra_analysis`
  (double-double, projective geometry), `spectral_core`, `optics_core`,
  `tensor_core`, `lbm_*` shaders and kernels, `gororoba_gpu_cuda`,
  `gororoba_view_*`, `gr_core` (absorption, synchrotron, coordinates, forces),
  and the Rocq directory. The cosmology, materials, quantum, and data crates
  were sampled by symbol search only, and a hit there would change this note.

## References

- Dorst, Fontijne, Mann, Geometric Algebra for Computer Science (2007), blade
  product sign and bitmask conventions.
- Schreiber and Schmitz, "Improved surrogate data for nonlinearity tests",
  Phys. Rev. Lett. 77 (1996), the IAAFT iteration.
- Jarzynski and Olano, "Hash Functions for GPU Rendering", JCGT 9 (2020), the
  PCG hash.
- Rybicki and Lightman, Radiative Processes in Astrophysics (1979), sections 5.2
  and 5.3 (free-free absorption).
- Conway and Smith, On Quaternions and Octonions (2003), the binary icosahedral
  group; Baez, "From the Icosahedron to E8" (2018).
- McKinney and Gammie (2004), ApJ 611, 977, MKS coordinates.
- Kim et al. (2002), cubic fit to the Planckian locus, as used by
  `dtBlackbodyChroma`.
- Neumaier (1974), improved compensated summation; Knuth TwoSum, Dekker
  TwoProduct.
