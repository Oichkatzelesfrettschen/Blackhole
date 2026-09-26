# open_gororoba novel numerics: what makes Blackhole cheaper and more accurate

Scope: the algebra, numerics, and infrastructure crates of open_gororoba (`cd_kernel`,
`fwht`, `gororoba_sparse_grid`, `fixed_point_lbm`, `pathion_ellip`, `spectral_core`,
`lattice_filtration`, `surreal_algebra`, `neural_homotopy`, `verified_core`, `tensor_core`,
`cosmic_scheduler`, `gororoba_engine`, `gororoba_algebra`, `gororoba_structurable`,
`algebra_analysis`, `algebra_experimental`, `stats_core`, `lbm_core`, `lbm_3d`), the Rocq
`proofs/` tree, and the `registry/` claims system. They are judged against Blackhole's hot
paths. The GR, GRMHD, optics, cosmology, and GPU crates, plus the formula cross-checks, are
covered in `02-open-gororoba-crossref.md`. The campaign `-ffp-contract` digest measurement
is in `03-game-engine.md`. Both repositories stayed read-only. Every executable ran outside
both trees; the drivers live in `harness/`, and `harness/README.md` defines `$PYTHON`,
`$HARNESS`, `$BH`, `$BOOST`, and `$OUT` for the commands below, which run in `$OUT`.

## Executive summary

open_gororoba's headline results are algebraic: Cayley-Dickson (CD) zero-divisor
combinatorics, box-kites, PSL(2,7), and associator gap quantization (`docs/NAVIGATOR.md`
Layer 0, `docs/GRAND_SYNTHESIS.md` Scale I). None of the non-associative levels (dimension 8
and up) reaches a Blackhole hot path. An integrator needs an associative algebra to carry
the chain rule and a composable propagator, and the sedenion tower gives that up by
construction (C-001, C-002). The value for Blackhole comes from the associative and numerical
edges of the project instead:

1. **The quaternion/Clifford rotation theorems (C-876, C-911, C-912) point to the Lorentz
   structure of polarized transfer.** The Stokes propagation matrix minus its trace is an
   so(1,3) generator. Its exponential therefore has a closed form driven by one complex
   square root of the biquaternion norm `(eta + i rho).(eta + i rho)`. I built and measured
   that propagator. It matches a 50-digit referee to 1e-11 in every regime tested. RK4 needs
   180 ns (Faraday depth 1) to 550 us (depth 1000) per segment to reach 1e-6. The exact step
   costs 190-250 ns in its robust direct-integral form. A 55-70 ns split form stays
   <= 8e-10 only for absorption depth >= 0.1 per segment, so it serves as an optimization,
   not the default. **ADOPT.** The construction itself is Landi Degl'Innocenti
   (1985) and ipole prior art, not open_gororoba code.
2. **Cross-checking `pathion_ellip`'s quartic solver against numpy found two independent
   root-finder defects.** Blackhole's CPU `findRadialRoots` returns zero real roots for
   `(r^2-1)(r^2-4)` and for every point on the Kerr critical curve
   (`analytic_kerr_geodesic.h:188`, `:207`). `pathion_ellip::solve_quartic` returns the
   negated roots whenever the depressed cubic term is nonzero (`quartic.rs:74-75`). Both
   fixes were verified in scratch copies. **ADOPT (bug fix).**
3. **The precision-tier idea (x87 80-bit vs Kahan vs plain, `algebra_analysis`
   `precision_policy`) pays off twice.**
   - Boost.Math's default `promote_double` policy runs Blackhole's analytic-Kerr elliptic
     calls in x87 long double. `promote_double<false>` makes `jacobi_sn` 8.5x faster and
     `ellint_1` 3.3x faster, with results that differ by at most 2e-15.
   - Kahan-compensated state accumulation in an FP32 RK4 photon orbit cuts total position
     error 15x at 1200 steps and 1700x at 30000 steps, for 16 extra adds per step. RK4
     truncation stays at or below 1e-7 at every step size tested (a long-double h/64 truth
     run), so FP32 roundoff dominates.
   - **ADOPT the policy change. PROTOTYPE the FP32 compensation on the GPU.**
4. **The same stress test found an FP32 cancellation in the shipped GPU Stokes/RTE step.**
   `(1 - E)/A` just above the `tauL < 1e-4` guard carries up to 2.9e-4 relative error in
   FP32. A 4-term series holds 8e-8 up to `tauL = 0.03`. **ADOPT.**
5. **Carlson duplication with Carlson's 1995 stopping rule and the correct series gives
   full double accuracy at 3.8x (R_F), 3.0x (R_D), and 8.2x (R_J) less cost** than
   Blackhole's `tol = 1e-10` loop. Blackhole's series coefficients are wrong: the tight
   tolerance masks them, and the defect shows as a 1e-9 error when the tolerance is
   loosened. **ADOPT when Carlson enters a hot path.** Today it is test-only.
6. **Structured random rotation plus Lloyd-Max quantization (TurboQuant, `fwht`) beats
   per-block affine quantization only at 2 bits/value** on a synthetic Kolmogorov field.
   Plain Walsh-Hadamard energy compaction with global bit allocation wins at 2-4 bits. That
   points to 8x GRMHD tile bandwidth reduction (RGBA32F to 4 bits/value) as the prototype,
   with compaction, not Gaussianization, as the mechanism. **PROTOTYPE.**
7. **The exact-integer-window theorem (C-1736) and exact dyadic arithmetic
   (`surreal_algebra::dyadic`) give the right model for cross-host deterministic game
   math.** `fixed_point_lbm` is the wrong exemplar: its collision runs in f32.
   **PROTOTYPE, as design guidance.**

Everything else is NOT-APPLICABLE, each for a stated computational reason: pathion 32D
Carlson, Cariow sedenion schedule, E8 rotation, QJL, IDCT8 butterfly, LBM crates,
`cosmic_scheduler`, TT-cross, `spectral_core`, `lattice_filtration`, `neural_homotopy`,
`gororoba_engine`, and Walsh-domain noise.

## Method, tools, and replay facts

- open_gororoba HEAD `006230b603c2f1705a72c6bb32348833abfb4565`. Blackhole HEAD
  `34e1bf1814bb4701b58aa3a09e17692417869979`. Both trees were read-only. The pre-existing
  local changes (`M .gitignore`, `?? .ignore`) in open_gororoba were left untouched.
- clang++ 22.1.8. rustc/cargo 1.98.1. Python with mpmath 1.4.1, numpy 2.5.3, scipy 1.18.1.
  Boost 1.90 headers from the Conan cache. CPU: AMD Ryzen 5 5600X3D.
- Timing runs were pinned with `taskset -c 3`. Each figure is the median or min of 5
  repetitions.
- C++ compiled with `-std=c++23 -O2`, and additionally `-ffp-contract=off` where stated.
  These flags omit Blackhole's `-march=native`, so they measure algorithmic cost rather than
  a particular target ISA.
- Cargo ran with `CARGO_TARGET_DIR` outside both trees, `--offline --locked`, and
  open_gororoba's own `Cargo.lock` copied into the scratch bench crate.
- Every formula a port needs is also written out below.
- Evidence labels:
  - **proved**: a Rocq theorem with no conclusion-restating axiom.
  - **tested**: compared against an independent reference.
  - **self-tested**: checked only against the same code's own outputs.
  - **asserted**: stated in comments or docs only.
  - **measured here**: run in this audit.

## Novel concepts elucidated

### N1. The Cayley-Dickson XOR basis rule and the left-multiplication matrix (C-1142)

Plain language: in every CD algebra the product of two basis units is another basis unit,
up to a sign, and the index of the result is the bitwise XOR of the two input indices. That
turns multiplication by a fixed element `a` into a dense matrix whose row `i`, column `j`
entry is `a_{i XOR j}` times a sign table. Tensor cores can then run CD products as
ordinary matrix-vector work.

Math: `e_i e_j = gamma(i,j) e_{i XOR j}`, so `L_a[i][j] = a_{i XOR j} gamma(i XOR j, j)`.
C-1142 proves that `j -> i XOR j` is an involutive bijection. The row scan is therefore
collision-free.

Where it lives: `crates/gororoba_algebra/src/gpu/tensor_avt/kernels.cu:19` (WMMA) and
`mod.rs:6`. The theorem is `proofs/verified/C1142_XORScatterGatherDuality.v`.

Evidence: proved (the XOR combinatorics). Kernels self-tested.

### N2. Hadamard-diagonalized CD multiplication (Cariow 2013, C-1646)

Plain language: the sedenion product matrix is block-symmetric Toeplitz. A 16-point
Hadamard transform nearly diagonalizes it. The product then costs 16 diagonal multiplies
plus 106 sparse corrections, 122 in total instead of 256.

Where it lives: `crates/cd_kernel/src/cayley_dickson/cariow_factorization.rs:44-46` and
`:203-229`.

Evidence:
- C-1646 is proved: extensional equality with the CD product over R^16.
- Tested against an independently written sedenion multiply for all 256 basis pairs and 16
  dense vectors (`:401-434`).
- The 32D figure of 498 multiplications is labeled a conjecture in the file (`~:452`).

### N3. Quaternion and Clifford rotation theorems (C-876, C-911, C-912)

Plain language: the quaternion sandwich `q v q*` equals the rotation matrix `R(q) v` for
unit `q`. It preserves the norm. Sandwiches compose by quaternion product for all `q`,
unit or not.

Where it lives:
- `proofs/verified/C876_QuaternionRotation.v`, discharged by `ring`/`nsatz`.
- `crates/gororoba_algebra/src/physics/quat_rotation.rs:46-79`.
- `crates/verified_core/src/quaternion.rs:104-112`. This one is extracted from Rocq and
  cross-validated against the CD quaternion in `verified_core/tests/cross_validate.rs` at
  1e-12.

Generic Clifford construction: `crates/gororoba_algebra/src/construction/clifford.rs`. Two
defects there:
- Its docstring maps Cl(3,0) to "H (+) H". Cl(3,0) is isomorphic to M2(C), the Pauli
  algebra. H (+) H is Cl(0,3).
- `clifford_basis_product` reads `k < p` against the 1-based `basis_square`. Untested here.

Evidence: proved (C-876, C-911, C-912). The Rust is tested against the independent CD
implementation.

**The bridge to Blackhole.** The Stokes propagation matrix `K` is `alpha_I 1 + K'`, where
`K' = [[0, eta^T], [eta, -[rho]_x]]` is the generator of a Lorentz transformation. `eta` is
the dichroism boost, `rho` the Faraday rotation. The Lie algebra so(1,3) is the complexified
quaternion algebra, sl(2,C) ~ Cl(3,0). Write `w = eta + i rho`. The eigenvalues of `K'` are
`+-L1` and `+-i L2`, with

    (L1 + i L2)^2 = w.w = (|eta|^2 - |rho|^2) + 2 i (eta.rho)

That single complex square root, the biquaternion norm, replaces a 4x4 matrix exponential.
Section M3 builds and measures the resulting propagator. Attribution: the closed form is
Landi Degl'Innocenti & Landi Degl'Innocenti (1985) and is used by ipole. open_gororoba
contributes the quaternion/Clifford framing and the proved rotation identities, not the
propagator.

### N4. Precision tiers: x87 80-bit, Kahan, and the crossover rule

Plain language: summing N terms in a format with unit roundoff `u` accumulates about `N u`
error. Compensated (Kahan) summation keeps it near `2u`. An 80-bit accumulator shrinks `u`
by 2^11. The repository's crossover is `2^-53 / 2^-64 = 2048` terms: the N at which the
accumulated x87 error `N 2^-64` reaches one f64 rounding `2^-53`. Below it, an x87
accumulator rounded once to double carries at most about one extra double rounding. Past
2048 terms x87 alone no longer holds the
result to one double rounding, and compensation takes over. The ratio therefore bounds how
far extended precision suffices; it is no threshold below which plain f64 is as accurate.
Equating plain-f64 error `N 2^-53` to one x87 rounding would give `N = 2^-11`, which has no
dispatch meaning.

Where it lives:
- `crates/algebra_analysis/tests/precision_tier_dispatch.rs:11-17`.
- Kahan at `crates/algebra_analysis/src/codebook/linear_algebra.rs:24-45`.
- x87 Givens rotation at `crates/cd_kernel/src/x87_jacobi_kernels.rs:25,62`, tested against
  an independent f64 recomputation (`:132-166`).
- `crates/algebra_analysis/benches/x87_bench.rs`.

Evidence:
- The crossover arithmetic is self-tested (a unit test of the formula).
- The x87 kernels are tested.
- The ranking "x87 > Kahan > FMA > naive" is asserted in comments.

Defect: `crates/verified_core/src/x87_math.rs:22-66` takes the quadrant-aware
`fpatan`/`atan2` angle on x86_64. Elsewhere it takes `0.5*atan(2apq/(app-aqq))`. The two
disagree by pi/2 when `app < aqq`, so x86_64 and aarch64 builds pick different Jacobi
rotations. Verified by reading.

Blackhole maps: Boost's default policy (measured in M2) and FP32 GPU RK4 accumulation
(measured in M4).

### N5. Exact-integer windows and dyadic arithmetic (C-1736, `surreal_algebra`)

Plain language: a floating-point sum or product is exact, and therefore independent of
evaluation order, FMA contraction, and host, when every intermediate is an integer (or
dyadic rational) that fits the significand. C-1736 proves the concrete case. An 8-term dot
product of 7-bit integers peaks at `8*127^2 = 129032 < 2^17`, which is exact in a 17-bit
significand.

Where it lives:
- `proofs/theories/IDCT8DP4ExactBound.v`, proved by `nia`/`vm_compute` with no axioms,
  exported as C-1736.
- `crates/surreal_algebra/src/dyadic.rs:1-135` stores `num: i128` over `2^shift`. Add, sub,
  and mul are exact.
- Release builds keep `overflow-checks = true` (workspace `Cargo.toml:527`).
- Gap: `align` shifts with `<<`, which drops high bits silently. It panics only on shift
  amounts >= 128.

Evidence: proved (C-1736). dyadic self-tested (3 tests).

Contrast, `fixed_point_lbm` (`src/lib.rs:1-13`):
- The crate claims integer-exact mass conservation, but the collision in
  `src/solver.rs:122-145` converts every `Q16_16`/`Q32_32` value to f32, computes the
  equilibrium in f32, and re-quantizes with truncating `as` casts. Only storage and
  streaming are integer.
- The SASS cycle counts (IADD3 0.53 vs FFMA 4.53) are asserted.
- The conservation tests are self-tested from a rest state.

### N6. Complex Carlson duplication "over pathions" (`pathion_ellip`, C-993)

Plain language: `PathionCarlson` splits a 32-component vector into 16 coordinate pairs,
treats each pair as a complex number, and runs complex Carlson R_F/R_D/R_J duplication on
each.

Where it lives: `crates/pathion_ellip/src/carlson.rs:18-61`, `:75-221`;
`src/diagonalizer.rs:12-40`.

Assessment:
- The algebra plays no role. The docstring claims the planes "diagonalize the
  non-associative algebra into 16 independent, commutative C planes". Pairing `(e_i,
  e_{i+15})` is not a subalgebra: `e_2 e_17 = +-e_19` lands in plane `(4,19)`, and
  `(x e_2 + y e_17)^2 = -(x^2+y^2) e_0` lands in plane 0.
- The reusable kernel is ordinary complex Carlson duplication.
- C-993 ("RF branch-free") is kernel-checked but vacuous. `proofs/theories/
  CarlsonIntegrals.v:32` declares `Axiom RF_positive`, which is the theorem's own
  statement, and C-993 is proved by `exact` of that axiom.

Evidence: complex Carlson tested against scipy values at 1e-5 to 1e-6 tolerances. C-993
proved only in name.

### N7. Structured random rotation plus Lloyd-Max quantization (TurboQuant, `fwht`)

Plain language: multiply a block by random signs, apply a fast Walsh-Hadamard transform, and
multiply by random signs again. The coordinates become nearly Gaussian and nearly
independent, so one precomputed Lloyd-Max codebook fits every block. The fast JL rotation
`D1 H D2` costs `O(d log d)` adds.

Where it lives:
- `crates/fwht/src/lib.rs:63-138`, MIT OR Apache-2.0. 5 tests pass.
- `crates/cd_kernel/src/turboquant/rotation.rs:1-47`.
- `crates/cd_kernel/src/lloyd_max.rs:206`.

Evidence: KS test against Haar in `e8_validation.rs`. The MSE numbers are self-tested golden
regressions (`integration_test.rs`, `regression_test.rs`).

### N8. Even/odd IDCT butterfly (C-1735)

Plain language: the 8-point inverse DCT splits into even and odd halves, costing 32
multiplies instead of 64.

Where it lives: Rocq only (`proofs/theories/IDCT8EvenOdd.v`). No Rust kernel exists.

Evidence: proved. The count is not state of the art. Loeffler-Ligtenberg-Moschytz (1989)
computes the 8-point DCT with 11 multiplications.

### N9. Infrastructure concepts

- **Sparse brick occupancy.** `gororoba_sparse_grid/src/lib.rs:114-186` counts active bricks
  with POPCNT. The byte-packed variant skips its tail mask when `valid_bytes ==
  bitset.len()`, so `[0xFF,0xFF,0xFF]` with 20 bricks returns 24 (verified by reading).
  The crate has no lookup API.
- **Tensor-train cross.** `tensor_core/src/tt_cross.rs:17-144`. Ranks are hard-coded to 1
  or 2, there is no maxvol, and a singular 2x2 pivot block silently returns a zero matrix.
- **Claims registry.** It carries 1572 claims with statuses and falsifiers, and
  `docs/preregistered/README.md` defines the policy. It works as process: every Blackhole
  validation doc could state its falsifier up front. C-993 shows that "kernel_checked"
  alone proves nothing when an axiom restates the conclusion.

## Mapping table

| Concept | Blackhole hot path (file:line) | Expected or measured delta | Evidence | Verdict |
|---|---|---|---|---|
| N3 Lorentz/biquaternion exact Stokes propagator | CPU full-K RK4 `stokes_transport.h:369-400` (tests only); GPU simplified K `shader/include/stokes_transport.glsl:65`, `src/cuda/device_physics.cuh:2199` | Measured: 1e-11 max error in all regimes. RK4 needs 181 ns to 553 us for 1e-6. Exact 190-220 ns robust, 55-60 ns fast | Math proved (C-876 framing); kernel measured here vs mpmath | ADOPT (C++ and GLSL reimplementation) |
| Thin-regime cancellation (found by the N3 stress test) | GLSL `stokes_transport.glsl:82-99`; CUDA `device_physics.cuh:~2231-2254` | Measured: FP32 `(1-E)/A` error 2.9e-4 at `tauL=1e-4`; 4-term series 8e-8 | measured here | ADOPT (series in GLSL; `expm1f` in CUDA) |
| N6 quartic cross-check | `findRadialRoots` `analytic_kerr_geodesic.h:188,207` (test path `tests/analytic_geodesic_reproducibility_test.cpp`) | Measured: 0 of 2 known quartics solved before the fix, all solved after | measured here | ADOPT (two-line fix plus regression test) |
| N6 complex Carlson plus Carlson 1995 rule | `elliptic_integrals.h:60-200` (tests and helper functions only) | Measured: RF 304->80 ns, RD 343->116 ns, RJ 1374->167 ns at <= 7e-16 error | tested (mpmath referee) | ADOPT when used in a hot path; pathion 32D wrapper NOT-APPLICABLE |
| N4 x87 insight applied to Boost policy | `analytic_kerr_geodesic.h:340,385` | Measured: `jacobi_sn` 1375->162 ns, `ellint_1` 19.4->5.9 ns, diff <= 2e-15 | measured here | ADOPT (policy argument) |
| N4 compensated accumulation in FP32 RK4 | `shader/include/geodesics.glsl:181`, verified `rk4.glsl`, CUDA FP32 kernels | Measured CPU FP32: 15x-1700x lower error. Overhead 1.07-1.08x on a 12-flop RHS; derived 3-5% on the Kerr RHS | measured here (CPU FP32 emulation) | PROTOTYPE (GPU A/B not run) |
| N7 rotation + Lloyd-Max quantization | GRMHD tiles `grmhd_streaming.h:92-99` (RGBA32F) | Measured (synthetic): RMSE/sigma 0.166 vs affine 0.210 at 2 bits; loses at >= 4 bits | measured here (synthetic field) | NOT-APPLICABLE as shipped |
| WHT energy compaction + bit allocation (N7 transform, used differently) | same | Measured (synthetic): 0.035 at 4 bits vs affine 0.042; 8x smaller than RGBA32F | measured here (synthetic field) | PROTOTYPE |
| N5 exact-integer window, dyadic ledger | `src/game/*.cpp` (doubles, `std::log` in `blackhole_time_field.cpp:42`, `kerr_time_field.cpp:69-71`) | Derived: turns "same binary and host" into a cross-host guarantee | proved (C-1736) | PROTOTYPE (design); `fixed_point_lbm` code NOT-APPLICABLE |
| FWHT for spectral noise | `src/physics/noise.cpp` (per-voxel hash noise) | Measured: Walsh low-pass has neighbor correlation 1.000 inside dyadic cells and 0.000 across them (blocky); Fourier 0.977 everywhere | measured here | NOT-APPLICABLE |
| N2 Cariow schedule | no 16D algebra in Blackhole | -- | proved and tested | NOT-APPLICABLE |
| N1 XOR L_a / tensor-core CD | Christoffel contraction differs per ray, so no shared matrix to batch | -- | proved | NOT-APPLICABLE |
| N8 IDCT8 butterfly | no DCT in bloom or tone mapping | -- | proved | NOT-APPLICABLE |
| E8 block rotation, QJL, sign-pack popcount | no inner-product compression workload | -- | self-tested | NOT-APPLICABLE |
| `gororoba_sparse_grid` | GRMHD octree occupancy | Standard popcount, has a tail bug, no lookup | self-tested | NOT-APPLICABLE |
| `tensor_core` TT-cross | LUTs are 1D (`multifreq_lut.h:269-309`) | Nothing to compress; rank fixed at 1 or 2 | self-tested | NOT-APPLICABLE |
| `cosmic_scheduler` two-phase clock | game turn loop, taskflow | Blackhole already uses an integer turn count; `enforce_timing` is never read (`phase_scheduler.rs:111-171`) | self-tested | NOT-APPLICABLE |
| `lbm_core`, `lbm_3d` (D2Q9/D3Q19 BGK and MRT) | no fluid solver; GRMHD comes from external codes | -- | Taylor-Green independent test | NOT-APPLICABLE |
| `spectral_core` fractional Laplacian | -- | -- | not reviewed in depth | NOT-APPLICABLE |
| `lattice_filtration` | -- | `compute_graph_persistence_b0` returns V-E of the active subgraph (beta0 - beta1), not beta0 (`topology.rs:53-70`) | read | NOT-APPLICABLE |
| `verified_core` `monograph/topological_rendering.rs` | -- | 40 lines of prose, no code | read | NOT-APPLICABLE |
| `neural_homotopy`, `gororoba_engine`, `gororoba_structurable`, `algebra_experimental` | -- | Thesis machinery. Engine and LBM criterion benches are `2+2` placeholders | read | NOT-APPLICABLE |

## Measured micro-benchmarks

### M1. Carlson R_F, R_D, R_J: accuracy and cost

Setup:
- Referee: mpmath `elliprf/elliprd/elliprj` at 40 digits on 630 argument sets.
  - 400 log-uniform triples on [1e-3, 1e3].
  - 30 complete-integral sets `(0, 1-k^2, 1, 1-n)` with k up to 0.999999.
  - 200 incomplete sets `(cos^2 phi, 1-k^2 sin^2 phi, 1, 1-n sin^2 phi)`.
- Blackhole's header was included unchanged. `carlson95` is the duplication loop with
  Carlson's 1995 stopping tolerance and the DLMF 19.36 series.

Commands:

    $PYTHON $HARNESS/carlson/gen_ref.py
    clang++ -std=c++23 -O2 -I$BH/src -I$BOOST $HARNESS/carlson/bench.cpp -o bench && taskset -c 3 ./bench

| Function | Variant | max rel err | median rel err | ns/call |
|---|---|---|---|---|
| R_F | Blackhole `tol=1e-10` | 6.6e-16 | 1.2e-16 | 303.6 |
| R_F | Blackhole series at `tol=2.5e-3` | 8.0e-10 | 8.4e-11 | -- |
| R_F | carlson95 `r=2.5e-3` | 4.4e-16 | 1.2e-16 | 79.7 |
| R_F | Boost 1.90 (default policy) | 2.2e-16 | 0 | 610.5 |
| R_F | pathion_ellip complex | 6.4e-16 | 1.4e-16 | 561.3 |
| R_D | Blackhole `tol=1e-10` | 7.7e-16 | 1.6e-16 | 343.4 |
| R_D | Blackhole series at `tol=1.5e-3` | 3.6e-08 | 1.6e-11 | -- |
| R_D | carlson95 `r=1.5e-3` | 6.1e-16 | 1.5e-16 | 115.8 |
| R_D | Boost | 2.2e-16 | 0 | 1160.7 |
| R_D | pathion_ellip complex | 3.3e-10 | 1.0e-13 | 140.3 |
| R_J | Blackhole `tol=1e-10` | 9.7e-16 | 1.9e-16 | 1373.5 |
| R_J | Blackhole series at `tol=1.5e-3` | 3.8e-08 | 4.1e-11 | -- |
| R_J | carlson95 `r=1.5e-3` | 7.2e-16 | 1.3e-16 | 166.5 |
| R_J | Boost | 2.2e-16 | 0 | 1754.6 |
| R_J | pathion_ellip complex | 6.3e-10 | 5.9e-14 | 1426.9 |

carlson95 averages 5.2, 5.7, and 6.0 duplication steps for R_F, R_D, and R_J.

Findings:
- Blackhole's `tol = 1e-10` forces about 17 duplication steps (derived: `log4(1e10)`; not
  counted). Its termination series
  coefficients are wrong, and the tight tolerance hides that. In `carlsonRf`
  (`elliptic_integrals.h:78-81`):

  | Series term | Blackhole coefficient | Correct coefficient |
  |---|---|---|
  | e3 | -3/22 | +1/14 |
  | e2^2 | 3/44 | 1/24 |
  | e2 e3 | 1/14 | -3/44 |

- The falsifier ran as predicted. At Carlson's own tolerance, Blackhole's series errs at
  1e-9 (R_F) and 4e-8 (R_D, R_J). The correct series stays at 4-7e-16.
- `carlsonRj` also runs a full nested R_F loop for every R_C term. The closed form removes
  it:
  - `R_C(x,y) = atan(sqrt((y-x)/x))/sqrt(y-x)` for x < y.
  - `R_C(x,y) = asinh(sqrt((x-y)/y))/sqrt(x-y)` for x > y.
- pathion_ellip's R_D and R_J stop at 3e-10 to 6e-10 because they converge against
  `1e-10^(-1/8)`. Its R_F is accurate, but costs 561 ns in complex arithmetic.
- Correct coefficients for a port, with `A = mean`, `X = (A-x)/A` and so on, per DLMF 19.36.1:
  - R_F: `E2 = XY - Z^2`, `E3 = XYZ`,
    `R_F = (1 - E2/10 + E3/14 + E2^2/24 - 3 E2 E3/44)/sqrt(A)`.
  - R_D and R_J: the DLMF 19.36.2 constants 3/14, 1/6, 9/22, 3/26 and 3/14, 1/3, 3/22,
    3/26 respectively.
- Hot-path status: none. `grep` finds no production caller of `carlsonR*` or
  `ellipticK/E/Pi`. Only `tests/elliptic_integrals_test.cpp` and helpers in the same header
  use them. The win lands when an analytic Kerr path in the style of Gralla-Lupsasca adopts
  Carlson forms.

### M2. Boost.Math `promote_double`: the x87 tier inside Blackhole's dependency

Boost's default policy evaluates double arguments in `long double`, which on x86-64 is the
x87 80-bit unit that `cd_kernel::x87_*` exploits on purpose. `analytic_kerr_geodesic.h:340`
(`jacobi_sn`) and `:385` (`ellint_1`) inherit that policy.

    clang++ -std=c++23 -O2 -I$BOOST $HARNESS/carlson/boostpol.cpp -o boostpol && taskset -c 3 ./boostpol

| Call | promoted (default) | `promote_double<false>` | max difference |
|---|---|---|---|
| `ellint_1(k)` | 19.4 ns | 5.9 ns | 7.9e-16 rel |
| `jacobi_sn(k,u)` | 1375.4 ns | 161.5 ns | 1.9e-15 abs |
| `ellint_rf(0,1-k^2,1)` | 94.2 ns | 15.9 ns | -- |

The accuracy cost is at most 2e-15. Consumers are
`tests/analytic_geodesic_reproducibility_test.cpp` and the CPU reference path. CUDA uses its
own FP32 Cephes AGM (`device_analytic_kerr.cuh:50`).

### M3. Exact polarized-transfer propagator vs RK4

Referee: mpmath `expm` at 40-50 digits of the augmented 5x5 generator `[[-K ds, J ds],
[0, 0]]` applied to `(S0, 1)`. That is the exact constant-coefficient segment solution for
Blackhole's `K`:
- `(I,Q,U,V)` rows `[aI,aQ,0,aV]`, `[aQ,aI,rV,0]`, `[0,-rV,aI,rQ]`, `[aV,0,-rQ,aI]`, as in
  `stokes_transport.h:378-381`.
- Positivity holds: `|eta| <= alphaI`.

Cases:
- Set A: 108 segments with Faraday depth `tauF = rho*ds` in {0.01 ... 1000} and
  `alphaI*ds` in [0.01, 2].
- Set B: 48 optically thin, Faraday-thick segments with `alphaI*ds` in {1e-3, 1e-6, 1e-9}
  and `tauF` in {10, 1000}.

Exact propagator (the direct-integral form, which is the one to port):

    L1^2, L2^2 = +-h + sqrt(h^2 + (eta.rho)^2),  h = (|eta|^2 - |rho|^2)/2,  D = L1^2 + L2^2
    e^{-K' t} = a0(t) - b1(t) K' + a2(t) K'^2 - b3(t) K'^3
      a0 = 1 + (L2^2 (cosh L1t - 1) - L1^2 (1 - cos L2t))/D
      a2 = (2 sinh^2(L1t/2) + 2 sin^2(L2t/2))/D
      b1 = (L2^2 sinh(L1t)/L1 + L1^2 sin(L2t)/L2)/D
      b3 = t [(sinh(L1t)/(L1t) - 1) - (sin(L2t)/(L2t) - 1)]/D      (series for |x| < 0.1)
    S(s) = e^{-aI s} [a0 S0 - b1 K'S0 + a2 K'^2 S0 - b3 K'^3 S0]
         + A0 J - B1 K'J + A2 K'^2 J - B3 K'^3 J

`A0..B3` are the integrals `int_0^s e^{-aI t} {a0, b1, a2, b3}(t) dt`, built from four
closed forms:
- `Ich = [phi(aI-L1) + phi(aI+L1)]/2`, with `phi(x) = -expm1(-x s)/x`.
- `Ish = [phi(aI-L1) - phi(aI+L1)]/(2 L1)`.
- `Ic = [aI (1-EC) + L2 E sin]/(aI^2+L2^2)`.
- `Is = [(1-EC) - aI E s sinc]/(aI^2+L2^2)`, with `1-EC = -expm1(-aI s) cos + 2 sin^2(L2 s/2)`.

These combine as:
- `A0 = (L2^2 Ich + L1^2 Ic)/D`.
- `B1 = (L2^2 Ish + L1^2 Is)/D`.
- `A2 = (Ich - Ic)/D`.
- `B3 = (Ish - Is)/D`.

Moment series `M_n = int_0^s t^n e^{-aI t} dt` take over when `L1 s` or `L2 s < 0.1`:
- `M_n` comes from downward recurrence for `aI s <= 8` and upward recurrence above.
- `Ish = M1 + L1^2 M3/6 + L1^4 M5/120 + L1^6 M7/5040`.
- `A2` and `B3` use the analogous even and odd series.

`K'v` costs 8 multiply-adds, so both polynomial evaluations cost 6 sparse matvecs. The fast
"split" form `S = Sinf + e^{-Ks}(S0 - Sinf)` with `Sinf = K^{-1} J` is cheaper, but it
cancels catastrophically as `alphaI*ds -> 0`.

    $PYTHON $HARNESS/stokes/gen.py; $PYTHON $HARNESS/stokes/gen_thin.py
    clang++ -std=c++23 -O2 -I$BH/src $HARNESS/stokes/bench.cpp -o bench && taskset -c 3 ./bench

| Regime (per segment) | split form | direct form | Blackhole RK4, 1 step | RK4 with `n = ceil(2 abs(K) ds)` |
|---|---|---|---|---|
| `tauF=0.01..1`, `aI ds` in [0.01, 2] | <= 1.1e-14 | <= 1.9e-15 | 0.19-1.7 | 1.2e-3 (n=2-3) |
| `tauF=10` | 3.3e-14 | 1.7e-15 | 1.0e2 | 7.4e-4 (n=12) |
| `tauF=100` | 1.2e-11 | 2.4e-13 | 1.8e6 | 9.4e-3 (n=149) |
| `tauF=1000` | 1.5e-10 | 1.1e-11 | 1.2e10 | 1.2e-1 (n=1442) |
| thin `aI ds=1e-3`, `tauF=10 / 1000` | 7.9e-9 / 8.9e-5 | 9.3e-16 / 1.1e-11 | 68 / 5.6e9 | 8.7e-4 / 9.4e-2 |
| thin `aI ds=1e-6`, `tauF=10 / 1000` | 2.4e-3 / 0.42 | 1.6e-15 / 1.4e-13 | 39 / 4.2e9 | 8.1e-4 / 7.7e-2 |
| thin `aI ds=1e-9`, `tauF=10 / 1000` | 7.4e2 / 2.2e5 | 2.2e-16 / 7.6e-14 | 26 / 6.9e9 | 6.2e-4 / 1.2e-1 |

All error values are max relative error.

RK4 substeps needed for a 1e-6 max error, found by doubling search, on Set A:

| tauF | 0.01 | 1 | 10 | 100 | 1000 |
|---|---|---|---|---|---|
| mean steps | 11 | 10 | 72 | 1579 | 30037 |
| cost at 18.4 ns/step | 204 ns | 181 ns | 1.3 us | 29 us | 553 us |

Cost per call (min of 5):

| Method | Set A | Set B |
|---|---|---|
| RK4 single step | 18.2 ns | 18.3 ns |
| split exact | 59.8 ns | 54.7 ns |
| direct exact | 192.3 ns | 218.8 ns |
| Blackhole simplified `stokesStep` (alphaI + rhoV only) | 24.7 ns | 27.5 ns |

Findings:
- A single RK4 step is unusable once `abs(K) ds > ~1`.
- To match the exact step at 1e-6, RK4 costs about the same at `tauF <= 1`, 7x more at
  `tauF = 10`, 150x at 100, and 2900x at 1000.
- Only the direct form holds in the thin, Faraday-thick regime.
- Set C (64 segments, `aI ds` in {0.01, 0.03, 0.1, 0.3}, `tauF` in {10, 1000}) sets the
  branch point. At `tauF = 1000` the split form errs 2.3e-7, 2.1e-8, 8.0e-10, and 4.2e-10
  respectively. The direct form stays at <= 1.6e-11.
- The direct form is the default and the only form that meets a 1e-10 gate at every
  measured depth. The split form is an optimization for `aI ds >= 0.1` where the error
  budget is at least 1e-9 (its 8.0e-10 and 4.2e-10 at `tauF = 1000` fail a 1e-10 gate).

Where it runs today:
- Full-K transfer (`stokesStepFull`: rhoQ conversion, alphaQ/alphaV dichroism) is called
  only from `tests/stokes_invariants_test.cpp`.
- Both GPU paths implement the simplified K only (`stokes_transport.glsl:65`,
  `device_physics.cuh:2199`; CUDA dispatch `kernels_fp32.cu:48-50`).

What it buys:
- It makes the CPU full-K reference exact.
- It adds Faraday conversion and dichroism to the GPU at 2.2x (split) to 8x (direct) the
  CPU cost of the simplified step. GPU cost was not measured.

**Cancellation already shipping on the GPU.** The same regime exposes the simplified step's
emission factor. In FP32, `(1 - E)/A` just above the `tauL < 1e-4` guard
(`stokes_transport.glsl:82-99`; CUDA `device_physics.cuh`, the `tauL < 1.0e-4f` branches)
loses digits:

| tauL | 1.01e-4 | 3e-4 | 1e-3 | 1e-2 | 3e-2 |
|---|---|---|---|---|---|
| FP32 `(1-E)/A` | 2.9e-4 | 9.8e-5 | 2.8e-5 | 2.9e-6 | 9.5e-7 |
| FP32 `L*(1 - x(1/2 - x(1/6 - x/24)))` | 8.3e-8 | 8.1e-8 | 8.2e-8 | 8.1e-8 | 1.6e-7 |

Values are max relative error against a double `expm1` reference (`thin32.cpp`,
`-ffp-contract=off`).

The branch below the guard has its own error. Derived: `em * L` omits the `-tauL/2` term of
`L(1 - tauL/2 + tauL^2/6)`, so the emission contribution errs by up to `tauL/2 = 5e-5` just
under the guard. That holds in double on the CPU (`stokes_transport.h:279-293`) as well as in
FP32 on the GPU. The double `(1-e)/a` branch above the guard is clean, at about 1e-12.

The fixes:
- Both sides of the guard, I and V channels, in all three implementations: evaluate the
  4-term series. The CPU Q/U branch (`oneME`, `stokes_transport.h:330`) already carries the
  second-order term.
- GLSL: raise the guard to `tauL < 0.03`.
- CUDA and C++: `-expm1f(-tauL)/A` and `-std::expm1(-tauL)/a`.

GLSL `exp` precision is driver-defined, so this emulation is a lower bound on the error.

### M4. Compensated accumulation in FP32 RK4

Test orbit: an equatorial photon in Schwarzschild with `r_s = 1`. The acceleration
`-1.5 L^2 x/r^5` is the Cartesian Binet form. The photon starts at x = 30 with impact
parameter b and integrates 60 units of affine length.

Three runs:
- Plain FP32.
- FP32 with Kahan-compensated `state += increment`.
- The same RK4 scheme in `long double`, as reference.

Because the reference uses the same scheme, the measured error isolates roundoff. A second
reference is `long double` at `h/64` over the same length (`k2.cpp`). It bounds RK4
truncation at 4.2e-9, 6.7e-12, and 1.1e-14 for b = 3.5, and 1.1e-7, 2.1e-10, and 3.4e-13 for
b = 2.7, at h = 0.05, 0.01, and 0.002. Total error against it matches the roundoff column
to two digits in every row, so the gain holds for total position error.

    clang++ -std=c++23 -O2 -ffp-contract=off $HARNESS/kahan/k.cpp -o k && taskset -c 3 ./k

| b | h | steps | FP32 plain | FP32 Kahan | improvement |
|---|---|---|---|---|---|
| 3.5 | 0.05 | 1200 | 1.36e-6 | 9.3e-8 | 15x |
| 3.5 | 0.01 | 6000 | 1.67e-5 | 7.7e-8 | 220x |
| 3.5 | 0.002 | 30000 | 2.78e-4 | 1.65e-7 | 1700x |
| 2.7 (near b_c = 2.598) | 0.05 | 1200 | 7.2e-5 | 3.1e-6 | 23x |
| 2.7 | 0.002 | 30000 | 1.2e-3 | 2.5e-6 | 480x |

Values are relative position error.

Plain FP32 error grows with step count while Kahan error stays flat. That is the signature
of roundoff dominating truncation.

Cost:
- Measured: 1.07-1.08x on this 12-flop RHS across all six configurations in quiet runs;
  noisy reruns spread 0.7-1.9x.
- Derived: the compensated update adds 4 flops per state component, 32 for the 8-component
  Kerr state. Against a Kerr BL RHS of roughly 150-250 flops times 4 stages, that is about
  3-5%.

This targets the FP32 GLSL integrator (`maxSteps = 1000`, `raytracer.frag:61`), the CUDA
FP32 kernels, and the horizon-grazing FMA sensitivity recorded as Issue-009.

Port notes:
- Declare the compensation variables `precise` in GLSL, or the driver may reassociate
  `(t - s) - y` to zero.
- In C++, keep `-fassociative-math` off, which is Blackhole's IEEE default.

GPU A/B: not run.

### M5. Quartic root solvers (radial potential)

The test uses the Kerr critical curve at a = 0.9 (Bardeen 1973). There `R(r)` has a double
root at `r_ph`, which gives an exact referee with no external library. The simple quartics
`(r^2-1)(r^2-4)` and roots `{1,2,3,-6}` serve as a second check. numpy `roots` confirms
both.

`pathion_ellip::solve_quartic` (`quartic.rs:74-75`):
- It returns the negated roots whenever the depressed coefficient `q != 0`. The two
  quadratic constant terms are swapped: the `+sqrt(2m) w` factor needs
  `m + p/2 - q/(2 sqrt(2m))`.
- Scaled residuals reach 0.53 on all 41 critical-curve points.
- Its tests pass because every case has `q = 0` (`quartic.rs:140-209`).

`pathion_shadow_boundary` (`shadow_boundary.rs:67`):
- It uses `eta = r^2 (...)` where Bardeen has `r^3 (...)`. At a = 0.9 and `r_ph = 3`,
  `R(r_ph) = 68.6` instead of 0.
- Its a = 0 test degenerates to a single point, `r_pro = r_retro`, and passes vacuously.

Blackhole `findRadialRoots` (`analytic_kerr_geodesic.h:181-290`) has two coefficient errors
in the Ferrari resolvent:

| Line | Shipped | Correct |
|---|---|---|
| 188 | `4 c2 c0 / 3` | `8 c2 c0 / 3` |
| 207 | `alpha^2 = y1 + c2` | `alpha^2 = y1 - c2` |

Effect of the errors:
- As shipped, it returns `nReal = 0` for `(r^2-1)(r^2-4)`, for `{1,2,3,-6}`, and for every
  tested critical-curve point.
- With both lines corrected in a scratch copy (`roots/r3.cpp`, `roots/r4.cpp`), the simple
  quartics return their roots exactly. The critical-curve double root comes back as a pair
  within 1e-9 of `r_ph` at 1.8, 2.5 and 3.0, and split to 3.500000060 / 3.499999940 (6e-8)
  at 3.5: a double root perturbed by rounding splits by O(sqrt(eps)) of the coefficient
  scale, so 6e-8 is the conditioning floor, not a residual defect.
- The CUDA port already carries the 8/3 correction (`device_analytic_kerr.cuh:203-211`,
  whose comment calls 4/3 a "common mistake") and a different resolvent, so the CPU
  reference and CUDA disagree.
- No test calls `findRadialRoots` directly.

### M6. GRMHD-style block quantization

Field: a synthetic 64^3 Gaussian random field with the Kolmogorov spectrum `P(k) ~
k^-11/3`, used as `ln rho` with `sigma = 1.5`. It is not real GRMHD data. Blocks are 4^3 =
64 values.

Four methods:
- A: per-block affine min/max uniform quantization, overhead 2 x fp16 per block.
- B: TurboQuant-style rotation, `D1 H D2` after mean removal, then a 2^b-level Lloyd-Max
  Gaussian codebook scaled by block RMS, same overhead.
- C: B without the random signs.
- D: plain WHT compaction with global reverse water-filling bit allocation and no per-block
  overhead. A to C carry 0.5 bit/value more than D.

    $PYTHON $HARNESS/quant/q.py

| bits/value | A affine | B rot+LM | C no signs | D WHT alloc |
|---|---|---|---|---|
| 2 | 0.210 | 0.166 | 0.262 | 0.118 |
| 3 | 0.089 | 0.089 | 0.184 | 0.065 |
| 4 | 0.042 | 0.046 | 0.133 | 0.035 |
| 6 | 0.0099 | 0.0138 | 0.086 | 0.0114 |

Values are RMSE/sigma. fp16 direct at 16 bits scores 2.1e-4.

Findings:
- Random rotation helps only at 2 bits. It Gaussianizes, and smooth fields want
  compaction instead.
- The random signs are essential to B (compare C).
- The GPU decode for D is one 64-point inverse WHT per block: 6 stages of 32 butterflies,
  about 6 adds per value.
- 4 bits/value is an 8x cut from RGBA32F (`grmhd_streaming.h:92-99`).

Real iharm3d/KORAL data and the EHT-grade tolerance are not run.

### M7. Walsh-domain noise

White noise low-passed in the WHT (sequency < 16) domain vs the Fourier domain (bins < 8),
n = 128, 4000 trials:

| Filter | neighbor correlation inside dyadic cells | across 7/8, 15/16, 31/32, 63/64 |
|---|---|---|
| Walsh | 1.000 | about 0.00 |
| Fourier | 0.977 | 0.977 |

The WHT diagonalizes XOR-shift convolution, not translation, so the filtered noise is
piecewise constant on dyadic cells. `noise.cpp`'s per-voxel hash noise gains nothing.

### M8. open_gororoba crate tests

    CARGO_TARGET_DIR=$OUT/target cargo test --offline --locked --release \
      -p pathion_ellip -p fwht -p fixed_point_lbm -p cosmic_scheduler -p gororoba_sparse_grid -p tensor_core

All pass: exit 0, with pathion_ellip 35, fwht 5, fixed_point_lbm 8, and cosmic_scheduler
13 + 9 + 6 + 10 + 2. Sections M1 and M5 show these suites passing over the defects listed,
because every test case sidesteps the failing branch.

## Defects found (both repositories)

Blackhole:
1. `src/physics/analytic_kerr_geodesic.h:188` and `:207` -- Ferrari resolvent errors (M5).
   CPU disagrees with CUDA.
2. `src/physics/elliptic_integrals.h:78-81` and the matching R_D and R_J series -- wrong
   termination coefficients, masked by `tol = 1e-10` at a 3-8x cost (M1).
3. `shader/include/stokes_transport.glsl:82-99` and the CUDA `d_stokes` step -- FP32
   `(1-E)/A` cancellation up to 2.9e-4 (M3). The first-order Taylor branch below the guard,
   including the CPU `stokes_transport.h:279-293`, errs by `tauL/2` (derived).
4. Boost default `promote_double` in the analytic Kerr calls -- 3-8.5x cost (M2). A
   performance defect only.

open_gororoba:
1. `crates/pathion_ellip/src/quartic.rs:74-75` -- sign swap, negated roots.
2. `crates/pathion_ellip/src/shadow_boundary.rs:67` -- `r^2` for `r^3`.
3. `crates/pathion_ellip/src/diagonalizer.rs:1-6` -- the claimed diagonalization is not an
   algebra decomposition.
4. `proofs/theories/CarlsonIntegrals.v:32` -- C-993 proved from an axiom equal to its
   conclusion.
5. `crates/fixed_point_lbm/src/solver.rs:122-145` -- collision in f32, contradicting the
   crate docs.
6. `crates/gororoba_sparse_grid/src/lib.rs:165-181` -- tail mask skipped when
   `valid_bytes == len`.
7. `crates/lattice_filtration/src/topology.rs:53-70` -- returns V-E, not beta0.
8. `crates/verified_core/src/x87_math.rs:58-66` -- non-x86 fallback picks a different
   Jacobi angle branch.
9. `crates/cosmic_scheduler/src/phase_scheduler.rs:111-171` -- `enforce_timing` is never
   read.
10. `crates/gororoba_algebra/src/construction/clifford.rs:57` -- wrong Cl(3,0)
    isomorphism in the docstring.
11. `crates/surreal_algebra/src/dyadic.rs:83-91` -- silent high-bit loss in `align`.

Items 7-9 were verified by reading the cited lines. Their runtime consequence was not
executed.

## Not run

- `cargo test` for `cd_kernel`, `gororoba_algebra`, `algebra_analysis`,
  `algebra_experimental`, `lbm_3d`, `stats_core`, `spectral_core`: build time and scope.
  Their evidence here comes from reading.
- All criterion benches. Several are `black_box(2 + 2)` placeholders
  (`gororoba_engine/benches/pipeline_bench.rs`, `lbm_3d/benches/lbm_3d_bench.rs`,
  `lattice_filtration/benches/filtration_bench.rs`). Numbers quoted in docs (TurboQuant
  kvec/s, SASS cycle counts, MLUPS) stay asserted.
- Any GPU or CUDA A/B: the exact Stokes propagator in GLSL/CUDA, Kahan in GLSL `precise`,
  and WHT tile decode. The GPU cost ratios above are CPU-derived.
- `clifford_basis_product` correctness (for example `(e1 e2)^2 = -1` in Cl(0,2)).
- Real GRMHD snapshots for M6. The campaign cross-host digest is covered by
  `03-game-engine.md`.

## Ranked recommendations

1. **Fix `findRadialRoots`** (`analytic_kerr_geodesic.h:188` to `8.0 * c.c2 * c.c0 / 3.0`;
   `:207` to `y1 - c.c2`). Add a test on known-root quartics and on the Kerr critical-curve
   double root. Cost: two lines. Falsifier: on the simple quartics, any root farther than
   1e-12 from the known value; on the critical curve, a returned pair whose members lie
   farther than 1e-7 from `r_ph` or a real-root count other than four. A residual gate
   cannot serve here, because a double root's residual is quadratic in the root error.
2. **Fix the emission factor near the thin-segment guard.**
   - FP32 cancellation above the guard in GLSL and CUDA. Measured: 2.9e-4 -> 8e-8.
   - First-order Taylor truncation below the guard in the I and V channels of all three
     implementations. Derived: 5e-5.
   - Remedy: a 4-term series to `tauL < 0.03`, `expm1` where available.
   - Falsifier: the GPU-vs-double parity test at `tauL` in [1e-5, 3e-2].
3. **Replace `stokesStepFull` RK4 with the exact Lorentz-group propagator.** Use the direct
   integral form by default and the split form only for `aI ds >= 0.1`. Then port it to GLSL/CUDA to
   bring rho_Q conversion and alpha_Q/alpha_V dichroism to the GPU. Measured 1e-11 exact vs
   RK4's 181 ns to 553 us per segment at 1e-6. Falsifier: disagreement > 1e-10 with the
   mpmath 5x5 `expm` referee on the M3 case sets, which should become a CTest.
4. **Pass `policy<promote_double<false>>`** to `jacobi_sn` and `ellint_1` in
   `analytic_kerr_geodesic.h`. Measured 8.5x and 3.3x at <= 2e-15. Falsifier: the
   `analytic_geodesic_reproducibility` tolerances.
5. **Rewrite `elliptic_integrals.h` Carlson** with the 1995 stopping rule, the DLMF 19.36
   series, and the closed-form R_C before any hot path uses it. Measured 3.8x/3.0x/8.2x at
   <= 7e-16. Falsifier: the M1 mpmath referee set.
6. **Prototype Kahan-compensated RK4 accumulation** in the FP32 GLSL and CUDA integrators,
   with `precise`. Measured 15-1700x lower roundoff on CPU FP32; derived 3-5% overhead.
   Falsifier: no reduction in GPU-vs-double geodesic endpoint error at `maxSteps = 1000`.
7. **Prototype WHT-compaction tile coding** for GRMHD streaming at 4-6 bits/value on real
   iharm3d/KORAL snapshots. Measured on the synthetic field: 0.035 sigma at 4 bits, an 8x
   bandwidth cut. Falsifier: image-plane flux or EHT closure-phase error above the
   validation tolerance.
8. **Adopt the exact-integer-window rule as campaign design guidance.** Ledger quantities
   become dyadic or integer values that stay inside 2^53. Transcendentals are evaluated
   once at campaign start and stored as integers. Alongside the `-ffp-contract=off` fix
   measured in `03-game-engine.md`, this extends "same binary and host" to cross-host.
   Falsifier: a digest mismatch between two hosts on the same campaign seed.

## License

| Crate | License |
|---|---|
| `cd_kernel`, `gororoba_algebra`, `algebra_analysis`, `algebra_experimental`, `gororoba_structurable`, `lattice_filtration`, `neural_homotopy`, `verified_core`, `gororoba_engine`, `lbm_3d` | GPL-2.0-or-later |
| `pathion_ellip`, `fixed_point_lbm`, `gororoba_sparse_grid`, `cosmic_scheduler`, `surreal_algebra` | workspace, GPL-2.0-or-later |
| `spectral_core`, `tensor_core`, `stats_core`, `lbm_core` | MIT |
| `fwht` | MIT OR Apache-2.0 |

Every license is compatible with Blackhole's GPL-3.0 (`LICENSE`), because "or-later" admits
GPL-3.0. The recommended ports are reimplementations from published mathematics (DLMF,
Carlson 1995, Landi Degl'Innocenti 1985, Kahan) and carry no copied open_gororoba code.
Boost is BSL-1.0 and already a dependency.
