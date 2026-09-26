# Physics, numerics, and game-engine audit: ranked summary

Scope: Blackhole at `34e1bf1` against two targets. The first is a highly accurate,
computationally efficient black hole simulator informed by current research and by
open_gororoba's physics and numerics. The second is a game engine that couples a
Cities: Skylines-style local builder with a Stellaris-style interstellar layer, where
civilizations interact under time dilation in the Interstellar (Thorne 2014; James et al.
2015) setting. Five reports carry the evidence:

| Report | Subject |
| --- | --- |
| [01-renderer-accuracy.md](01-renderer-accuracy.md) | GLSL/CUDA/CPU ray tracing and disk physics vs 2024-26 literature |
| [02-open-gororoba-crossref.md](02-open-gororoba-crossref.md) | Numeric cross-check of shared physics, lineage, crate triage |
| [03-game-engine.md](03-game-engine.md) | Game clocks, Interstellar canon, gap map, engine architecture |
| [04-engineering-baseline.md](04-engineering-baseline.md) | Tests, CI, static gates, hygiene |
| [05-open-gororoba-novel-numerics.md](05-open-gororoba-novel-numerics.md) | Algebra and numerics concepts explained, mapped to Blackhole hot paths, measured |

Every numeric verdict comes from an independent referee (mpmath at 50 digits written from
the textbook metric, numpy, or a C++/Rust driver; all kept in `harness/`). Agreement between Blackhole and
open_gororoba counts for nothing on the modules gr_core ported from Blackhole in 2026-02
(02, "Lineage finding"): one source counted twice. Findings marked MECHANISM RE-VERIFIED
had their algebra and code path re-derived a second time outside the reporting agent; the
quantitative consequences (shadow widths, ray counts) rest on that agent's scratch ports.

## P0 -- the Kerr renderer does not trace Kerr null geodesics

1. **Carter potentials use two conventions at once** (01 F1, MECHANISM RE-VERIFIED).
   `shader/include/kerr.glsl:176-177` writes Theta = Q + a^2 cos^2 - Lz^2/sin^2, so the
   initializer's Q equals Carter's Q + Lz^2. `kerr.glsl:175` then builds
   R = A^2 - Delta (Q + (Lz - a)^2) with Carter's form, which over-subtracts Delta Lz^2. The
   same pair lives in `src/cuda/device_physics.cuh:390,481,484` and `src/physics/kerr.cpp:91`.
   The reporting agent measures the shadow at a != 0 at 0.67-0.69x the correct width, with
   a 32% jump between a = 0 (Schwarzschild RK4 branch) and a = 0.01. `roadmap.md:451` and
   `lacunae.md:529` record this path as exact. Falsifier: a ray at b = 1.001 b_c(a) escapes
   and one at 0.999 b_c is captured, with b_c from Bardeen's closed-form critical curve or
   the mpmath referee -- not from `analytic_kerr_geodesic.h`, whose quartic solver is
   broken (item 10).
2. **The Mino step freezes at radial turning points** (01 F2, 02 F6, MECHANISM
   RE-VERIFIED). `kerr.glsl:180-190` flips `sign_r` when R < 0 but steps with
   `sqrt(max(R, 0))`, so r stops changing once a step overshoots. The reporting agent finds
   every deflected equatorial ray ending at max-steps. The fix is the second-order form
   d^2r/dlambda^2 = R'(r)/2 (gr_core `kerr.rs` uses it with u = 1/r and DOPRI5). Measured in
   scratch on the CPU tracer: the stalled b = 1.001 b_c ray turns at r = 1.58524 and
   escapes, at 91 ns/step against 145 ns/step.
3. **The image shows spin -a** (01 F3). The tracer integrates the future-directed ray the
   camera would emit instead of the past-directed photon arriving along -dir. Time reversal
   t -> -t maps Kerr with spin a to Kerr with spin -a, so tracing the emitted ray images the
   mirrored hole (code b = +4.0M for a physical -4.0M). The docs' "outgoing" KS form is the
   ingoing one. Fix together with item 2.
4. **The default desktop view is a Schwarzschild-only beauty tracer** (01 F4, tracked in
   issues #14/#15). The spin slider changes tint only.

## P0 -- the accretion disk is Newtonian

5. **"Page & Thorne" flux is the Newtonian profile** (01 F6, 02 F1). The default emissivity
   LUT (`scripts/generate_luts.py:44-46`) peaks at 1.365 r_isco on its 256-point grid (the
   continuous Newtonian peak is 49/36 = 1.361); Page-Thorne peaks at 9.55M = 1.592 r_isco
   at a = 0 (normalized shape off by up to 0.40). The Kerr LUT uses an invented
   formula (`thin_disk.h:243-270`). Fix: the closed-form Page-Thorne flux with the cubic roots
   x_k = 2cos(acos(a)/3 -+ pi/3), -2cos(acos(a)/3); falsifier: agreement with quadrature to
   1e-6 and continuous peaks at 1.592/1.563/1.483/1.278 r_isco for a = 0/0.5/0.9/0.998
   (mpmath quadrature of the Page-Thorne integral; the LUT grid rounds them to
   1.588/1.565/1.482/1.282).
6. **No render path applies a g-factor; the redshift LUT models a static emitter** (01 F5,
   02 F2). At a = 0 the LUT's ISCO value is z = 0.225 against 0.414 for the orbiting
   emitter; at a = 0.998, 53 of 256 entries read zero where z = 9.79. Fix:
   g = 1 / (u^t (1 - Omega lambda)) with u^t from Bardeen-Press-Teukolsky 1972. Interstellar
   dropped Doppler shifts on purpose (arXiv:1502.03808 sec. 4); that look belongs behind a
   labeled toggle.
7. **`kerrDiskGFactor` drops (1 + a r^-3/2)** (01 F7, 02 F11, 03, MECHANISM RE-VERIFIED).
   `src/physics/iron_kline.h:103-108` divides sqrt(f) by the Doppler term only, so it
   agrees with the no-bending Schwarzschild limit at a = 0 and diverges with spin: 1.73x
   too high at the a = 0.998 ISCO, 0.465 against 0.371 at a = 0.9. It also omits light
   bending, so it is not the Laor 1991 transfer function its docstring names.

## P1 -- library physics labeled verified or complete that is wrong

8. **Kerr-Newman ISCO moves the wrong way** (02 F4, RE-VERIFIED numerically).
   `src/physics/verified/kerr_newman.hpp:342-353` adds +Q^2/(2M^2) to the Kerr ISCO: 6.405
   at a = 0, Q = 0.9, where the Reissner-Nordstrom cubic r^3 - 6r^2 + 9Q^2 r - 4Q^4 = 0
   gives 4.514. `g_tphi` and omega drop the Q^2 term. The Rocq source
   (`rocq/theories/Metrics/KerrNewman.v:70,191-201`) carries the same definitions and its
   reduction theorems end in `Admitted.`, so "verified" certifies transcription, not physics.
9. **Kerr-de Sitter is not the Carter metric** (02 F5). Delta is quadratic, so no
   cosmological horizon exists, and g_tt has the wrong sign at a = 0. Falsifier: SdS
   horizons (2.027794, 16.217355) at a = 0, Lambda = 1e-2.
10. **Analytic Kerr quartic solver has two Ferrari errors** (05 M5, RE-VERIFIED by
    derivation). `src/physics/analytic_kerr_geodesic.h:188` uses 4/3 where the depressed
    resolvent needs 8/3 c2 c0; `:207` uses alpha^2 = y1 + c2 where x^4 + c2 x^2 + c1 x + c0
    needs y1 - c2. It returns no real roots for (r^2-1)(r^2-4) and on the Kerr critical
    curve. The CUDA port already carries 8/3, so CPU and CUDA disagree.
11. **"Energy-conserving" null correction zeroes v^r** (02 F7).
    `verified/energy_conserving_geodesic.hpp:228-240` turns a photon with 1e-6 drift into a
    timelike vector (norm -1.16). gr_core's additive correction (`energy_conserving.rs:242-280`,
    about 10 lines, same author) holds the norm at 3.6e-15. This is the one direct port.
12. **Smaller defects**: `NovikovThorneDisk` temperature 100x high (`novikov_thorne.h:118`,
    since `820e2ff`; gr_core fixed it); `kerrTimeDilation` is the static-observer rate and
    NaN inside the ergoregion, `kerrRedshift` +inf there (01 F10); disk Doppler velocity
    evaluates to 1.78c before the 0.99c clamp at a = 0.998, r = 1.5 (02 F11); ISCO and photon-orbit functions disagree on
    the sign convention for a < 0 (02 F13); GPU "RTE" and "Stokes IQUV" are shading models
    without covariant transport (01 F8); `lacunae.md` misattributes four citations (01 F12).
13. **Tests that restate the implementation survive `ea2eb1a`** (01 F14).
    `novikov_thorne_test` asserts the hard-coded 1.5 r_isco; `radiative_transfer_test` tests a
    local reimplementation, not `rte_integrator.h`; no test constrains R, the capture radius,
    or escape. All 23 physics CTest entries pass, which is itself the finding.

## open_gororoba: the concepts, and what each buys Blackhole

open_gororoba led in four places that make Blackhole's physics cheaper, more accurate, or
both, each measured in 02 or 05:

- **Second-order Mino stepping with u = 1/r** (gr_core `kerr.rs`). Integrating
  d^2r/dlambda^2 = R'(r)/2 instead of dr/dlambda = +-sqrt(R) carries rays through turning
  points with no sign bookkeeping, and u = 1/r compresses the far field so fewer steps
  reach the sky. It fixes P0 item 2 and ran 1.6x faster per step (91 vs 145 ns).
- **Additive null-norm projection** (gr_core `energy_conserving.rs:242-280`). Rescaling
  only the spatial momentum to restore g(k, k) = 0 holds the norm at 3.6e-15 for 11%
  per-step cost, and it lets the integrator take longer steps without drifting off the
  light cone. It replaces Blackhole's projection, which destroys radial motion (item 11).
- **Precision tiers** (`algebra_analysis` precision_policy). The rule is to spend
  precision where the error accumulates, not everywhere. x87 accumulation of up to 2048 terms
  stays within one final double rounding (`N 2^-64 <= 2^-53`); longer sums need Kahan
  compensation. For Blackhole, the M2 measurement alone says Boost.Math should stop
  promoting doubles to x87 80-bit: the unpromoted `jacobi_sn` and `ellint_1` land within
  2e-15 of the promoted results, so promotion buys nothing at 8.5x and 3.3x cost. FP32 GPU RK4
  should compensate its state accumulation (position error 15x lower at 1200 steps and
  1700x lower at 30000, for about 3-5% cost).
- **The Lorentz structure of polarized transfer** (quaternion/Clifford theorems C-876,
  C-911, C-912). The Stokes propagation matrix minus its trace generates a Lorentz
  transformation: dichroism is a boost, Faraday rotation is a rotation, and so(1,3) is the
  complexified quaternion algebra. Writing w = eta + i rho, the eigenvalues follow from one
  complex square root of w.w = |eta|^2 - |rho|^2 + 2i eta.rho, which replaces a 4x4 matrix
  exponential or many RK4 substeps with one closed-form step. Measured: 1e-11 against a
  50-digit referee in every regime, at 190-250 ns per segment against RK4's 181 ns at
  Faraday depth 1 and 553 us at depth 1000. The propagator itself is Landi Degl'Innocenti
  (1985), as in ipole; open_gororoba supplies the framing and the proved identities.

Every concept examined, in plain language, with its verdict (05 carries the math and file
lines):

| Concept | What it is | Blackhole hot path | Measured or derived result | Verdict |
| --- | --- | --- | --- | --- |
| N3 quaternion/Clifford rotations | Sandwich q v q* equals the rotation matrix, preserves norm, composes by product (proved) | Polarized transfer (`stokes_transport.h`, GPU Stokes) | Closed-form Lorentz propagator above | ADOPT (reimplement) |
| N4 precision tiers | Error grows as N u; Kahan keeps it near 2u; x87 shrinks u by 2^11 | Boost elliptic calls; FP32 RK4 state | 8.5x/3.3x faster elliptic; 15-1700x lower FP32 drift | ADOPT policy; PROTOTYPE GPU Kahan |
| N6 Carlson duplication | Elliptic integrals by repeated argument halving, then a short series | `elliptic_integrals.h` R_F/R_D/R_J | Carlson 1995 stopping rule: 3.8x/3.0x/8.2x faster at <= 7e-16; Blackhole's series coefficients are wrong, masked by tol = 1e-10 | ADOPT when Carlson reaches a hot path. The "32D pathion" wrapper is 16 independent complex evaluations; the pairing is not a subalgebra, so the algebra adds nothing |
| Series stress test (from N4) | Taylor-expand (1-E)/A where FP32 cancels | GPU Stokes/RTE emission factor near `tauL < 1e-4` | 2.9e-4 FP32 error above the guard; 4-term series holds 8e-8 to tauL = 0.03 | ADOPT |
| N7 random rotation + Lloyd-Max (`fwht`) | Random signs, fast Walsh-Hadamard, random signs make block values near-Gaussian, so one codebook fits all | GRMHD tile streaming | Plain WHT compaction with bit allocation: about 8x below RGBA32F at 2-4 bits/value on a synthetic Kolmogorov field; the rotation wins only at 2 bits | PROTOTYPE on real GRMHD dumps |
| N5 exact-integer windows (C-1736), dyadic rationals | A float sum or product is order-, FMA-, and host-independent when every intermediate is an integer that fits the significand | Game determinism across hosts and compilers (item 19) | Design guidance; proved bound | PROTOTYPE as a dyadic/fixed-point ledger |
| N1 XOR basis rule (C-1142) | In a Cayley-Dickson algebra e_i e_j = +-e_(i XOR j), so multiplication by a fixed element is a signed matrix tensor cores can run | None: no Blackhole path multiplies in an algebra of dimension >= 8 | -- | NOT-APPLICABLE: the non-associative levels cannot carry the chain rule or compose propagators |
| N2 Cariow Hadamard factorization (C-1646) | A 16-point Hadamard transform nearly diagonalizes the sedenion product: 122 multiplies instead of 256 | None, same reason | Proved and tested in open_gororoba | NOT-APPLICABLE to Blackhole; a real win for open_gororoba's own sedenion work |
| N8 even/odd IDCT butterfly (C-1735) | 8-point inverse DCT in 32 multiplies | None | Loeffler-Ligtenberg-Moschytz (1989) needs 11 | NOT-APPLICABLE |
| Walsh-domain noise | Noise synthesized in the Walsh basis | Procedural noise | Blocky: neighbor correlation 1.000 inside dyadic cells, 0.000 across | NOT-APPLICABLE |
| `sedenion_geodesic`, `chingon_frame_dragging`, `cd_ladder_force` | Algebra-driven replacements or additions to the geodesic RHS | Geodesic RHS | `sedenion_geodesic` leaves v_r at exactly -0.1 for 1000 steps at a = 0 (no gravity); the others add terms that break Killing conservation or inherit the KN error | NOT-APPLICABLE to the accuracy path; at most a labeled alternative metric |
| `cosmic_scheduler`, TT-cross, `spectral_core`, `lattice_filtration`, `neural_homotopy`, `gororoba_engine` | Scheduling, low-rank tensors, spectral and topological tools | Taskflow scheduling; LUT generation | No path where they beat what Blackhole runs (05 lists each reason) | NOT-APPLICABLE |
| Photon-ring Lyapunov exponent | Rate at which nearby photon-ring orbits diverge; sets subring brightness ratios | Photon-ring and anti-aliasing budget | Closed form exists (Johnson et al. 2020); gr_core `lyapunov.rs` is a generic accumulator | Implement the closed form |
| Claims registry with falsifiers | 1572 claims, each with status and falsifier | Validation docs | Process, not code; C-993 shows "kernel_checked" proves nothing when an axiom restates the conclusion | ADOPT as process |

open_gororoba defects that surfaced along the way (report upstream): `pathion_ellip`
`solve_quartic` negates roots (`quartic.rs:74-75`) and its shadow boundary uses r^2 for r^3
(`shadow_boundary.rs:67`); gr_core's null integrator uses the timelike polar potential
(`kerr.rs:204,269,342`), its TaylorF2 phase lacks 1/eta (`gravitational_waves.rs:230`), and
its synchrotron F(x) "fit" is off 2.4x at x = 1 (Blackhole carries the same polynomial
in `shader/include/synchrotron_emission.glsl:47-70`, and a CUDA G(x) fallback at
`device_physics.cuh:1063-1065` gives 0.797 against K_{2/3}(1) = 0.4945 whenever the G
LUT is absent); `lattice_filtration` computes beta0 - beta1;
`fixed_point_lbm` runs its collision in f32; several criterion benches time `2 + 2`.
`grmhd_core` is a real finite-volume solver with real CUDA, CubeCL, and Vulkan kernels but
has no shock-tube or Bondi test and declares itself non-production; it does not replace
iharm3d/KORAL/BHAC ingestion. `gororoba_optix` and `gororoba_gpu_cubecl` are wrappers
without kernels. All licenses are GPL-2.0-or-later, MIT, or MIT/Apache, compatible with
Blackhole's GPL-3.0; the recommended ports reimplement published math.

## Game engine: Interstellar fidelity and the missing layers

14. **Every entity carries the ZAMO (hovering) clock; planets orbit** (03 F3, RE-VERIFIED
    numerically). At r = 6M, a = 0.9: ZAMO 0.818, prograde circular orbit 0.743, retrograde
    0.655. Band 0 (1.7M) lies inside the marginally bound radius (1.732M), so no bound orbit
    exists there. Fix: observer-typed entities (orbiting colony, hovering station, fleet in
    transit).
15. **Miller's planet is unrepresentable** (03 F4, RE-VERIFIED numerically). The 0.998 spin
    clamp caps orbital dilation at 10.8x. 61,000x needs 1 - a = 1.33e-14 with the prograde
    ISCO at 1 + 3.76e-5 M (mpmath: 61,403x at 1 - a = 1.33e-14; 03 quotes 61,362x at the
    unrounded 1 - a = 1.3327e-14 from arXiv:1601.02897). Spin must be stored as delta = 1 - a;
    `1 - a*a` keeps two significant digits in a double at that spin. The film rendered
    a = 0.6 for visuals (arXiv:1502.03808), so the game needs a declared canon (03, canon
    options table).
16. **Dilation cancels out of the yield rate** (03 F5). Yield divides by dtau/dt, so with
    wear disabled, output per turn is identical across bands (68,242-69,264; spread is report
    latency). Wear, hazard, and containment accrue per proper day, so per outside turn a deep
    fleet outside the ergoregion ages more slowly and holds its reliability-scaled yield
    longer (the campaign's 0.9 corruption threshold arrives after 50/rate busy turns). Deep
    time has no scarcity mechanic; its clock consequences are latency and per-proper-day
    wear.
17. **Causality leaks** (03 F1, F2, F8). Unlinked systems exchange intel with zero delay
    (latent until a third system exists); same-system intel skips the radial leg (2 turns
    against 153.8); authorities see their own remote fleets instantly; one faction's win
    sets a global `decided_` latch that refuses every faction's orders for the rest of
    the campaign.
18. **The locked balance shape comes from harness cadence** (03 F6). Re-tasking every turn
    instead of every 30 flips solo and pod from Lost to Won. The invariant test pins one
    cadence and one rival; no balance claim stands without a cadence and rival sweep.
19. **Determinism digest depends on `-march=native` through FMA contraction** (03 F7):
    native 4501c3.. vs generic ddec60..; `-ffp-contract=off` restores it. The printed values
    are identical, so the digest guards bits, not behavior.
20. **The vision's local layer does not exist.** No grid, zoning, networks, cohorts,
    services, traffic, diplomacy, tech tree, events, versioned save, data-driven content,
    ECS layout, simulation LOD, or constellation UI (03 gap map). Crews in transit age at
    the coordinate rate (no special-relativity factor); signal delay ignores azimuth.

Recommended architecture (03 section 9): L0 physics oracle consulted at load and orbital
epochs, quantized into the save; L1 colony city sim ticking in proper time through an
integer fixed-point accumulator (`rateQ = round(dtau/dt * 2^32)`; canon Miller runs one
local hour per 2,557 one-day turns); L2 per-system region with its own integer turn and
event queue; L3 interstellar belief-state diplomacy over a light-delay path matrix, whose
minimum edge delay is the lookahead of a conservative parallel discrete-event simulation.
Focusing a colony sets the outside clock rate, so the film's "23 years of messages" becomes
a mechanic.

## Engineering baseline

21. **10 of 93 local tests fail from one cause** (04 #1). `.conan/p/` holds only its index
    database; binaries in `build/Release` (configured 2026-07-19, 24 commits behind HEAD)
    carry RUNPATHs into deleted package folders. No failure is an assertion failure.
22. **CI covers GCC 14 only** (04 #3). It never builds CUDA, never compiles with clang
    (the local compiler), and never runs ASan/UBSan/TSan, coverage, fuzzing, or IWYU;
    `docs/developer-guide/ci.md` discloses this accurately.
23. **The benchmark regression gate cannot produce a result** (04 #4): not wired to CI, no
    committed baseline, and its binary path does not match the `riced` preset.
24. **Five meta-tests share the build tree without `RESOURCE_LOCK`** (04 #7), so
    `ctest -j > 1` on a stale tree reconfigures and races itself.

## Order of work

1. Fix the Ferrari quartic, then Carter potentials, second-order Mino stepping, and
   arriving-photon direction in GLSL, CUDA, and `kerr.cpp` together; gate capture edges
   against Bardeen's critical curve and add potential-consistency and escape tests.
2. Page-Thorne closed-form flux, orbiting-emitter g-factor, `kerrDiskGFactor` fix; regenerate
   LUTs; add an Interstellar no-Doppler toggle.
3. Kerr-Newman, Kerr-de Sitter, NovikovThorneDisk units, additive null-norm correction;
   correct the Rocq definitions so generated code follows; replace tautological tests.
4. Numerics adoptions: exact Stokes propagator, `promote_double<false>`, emission-factor
   series, Carlson stopping rule; GPU A/B for Kahan-compensated RK4.
5. Game: observer-typed clocks with delta-parameterized spin, causality fixes, cadence-swept
   balance invariants, `-ffp-contract=off` on campaign targets, then the L1 local layer and
   a versioned save.
6. CI: clang lane, sanitizer lane, `RESOURCE_LOCK` on meta-tests, rebuild the Conan cache.

## Decisions for the owner

1. Spin canon: physics canon (1 - a = 1.33e-14, 61,000x Miller) for Gargantua with graded
   presets elsewhere and a = 0.6 as the rendered spin, disclosed in the UI (recommended);
   or one spin for both render and clocks.
2. Disk look: physically Doppler-beamed disk by default with Interstellar's no-Doppler look
   as a toggle (recommended), or the reverse.
3. Local-layer clock: the focused colony at wall-clock proper time with all others advanced
   through the integer accumulator (recommended), or pure turns everywhere.
4. Whether the audit lands as a docs PR and whether the P0 renderer fixes start next.

## Not run

GPU pixel captures of the rendered shadow (no offscreen harness exists); GPU A/B for Kahan
compensation and the exact Stokes propagator; real GRMHD data for Walsh compaction; a clean
rebuild at HEAD in the primary checkout; `physics_bench`; cross-platform digest comparison;
the cosmology/TOV cross-check against `cosmology_core`; Endurance, Mann, and Edmunds orbital
numbers (no fetched source states them). Each report lists its own not-run items with
reasons.
