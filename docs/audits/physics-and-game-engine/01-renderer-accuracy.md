# Renderer and Physics-Library Accuracy Audit

Scope: the renderer (default fragment, interop fragment, GL compute, CUDA) and
`src/physics/`, judged against the goal "a highly accurate black hole simulator based on the
latest research, with physics performance enhancements". Source baseline: `main` at
`34e1bf1` (2026-09-22). The test binaries under `build/Release` date from 2026-07-19..23 and
predate `a4e1f1d`. Each numeric cross-check below ports the current source text line by line
into Python, so the findings bind to `34e1bf1` and not to the stale binaries. The
scripts (`checks.py`, `rcheck.py`, `shadow.py`, `shadow2.py`) and their expected output live
in `harness/` (`harness/README.md`); section 5 states their method.

Tags: **NEW** means no repo doc or issue names the defect. **TRACKED** carries a doc or
issue pointer. **TRACKED-BUT-WRONG** means a repo doc asserts the opposite of what the
source does.

## Summary

The Kerr ray tracer shipped in both GLSL and CUDA does not integrate Kerr null geodesics.
Three defects compound in `kerrStep`/`d_kerr_step`:

1. The Theta potential uses `Lz^2/sin^2` where Carter's separation has `Lz^2 cot^2`. The
   initializer then picks Q to satisfy that Theta, which leaves the radial potential short
   by `Delta*Lz^2`.
2. The traced ray is the future-directed ray the camera would emit, so the image is the
   image of spin `-a`.
3. The forward-Euler Mino step freezes permanently at every radial turning point, so no
   deflected ray ever reaches the escape test.

At `a = 0` the same code switches to a correct Schwarzschild RK4 tracer, so the rendered
shadow width drops by 32% between `a = 0` and `a = 0.01`.

The default desktop path is a separate beauty tracer that handles only Schwarzschild. Its
spin slider changes artistic tinting and nothing else. No render path applies a relativistic
disk transfer function (a `g`-factor). The "Novikov-Thorne" profile in every render path is
the Newtonian Shakura-Sunyaev profile. The "complete" RTE, Stokes, and Fe K-alpha claims
describe formula-level code. Their tests check analytic flat-slab limits or qualitative
properties, and none reproduces a published GRRT benchmark.

All 23 physics-relevant CTest entries pass (`ctest -R
"kerr|analytic|eht|iron|stokes|rte|radiative|novikov|doppler|gpu_cpu|glsl_parity|cuda_device|cuda_geodesic"`,
23/23, RTX 4070 Ti present). That pass is itself a finding. Four CUDA tests drive the Kerr
kernel with nonzero spin (`cuda_device_physics_test.cu:205` spin 0.9,
`cuda_variants_test.cu:46` spin 0.6, `cuda_stokes_test.cu:90`, `cuda_rte_test.cu:57`), but
they assert only a black center pixel, agreement between kernel variants that share one
implementation, and nonzero output. No assertion constrains the radial potential, the
capture radius, or escape, and no test measures rendered geometry.

## 1. Ranked findings

### F1. Kerr Theta/Q convention makes the GPU radial potential wrong by `Delta*Lz^2` -- CRITICAL

Tag: **TRACKED-BUT-WRONG**. `docs/developer-guide/roadmap.md:451` and
`docs/physics/lacunae.md:529` mark "Exact Kerr Carter constants" COMPLETE with "70/70
tests".

Sites:
- `shader/include/kerr.glsl:132` (`c.Q = ptheta^2 - a^2 cos^2 + Lz^2/sin2`), `:175` (R), and
  `:176-177` (Theta).
- `src/cuda/device_physics.cuh:390`, `:481`, and `:484`, which are the same code.
- `src/physics/kerr.cpp:84` and `:91`. The CPU pair is inconsistent in the opposite
  direction: R is standard and Theta is non-standard.

Observed:
- Carter's separation has `Theta(theta) = Q + a^2 E^2 cos^2 - Lz^2 cot^2` and `R =
  (E(r^2+a^2) - a Lz)^2 - Delta (Q + (Lz - aE)^2)`. See Gralla and Lupsasca, "The Null
  Geodesics of the Kerr Exterior", PRD 101, 044032 (2020), arXiv:1910.12881. The repo's own
  oracle `src/physics/analytic_kerr_geodesic.h:110-120` (`radialPotential`) also uses this
  standard R.
- All three code paths write `Lz^2/sin^2` in Theta. Because `Lz^2/sin^2 = Lz^2 cot^2 +
  Lz^2`, the GPU initializer's `Q_code = Q_std + Lz^2`. The unchanged R formula then
  evaluates `R_std - Delta*Lz^2`.
- A port of `kerrInitConsts` shows that Theta matches `(Sigma k^theta/E)^2` exactly while R
  does not. For a generic ray at `(15,3,4)` with a = 0.9, `R_code = 41958` against a true
  value of `51139`. For a tangential ray at r = 20, `R_code = -1.59e5` against a true value
  of 0.
- The docstring at `kerr.glsl:63` states that the tangential ray "gives R <= 0, correctly
  anchoring the ray at its turning point". That sentence records the defect as if it were a
  feature, because the true value is exactly 0.

Measured (equatorial scan, camera at r = 15M, `r_s = 2`, the renderer's own
pixel-to-constants mapping, capture edges in tan-angle units). The reference column reuses
that same Euclidean, non-tetrad pixel-to-constants mapping (`harness/shadow2.py`'s
`exact_capture`, called on the same `pix(y)` the shipped column uses) with the standard
`R`, so the table is a same-camera isolation of F1's Theta/Q convention error, not a
physical angular width; a physical-size comparison needs F9's observer-tetrad mapping:

| a | shipped edges | width | R_std width (same camera) | ratio |
| --- | --- | --- | --- | --- |
| 0.01 | (-0.252, +0.251) | 0.503 | 0.732 | 0.687 |
| 0.5 | (-0.278, +0.215) | 0.493 | 0.722 | 0.683 |
| 0.9 | (-0.295, +0.170) | 0.464 | 0.688 | 0.674 |
| 0.99 | (-0.298, +0.148) | 0.446 | 0.659 | 0.676 |

Note: F9's falsifier gives a physical, static-observer half-width of 0.3407 at r = 15M in
the a -> 0 limit, a total width of 0.6814. Comparing the a = 0.01 shipped width to that
value instead of the same-camera reference above gives a ratio of 0.503/0.6814 = 0.738, not
0.687. The two references disagree because the same-camera column still carries F9's
coordinate-to-angle error; the 0.674-0.687x figures above isolate F1 at fixed camera model,
they do not state the renderer's physical size error.

The a = 0 branch uses `bhStepRK4` with the exact Schwarzschild `-1.5 r_s h^2 x / r^5` form,
which gives a width of 0.739. The rendered horizontal shadow width therefore drops from
0.739 to 0.503 when the spin slider moves from 0 to 0.01.

Inferred: the error scales as `Lz^2`, and rays in the vertical plane through the camera have
`Lz = 0`. The vertical extent is therefore close to correct and the horizontal extent is
about 0.68x, so every Kerr shadow the GPU renders is oblate. Confidence is high. A vertical
scan with theta stepping would confirm it (not run).

Why it matters: the critical curve is the observable the EHT and BHEX target. A 32% size
error and an aspect-ratio error rule out any claim of quantitative accuracy for the Kerr
path.

Fix:
1. Write Theta with `Lz^2 cot^2` in `kerr.glsl`, `device_physics.cuh`, and `kerr.cpp`.
2. Initialize `Q = p_theta^2 - a^2 cos^2 + Lz^2 cot^2`.
3. Derive the GLSL/CUDA potentials from one table, following the X-macro pattern of
   `interop_uniform_registry.h`.
4. Add a regression test that is independent of camera convention: for random positions,
   directions, and spins, assert `R(r0) == (Sigma k^r/E)^2` and `Theta(theta0) == (Sigma
   k^theta/E)^2` to 1e-5 relative, on CPU and through the CUDA kernel.

Falsifier: evaluate `kerrInitConsts` followed by `R` on the GPU for a tangential equatorial
ray. A result of 0, rather than `-Delta*Lz^2`, disproves F1.

### F2. The forward-Euler Mino step freezes at every turning point, so deflected Kerr rays never escape -- CRITICAL

Tag: **NEW** as a cause. Issue #21 tracks the symptom (max-step exhaustion counted as
escape) without naming this mechanism.

Sites:
- `shader/include/kerr.glsl:180-189` and `:229`.
- `src/cuda/device_physics.cuh:486-492` and `:525`.

Observed:
- `if (R < 0) sign_r *= -1` is followed by `dr = sign_r*sqrt(max(R,0))`.
- A first-order step overshoots the turning point into `R < 0`. There `dr = 0`, so r does
  not change and R stays negative. The sign then flips again on every later step while r
  stays frozen and phi keeps advancing.
- Theta behaves the same way at theta turning points.

Measured (port of the shipped scheme, a = 0.5 and 0.9, 961 equatorial pixels): every ray
that is not captured ends at `maxSteps`, and none reaches `r > maxDistance`.

| a | shipped | Q-fixed |
| --- | --- | --- |
| 0.5 | 763 maxsteps / 198 capture | 672 maxsteps / 289 capture |
| 0.9 | 776 maxsteps / 185 capture | 686 maxsteps / 275 capture |

The escape direction then comes from `normalize(hitPoint - oldPos)` on the frozen step. That
direction is tangent to the periapsis circle. For weak lensing it approximates half the true
deflection, not the full deflection.

Inferred: the Kerr background lensing, the Einstein ring, and the secondary images are all
wrong. The picture still looks plausible because the frozen tangent points roughly in the
right direction. Confidence is high: the mechanism is exact in both source files.

Fix: stop stepping `sqrt(R)` with sign flips. Use one of these:
- The second-order Mino form `d^2r/dlambda^2 = R'(r)/2` and `d^2theta/dlambda^2 =
  Theta'(theta)/2` with RK4 or RKF45. `kerr.cpp` already computes `dRdr` and `dThetadtheta`.
- The Hamiltonian form in Kerr-Schild Cartesian coordinates, as in GRay2 (Chan et al.,
  arXiv:1706.07062).
- The closed-form elliptic solution (Gralla and Lupsasca 2020). The repo holds only
  radial prototypes of it, and they cannot replace the tracer as they stand:
  - `analytic_kerr_geodesic.h` implements `rAnalytic` alone, which returns -1 unless
    `findRadialRoots` reports four real roots (`:315-319`); that root finder is broken
    (`05-open-gororoba-novel-numerics.md` M5).
  - Neither header evolves theta, phi, or t analytically.
  - The CPU and CUDA radial Mobius formulas differ (`analytic_kerr_geodesic.h:344-345`
    uses `r1 - r4` and `r1 - r3`; `device_analytic_kerr.cuh:360-365` uses `r2 - r4` and
    `r2 - r3`).
  - No render kernel includes the CUDA header; only `tests/cuda_analytic_kerr_test.cu` does.
  A closed-form renderer needs the fixed root finder, every root-class branch, the
  theta/phi/t integrals, and one agreed Mobius form first.

Falsifier: render with spin 0.5 and the `BH_DEBUG_FLAG_MAXSTEPS` display enabled. If most
non-captured pixels do not carry the flag, F2 is wrong.

### F3. The Kerr tracer images spin `-a`: the ray is the camera-emitted future-directed geodesic -- HIGH

Tag: **NEW**. Issue #16 section C asks for a prograde/retrograde orientation test but does
not identify this defect.

Sites: `shader/include/kerr.glsl` (`kerrInitConsts`, the future root `kt > 0` taken with
spatial part `+dir`, and `kerrInitRay` with `sign_r = sign(dir . e_r)`), and
`src/cuda/device_physics.cuh:322`.

Observed:
- For a camera on +x looking along -x with a pixel offset in +y, the port gives code `b =
  Lz/E = +3.998 M`. The photon that actually arrives along `-dir` has `b = -4.000 M`.
- `R` is invariant under `(E,Lz) -> (-E,-Lz)` but not under `Lz -> -Lz`. The code's `(1,
  +b)` therefore has the radial potential of the physical ray in spin `-a`.
- With F1 corrected in the port, the code-convention capture edges at a = 0.9 are (-0.487,
  +0.201), while the physical edges are (-0.201, +0.487). They are mirror images.

Why it matters:
- The flattened (prograde) edge of the shadow lands on the wrong side relative to the spin
  sign and to any disk beaming computed from the spin.
- A Kerr movie or comparison image is labeled with the wrong handedness.

Fix: take the constants from the arriving photon, `p ~ -dir` with `E > 0`, and integrate the
Mino equations with decreasing `lambda`. This is DNGR's procedure: "the direction -n of the
incoming ray" in the camera's FIDO frame (James, von Tunzelmann, Franklin, Thorne, CQG 32
065001, arXiv:1502.03808, Appendix A.1).

This fix changes which Kerr-Schild branch is regular. The current `(A + dr)/Delta` form at
`kerr.glsl:216-219` is the ingoing-KS form. That is the correct form for the future-directed
rays the code traces today, and it becomes the wrong one once the rays are past-directed, as
F12 explains. Apply F1 first, then the direction fix, then re-measure.

Falsifier: place a prograde disk with physical `g`-factor beaming (F5 fix) in the scene. The
flattened shadow edge must fall on the approaching, brighter side. F3 is a world-frame
defect: `interop_raygen.glsl:11` negates `uv.x`, so which screen side appears flattened also
depends on the camera basis. The fix therefore needs an orientation test in world
coordinates (sign of `Lz` for a known pixel), not a visual check.

### F4. The default desktop image comes from a Schwarzschild-only beauty tracer with fixed first-order steps -- HIGH

Tag: **TRACKED**. Issues #14 and #15 ("legacy fixed-loop beauty tracer, `STEP_SIZE = 0.1`,
`300` iterations"). Debt-ledger PHYS-1 covers only the separate
`integrator.glsl`/`raytracer.frag` Schwarzschild fallback. The discontinuity with the Kerr
path, measured below, is **NEW**.

Sites: `shader/blackhole_main.frag:401`, `:416`, `:432-436`, `:442`, `:149`, `:518`, and
`:680-734`. `src/render/render_state.h:186` (`kerrSpin = 0`) and `:314`
(`useComputeRaytracer = false`). `src/main.cpp:749-751`.

Observed at launch (`Blackhole`, `BlackholeGLSL`):
- `traceColor` integrates the Schwarzschild Binet form with a semi-implicit Euler step (`dir
  += acc; pos += dir`) of fixed length 0.1 over 300 iterations.
- Capture is tested at `r < r_s` regardless of spin.
- The disk inner edge is fixed at `3 r_s` by the macro at `:149`.
- `kerrSpin` reaches only shading: `diskDopplerBoost` (`:326`), the disk and photon-ring
  "anisotropic" multipliers (`:332-334`, `:484-490`), the sign-only escaped-sky sector
  shaping (`:616-620`, debug view `:594-598`), and the optional wiregrid overlay (`:670`).
- The sky is rotated by `time` degrees (`:518`), which is 1 deg/s of wall clock.
- The Kerr path (`bhTraceGeodesic*`) runs only when `interopParityMode` is set, which comes
  from compare mode, or on the compute path when `useComputeRaytracer` is set.
- `BlackholeCUDA` defaults to spin 0 and the Schwarzschild RK4 (`device_physics.cuh:991`),
  and enters the F1-F3 Kerr path whenever spin is nonzero.

Why it matters: what a user sees at launch has no stated error bound. Moving the spin slider
in the default path changes color and nothing geometric, while moving it in the compute or
CUDA paths shrinks the shadow by 32%.

Fix: issue #15's typed renderer/model selection, with the legacy path labeled "artistic".
Promote a Kerr reference path only after F1-F3 and issue #16's scene A/C gates pass.

Falsifier: at spin 0.9 in the default path, capture at a radius other than `r_s` in the
captured-pixel mask.

### F5. No render path uses a relativistic disk transfer function -- HIGH

Tag: **NEW**. The disk-plane axis mismatch alone is **TRACKED** in the issue #21 note and
the #15 "disk-plane conventions" item.

Sites:
- `shader/include/interop_trace.glsl:163-173`: redshift `sqrt(1 - r_s/r)`, which is
  static-emitter only.
- `interop_trace.glsl:402`, `:607`, and `:743`: `doppler = 1 + 0.3 v cos(phi)` with `phi =
  atan(y,x)` fixed in world axes.
- `shader/include/doppler_beaming.glsl:86` and `:98`, used by the default path through
  `blackhole_main.frag:323`.
- `src/cuda/device_physics.cuh:1154` and `:1163`.

Observed:
- The observed intensity is never computed as `g^3 I_nu` or `g^4 I` with `g = 1/(u^t (1 -
  Omega b))` taken from the traced photon's constants. `kerrDiskGFactor` (`iron_kline.h:91`)
  exists but no render path calls it.
- The default path's beaming uses `cos(theta) = sin(i) cos(phi)` with phi measured from
  world +x. The approaching side stays fixed in the world frame, so when the camera orbits,
  the bright side does not follow the line of sight.
- Its Kerr orbital speed `sqrt(1/(r - 2 + a sqrt(1/r)))` is not the Bardeen-Press-Teukolsky
  ZAMO-frame speed. At a = 0.9 the repo value saturates at the 0.99 cap at r_isco = 2.32 M,
  while the exact value is 0.624. At r = 6 M the values are 0.479 and 0.417. At a = 0 the
  formula is exact.
- The CUDA disk takes r from `(x, y)`, meaning the disk lies in the xy plane, but sets
  `vel_dir = (-z, 0, x)`, a velocity in the xz plane. The beaming term is therefore not tied
  to the disk's own rotation.

Why it matters: the brightness asymmetry of the disk and the photon ring is the most visible
spin signature and the quantity the EHT fits. With this code it is decoration.

Fix:
1. Carry `(E, Lz)` from the traced ray to the disk hit.
2. Compute `g = sqrt(1 - 3/r + 2a r^{-3/2}) / ((1 + a r^{-3/2})(1 - Omega b))` in M = 1
   units, for r >= r_isco.
3. Use `I_obs = g^4 F(r)` for the bolometric render.
4. Expose `dopplerStrength` as a labeled canon/accuracy toggle. James et al. 2015
   (arXiv:1502.03808, section 4) document that Nolan and Franklin removed Doppler and
   gravitational shifts from the Interstellar disk, and lowered the spin to a/M = 0.6, for
   visual reasons. "Interstellar look" is therefore a legitimate named preset, but it should
   not be the default.

Falsifier: for a face-on disk, the rendered ISCO-to-10M intensity ratio should match `g^4 F`
computed by hand.

### F6. "Novikov-Thorne" in every render path is the Newtonian profile, and `thin_disk.h`'s "Page & Thorne formula" is not Page-Thorne -- HIGH

Tag: **TRACKED-BUT-WRONG**. `docs/physics/lacunae.md:41` marks the "Novikov-Thorne accretion
disk 100%", and `claims_evidence.json` claim `novikov_thorne_disk` says the same.

Sites:
- `interop_trace.glsl:376-379` and `:599-600`, and `device_physics.cuh:1104`: `x^3 (1 - sqrt
  x)`.
- `src/physics/novikov_thorne.h:130` and `:175`: `1 - sqrt(r_isco/r)`, labeled a "simplified
  approximation".
- `src/physics/thin_disk.h:212-230` (`novikovThorneFactor`, labeled "Page & Thorne (1974)
  formula").
- `scripts/generate_luts.py:45`: an ad hoc `spin_factor = 1 + 0.5 a sqrt(M/r)`.

Measured against the Page-Thorne flux. A numerical integral and the x0..x3 closed form agree
to 1e-5 at 8 radii for a = 0 and a = 0.9. The integral is normalized so that it tends to the
Newtonian form at large r (ratio 0.954, 0.985, 0.995 at r = 1e3, 1e4, 1e5):
- At a = 0 the flux peaks at 9.55 M. The repo profile peaks at 8.17 M. After
  max-normalization the flux ratio (Page-Thorne / repo) is 0.62 at 1.2 r_in, 1.32 at 2 r_in,
  and 1.67 at 4 r_in.
- At a = 0.9 the peaks are 3.44 M and 3.16 M.
- `novikovThorneFactor` at r = 7, 10, 20, 100 M gives 0.023, 0.100, 0.283, 0.642, while the
  exact f is 0.018, 0.114, 0.317, 0.652. Its three terms do not match Page-Thorne's closed
  form, which uses the roots x1, x2, x3 of `x^3 - 3x + 2a = 0`.

Fix: implement the Page-Thorne closed form, which reduces to the x0..x3 logarithmic
expression in Page and Thorne (1974), and generate the emissivity LUT from it. Test the a =
0 peak at 9.55 M and the efficiency `1 - E_isco`.

Falsifier: a Page-Thorne flux peak at a = 0 of anything other than about 9.5 M would
disprove F6.

### F7. The Fe K-alpha "Laor 1991" profile has no light bending and a wrong `u^t` for a != 0 -- MEDIUM

Tag: **TRACKED-BUT-WRONG**. `lacunae.md:540` says "COMPLETE -- ironKLineProfile".

Sites: `src/physics/iron_kline.h:98` and `:104`.

Observed:
- `g = sqrt(1 - 3/r + 2a r^{-3/2}) / (1 - sin(phi) sin(i) Omega r)`. Two things are missing:
  the `(1 + a r^{-3/2})` factor of `1/u^t` (Bardeen-Press-Teukolsky), and ray tracing. The
  impact parameter is the flat-space projection `b = r sin(i) sin(phi)`, and the disk-area
  weighting `r dr dphi` stands in for the observer solid angle.
- Laor (1991) computed a ray-traced transfer function. The g^4 weighting for an
  energy-binned delta line is correct and is not part of this finding.

Measured face-on at the ISCO (repo / exact):
- a = 0.5: 1.057
- a = 0.9: 1.255
- a = 0.998: 1.725

The tests (`tests/iron_kline_test.cpp`) assert only properties: the Schwarzschild value, the
side of the shift, normalization, and monotonicity. None compares against a published
profile.

Fix: add the missing factor, drive the profile from the F2-fixed Kerr tracer or from
AART-style analytic transfer functions (Cardenas-Avendano, Lupsasca, Zhu, PRD 107 043030,
arXiv:2211.07469), and gate it against a tabulated relline/kyrline or Laor profile at two
spins.

Falsifier: `1/u^t` at a = 0.9, r = r_isco evaluated from the metric equals 0.371. The repo
gives 0.465.

### F8. The GPU "volumetric RTE" and "Stokes IQUV" paths are shading models, not radiative transfer -- MEDIUM

Tag: **TRACKED-BUT-WRONG**. `lacunae.md:522-523` marks both COMPLETE, while the same
document's sections 2.2 (`:113-131`) and 6.3 (`:669`) still call polarized RT "completely
absent", which contradicts the table.

Sites:
- `interop_trace.glsl:545-554` (a = 0 falls back to a surface hit), `:582` and `:616`
  (`rteStepDt` used as the path length), and `:614` (`alphaNu = opacityScale*jEff`).
- `interop_trace.glsl:697` and `:757` (uniform sky-plane EVPA `bFieldAngle`, fixed `PI_LIN =
  0.75`).

Observed:
- The path length passed to the transfer step is the Mino-time increment `d lambda`. That is
  neither affine distance nor proper length, and it depends on the E = 1 normalization.
- Absorption is `alpha = k*j`, so the source function is the constant `1/k`. Kirchhoff's law
  and frequency dependence are absent, and the invariant `I_nu/nu^3` is never formed.
- The polarization frame is never parallel-transported: there is no Walker-Penrose constant
  and no tetrad at the emitter, and the B-field direction is a single global sky angle.
- The volumetric model exists only for a != 0, so the radiative model changes
  discontinuously at a = 0.
- The CPU `rte_integrator.h` and `stokes_transport.h` steps are tested against exact
  flat-slab solutions (`tests/rte_integrator_test.cpp:104`,
  `tests/stokes_transport_test.cpp:183-233`). That testing is sound for the one-step solver,
  but it does not validate GR transport.

Fix:
1. Integrate in affine parameter, with `ds = (dlambda_affine)(-k_mu u^mu)` in the fluid
   frame.
2. Use thermal synchrotron `j_nu`/`alpha_nu` with Kirchhoff's law.
3. Transport the polarization with the Walker-Penrose constant or a covariant tetrad, as in
   ipole or Coport (Huang, Zheng, Guo, Chen, arXiv:2407.10431).
4. Adopt the EHT polarized code-comparison analytic model as a gate. Prather et al., ApJ 950
   35 (2023), arXiv:2303.12004, report inter-code NMSE <= 0.012 on the analytic model, and
   0.02/0.04/0.12 for I/QU/V on a GRMHD snapshot.

Falsifier: if the rendered Stokes image of that analytic model reached NMSE < 0.05 against
the published reference, F8 would be overstated.

### F9. The camera does not use a local orthonormal observer frame -- MEDIUM

Tag: **TRACKED**. Issue #15 lists "camera tetrad / local direction initialization".

Sites: `shader/include/interop_raygen.glsl:10-17` and `kerr.glsl:104-106`.

Observed: the pixel direction is a Euclidean unit vector. Its coordinate-basis components
`k^r = dir.e_r` and `k^phi = dir.e_phi/(r sin theta)` enter the metric with no `sqrt(g_rr)`
or ZAMO/FIDO normalization. The same pixel therefore maps to different angles in the a = 0
Binet path and the Kerr path. At r = 15 M, a = 0.01, the physical half-width is 0.366
against 0.369 on the Binet path, while the static-observer exact value is 0.341.

Fix: build the FIDO/ZAMO tetrad at the camera and apply camera-velocity aberration, as in
James et al. 2015, Appendix A.1 (arXiv:1502.03808).

Falsifier: the rendered Schwarzschild shadow half-width at r = 15 M matching the
static-observer value `tan(asin(sqrt(27)*sqrt(1 - 2/15)/15)) = 0.3407` in both the a = 0 and
the a -> 0 Kerr paths would disprove F9.

### F10. `kerrTimeDilation` is the static-observer rate and returns NaN inside the ergoregion; `kerrRedshift` returns +inf there -- MEDIUM

Tag: the static-observer mislabel is **TRACKED** in a source comment,
`src/game/kerr_time_field.h:12`. The NaN is **NEW**.

Sites: `src/physics/kerr.h:348-362` and `:389`, and `src/physics/batch.h:671`.

Observed:
- The docstring promises the ZAMO rate. The body returns `sqrt(-g_tt)`.
- At a = 0.9, r = 1.6 M (between r+ = 1.436 and r_ergo = 2), `-g_tt = -0.25`, so the
  function returns `sqrt(-0.25) = NaN`. The ZAMO lapse there is 0.197.
- `kerrRedshift` (`kerr.h:380-390`) is the static-emitter `1+z`. It returns `safeInfinity`
  at and inside the ergosurface rather than at the horizon, and `kerrRedshiftBatch`
  (`batch.h:671-675`) maps that non-finite value to z = 0, meaning no redshift at all for an
  ergoregion emitter.

Fix: return the ZAMO lapse `sqrt(Sigma Delta / A)`, which `game::KerrTimeField` already
computes, or rename the function to `staticObserverRate` with an ergoregion precondition.
Emitters on circular orbits use `1/u^t` (F5).

Falsifier: `kerrTimeDilation(1.6M, pi/2, M, 0.9M)` returning a finite value.

### F11. The integrator lacks error control, has a Schwarzschild-hardcoded refinement zone, is FP32-only, and has no anti-aliasing or ray bundles -- MEDIUM (performance plus accuracy)

Tag: partially **TRACKED** at `lacunae.md:507-514` (AMR). The rest is **NEW**.

Sites: `interop_trace.glsl:91-103` and `device_physics.cuh:877`.

Observed:
- The step is a heuristic `min(scale_far, scale_h, scale_ph)` with `r_ph = 1.5 r_s` for
  every spin. The Kerr photon shell spans 1-4 M, and there is no local error estimate.
- The CPU `dormand_prince` stepper exists, but no GPU path uses it.
- No `double` or `dvec` appears in any shader or in `device_physics.cuh`.
- The code has no supersampling, no ray-bundle or geodesic-deviation propagation
  (`geodesics.glsl:83` is a comment only), no temporal reprojection, and no
  persistent-thread scheduling.
- Critical-curve sharpness, meaning the n >= 1 subrings, is limited by single-sample pixels.

Why it matters: the photon subrings decay exponentially with order (Johnson et al., Sci.
Adv. 6 eaaz1310, arXiv:1907.04329). Resolving them needs step control near the photon shell
and either adaptive screen sampling (AART) or ray-bundle filtering. DNGR states that ray
bundles were "crucial for achieving IMAX-quality smoothness without flickering"
(arXiv:1502.03808).

Fix:
1. After F1-F2, replace the heuristic with an embedded RK error estimate in Mino time.
2. Add a per-pixel Jacobian (geodesic deviation or finite-differenced neighbor rays) for
   magnification and footprint-based texture filtering.
3. Keep FP32 for the march, but compute near-horizon and turning-point quantities in
   rationalized forms. On consumer GPUs FP64 runs at 1/64 rate. Moscibrodzka and Yfantis
   (arXiv:2302.02733) report a speedup of up to about 1200x only on GPUs with strong FP64.

Falsifier: MAXSTEPS fraction and critical-curve radius error both falling monotonically with
the step budget on issue #16's scene D.

### F12. Research citations in `lacunae.md` misattribute authors and misstate findings -- MEDIUM (documentation integrity)

Tag: **TRACKED-BUT-WRONG**. Each entry below was checked against the fetched arXiv abstract
page.

- arXiv:2310.02321 is Bozzola, Chan, Paschalidis, "Not all spacetime coordinates for
  general-relativistic ray tracing are created equal", PRD 108 084004 (2023), not "Vos, J.
  et al." (`lacunae.md:760`). The abstract reports that rays whose momentum points toward or
  away from the horizon lead to different solutions, and that different coordinates give
  "the same images up to numerical errors". It does not establish the "OUTGOING KS is the
  correct choice ... critical correctness constraint" rule at `:403-415` and `:636-653`. The
  code the doc calls "outgoing KS" (`kerr.glsl:193`) is the ingoing-KS form (`A + dr` over
  Delta), consistent with F3.
- arXiv:2302.03704 is Dyson and van de Meent, "Kerr-fully Diving into the Abyss: Analytic
  Solutions to Plunging Geodesics in Kerr", not "Dyson, Warburton, Barack" (`:352-361`,
  `:740`). It treats timelike plunges, which do not bear on the photon ray-tracing estimate
  the doc revises with it.
- arXiv:2304.11185 is Blanchet, Faye, Henry, Larrouturou, Trestini, "Gravitational-Wave
  Phasing of Quasi-Circular Compact Binary Systems to the Fourth-and-a-Half post-Newtonian
  Order", PRL 131 121402 (2023), not "Blanchet, Buonanno, Henry 2024, tail effects in the
  3PN flux" (`:732`).
- DOI 10.3847/2041-8213/ad2df1 is "First Sagittarius A* EHT Results. VIII. Physical
  Interpretation of the Polarized Ring", ApJL 964 L26 (2024). The doc calls it "Paper IX:
  Polarimetry" (`:742`). The quoted "~25% linear polarization" was not verified from the
  fetched page (metadata only).

Fix: correct the attributions, delete the "outgoing KS is a critical correctness constraint"
rule, and add a citation verifier that resolves arXiv IDs to titles, extending issue #19's
evidence taxonomy.

### F13. The EHT shadow claim rests on a mock generator -- MEDIUM

Tag: **TRACKED** in issues #16 and #19. `claims_evidence.json` claim `eht_observables` lists
`eht_shadow_validation`, and `tests/eht_shadow_test.cpp` never renders through GL or CUDA.
F1 shows the consequence: that claim coexists with a 32% error in the rendered Kerr shadow.
Issue #16's scenes A, C, and D would have caught F1-F3.

### F14. Tautological tests survive `ea2eb1a`; the GRMHD claim is pipeline evidence only -- MEDIUM

Tag: **TRACKED-BUT-WRONG** for `claims_evidence.json` claims `novikov_thorne_disk`,
`radiative_transfer_pipeline`, and `grmhd_ingestion_streaming`. Issue #19 names the class
but not these instances.

Observed:
- `tests/novikov_thorne_test.cpp:136-160` asserts `peakTemperatureRadius / r_isco == 1.5` to
  1e-6. `src/physics/novikov_thorne.h:194` hard-codes `return 1.5 * iscoRadius(aStar)`, so
  the test restates the implementation. The Page-Thorne value is 9.55/6 = 1.59 (F6).
- `tests/radiative_transfer_test.cpp:32-64` defines its own `cpuOpticalDepthIntegrate` and
  `cpuIntensityStep` and tests those. Only the synchrotron coefficients come from `src/`,
  and neither `rte_integrator.h` nor the shader is exercised. (`rte_integrator_test.cpp`
  does test the real step against the exact slab solution.)
- `tests/grmhd_composite_raytracer_test.cpp:19-58` computes an inline 70/30 blend and checks
  that the result lies in [0, 1]. It includes no compositing code from `src/`.
- The GRMHD tests (`grmhd_hdf5_loader`, `grmhd_streamer_e2e`, `grmhd_gpu_async`,
  `grmhd_pack`, `grmhd_metadata`) are pipeline evidence of I/O, cache, and upload integrity.
  No test evaluates `shader/include/grmhd_octree.glsl` emission or absorption against a
  known model, and none renders a GRMHD snapshot. The Prather et al. (2023) snapshot test is
  the natural gate.
- `ea2eb1a` rewrote the tests of `iron_kline`, `kerr_newman`, `newman_penrose`,
  `gw_multipole`, and other modules. It changed only two lines of
  `radiative_transfer_test.cpp` and did not touch `novikov_thorne_test.cpp`.

Fix: tag each claim with issue #19's evidence class and demote these three to `formula-unit`
or `pipeline` until a gate backed by an independent oracle or a render output exists.

Falsifier: a `src/` include that makes `cpuIntensityStep` a thin wrapper over
`rte_integrator.h` would clear the RTE item.

## 2. State-of-the-art gap map

| Capability | Repo status (evidence) | 2025-26 best practice (fetched source) | Priority |
| --- | --- | --- | --- |
| Kerr null geodesic constants | Wrong R (F1); spin mirrored (F3) | Separated R/Theta, Gralla and Lupsasca PRD 101 044032, arXiv:1910.12881 | P0 |
| Geodesic integrator | Euler Mino, frozen at turning points (F2); Schwarzschild Binet RK4 is correct | Hamiltonian in Cartesian KS with adaptive RK (GRay2, arXiv:1706.07062); closed-form elliptic (1910.12881) | P0 |
| Analytic/fast imaging | `analytic_kerr_geodesic.h` and `device_analytic_kerr.cuh` are radial-only prototypes used by tests only (F2) | AART adaptive analytic ray tracing for photon rings, arXiv:2211.07469 | P1 |
| Camera model | Euclidean directions, no tetrad (F9) | FIDO-frame camera with aberration, arXiv:1502.03808 App. A | P1 |
| Disk emission | Newtonian profile, ad hoc Doppler, static redshift (F5, F6) | Page-Thorne flux with g^4 transfer; Interstellar's no-Doppler look as an explicit toggle (1502.03808 sec. 4) | P0 |
| Polarized GRRT | Uniform-EVPA shading; transfer step only in flat slab (F8) | Covariant transport (ipole, Coport arXiv:2407.10431); cross-code NMSE gates (Prather et al. arXiv:2303.12004) | P1 |
| GRRT verification | No published benchmark reproduced; mock EHT test (F13) | EHT GRRT verification suite, Gold et al., ApJ 897 148 (2020), DOI 10.3847/1538-4357/ab96c6 | P1 |
| Observational anchors | Static M87*/Sgr A* presets | M87* ring diameter 43.9 +/- 0.6 uas across 2017/2018/2021, EVPA helicity flip in 2021, arXiv:2509.24593; Sgr A* polarized ring ApJL 964 L26 (2024) | P2 |
| Photon-ring and subring science | None (single-sample pixels) | Universal interferometric subring signatures, arXiv:1907.04329; BHEX mission, arXiv:2406.12917 | P2 |
| 345 GHz / higher frequency | Single-frequency LUT shading | First 870 um VLBI detections, 19 uas fringe spacing, Raymond et al. AJ 168 130 (2024), arXiv:2410.07453 | P3 |
| Anti-aliasing and magnification | None (F11) | Ray bundles via geodesic deviation with spatial and temporal filtering (DNGR, 1502.03808 sec. 2.2-2.3) | P1 |
| Precision strategy | FP32 everywhere; rationalized horizon terms (sound idea) | FP64 where hardware supports it (Moscibrodzka and Yfantis, arXiv:2302.02733); otherwise rationalized FP32 plus error control | P2 |
| GPU scheduling | Tile dispatch plus 2-ray ILP interleave (`kernels_fp32.cu:119`); no persistent threads or reprojection | Wavefront/persistent scheduling and temporal reprojection are general GPU practice (no source fetched; inference) | P3 |
| Time dilation / redshift API | Static-observer, NaN in ergoregion (F10) | ZAMO lapse `sqrt(Sigma Delta/A)`; emitter `1/u^t` | P1 |

## 3. Recommended order of work

1. Apply F1 to all three sites and add the potential-consistency test. This is a one-term
   change plus a test.
2. Fix F2 with the second-order Mino form or KS Hamiltonian RK, reusing `kerr.cpp`'s `dRdr`,
   and fix F3 by tracing the arriving photon backward. Then re-measure the capture edges
   against the R-positivity scan of section 5 (`harness/shadow2.py`);
   `analytic_kerr_geodesic.h` becomes an oracle only after its `findRadialRoots` fix
   (05 M5).
3. Land issue #16 scenes A/C/D as offscreen gates on the fixed path. Then apply F9 (camera
   tetrad) and F5/F6 (g-factor and Page-Thorne).
4. Pursue F8 (covariant polarized transport against the Prather 2023 analytic model) and F11
   (error control, per-pixel Jacobian, filtering).
5. Apply the F10 and F12 documentation and API corrections in the same pass as issue #19.

## 4. Checks not run

- Rendered-pixel measurements were not run. No offscreen GL/CUDA capture harness exists
  (issue #16), and running the desktop binary was out of scope. Every geometry number is a
  line-by-line Python port of `kerr.glsl`/`device_physics.cuh`, not a GPU capture.
- A vertical (beta) scan confirming F1's oblateness was not run because it needs theta
  stepping in the port. The `Lz = 0` argument is analytic.
- No rebuild was done: the primary checkout is read-only for this audit. The CTest results
  come from July binaries (before `a4e1f1d`), and the shader findings bind to source because
  GLSL loads at runtime from `shader/`.
- `physics_bench` and the compare sweep were not run: they are performance and parity tools
  and do not bear on F1-F3's correctness.
- The Gold et al. (2020) arXiv ID was not resolved (a search named arXiv:2002.04273, which
  is an unrelated mathematics paper). The DOI page was fetched and is cited instead.
- EHT Sgr A* polarization fractions were not verified (the page fetch returned metadata
  only).

## 5. Reproduction notes

Each item runs from `harness/`; `harness/README.md` gives the commands.

- F1: port `kerrInitConsts` verbatim and compare `A^2 - Delta (Q + (Lz - a)^2)` with `(Sigma
  k^r/E)^2`.
- F2 and F3: port `kerrStep` and `bhAdaptiveStep` with the defaults `stepSize = 0.1`,
  `maxSteps = 300`, and `maxDistance = 100` (`render_state.h:319-320`, `:103`). Put the
  camera at `(15, 0, 0)` and use equatorial pixels `normalize(-1, y, 0)`. Tally terminal
  classes, and apply R-positivity on `(r+, r0)` to the constants from `dir` and from `-dir`.
- F5-F7: use the BPT closed forms for `u^t`, the ZAMO speed, and `r_isco`, and the
  Page-Thorne integral cross-checked against its closed form.
