# open_gororoba cross-reference for the Blackhole physics core

Scope: numeric and formula cross-check of Blackhole (`/home/eirikr/Github/Blackhole`, GPL-3.0,
HEAD `34e1bf1`) against open_gororoba (`/home/eirikr/Github/open_gororoba`, workspace
GPL-2.0-or-later), triage of the physics and GPU crates on the two axes
mathematical accuracy and computational efficiency, and ranked porting advice. Both trees
were read-only. Every number below comes from one of three executables built in the
session scratchpad:

- `referee.py` -- an mpmath (1.4.1, 30 digits) referee written from textbook metrics only:
  Kerr and Kerr-Newman in Boyer-Lindquist form with `g_tphi = -a sin^2(2Mr - Q^2)/Sigma`
  (Misner-Thorne-Wheeler 33.2), and Carter's Kerr-de Sitter form with
  `Delta_r = (r^2+a^2)(1 - Lambda r^2/3) - 2Mr`, `Delta_theta`, `Xi`. It derives circular
  orbits from `dg/dr`, sets the ISCO at `dE/dr = 0` and the photon orbit at the pole of
  `u^t`, and computes the Page-Thorne flux by quadrature. Three anchors hold: the
  metric-derived ISCO equals BPT to 16 digits at every spin; the a=0 Kerr-Newman ISCO
  equals the Reissner-Nordstrom cubic `r^3 - 6Mr^2 + 9Q^2 r - 4Q^4/M = 0`; and the
  Page-Thorne quadrature equals the Page-Thorne 1974 closed form to 6 digits at four spins.
- `bh/driver.cpp`, `bh/mino2.cpp`, `bh/gfac.cpp` and `bh/ecg.cpp` -- clang++ 22.1.8 `-std=c++23 -O2`. They link Blackhole's
  `src/physics` headers together with `kerr.cpp` and `schwarzschild.cpp`.
- `grx` -- rustc 1.98.1 release. It takes a path dependency on `gr_core` pinned to
  open_gororoba's `Cargo.lock`, with `CARGO_TARGET_DIR` set to the scratchpad.

Units are M = 1 unless stated. OBSERVED means the output of one of these executables or a
read of the named line. INFERRED means a conclusion that goes beyond that output.

## Lineage finding (read first)

OBSERVED: open_gororoba's black-hole modules in `gr_core` are ports of Blackhole. They are
`novikov_thorne`, `doppler`, `hawking`, `synchrotron`, `penrose`, `kerr_newman`,
`kerr_de_sitter`, `energy_conserving` and `null_constraint`. The git creation dates settle
the direction:

| Module | Blackhole created | gr_core created |
|---|---|---|
| Blackhole physics headers (`doppler`, `hawking`, `synchrotron`, `penrose`) | 2025-12-29 | 2026-02-06 |
| Rocq KN/KdS | 2026-01-02 | 2026-02-07 |

The docstrings are identical ("phi=0 = approaching limb", "Fouka & Ouichaoui (2013)
polynomial fit"). The KN and KdS errors match to the last digit (tables below).

Consequence: agreement between the repos on these modules is one source counted twice, and
it is no evidence of correctness. Only the literature referee adjudicates. The
independent content in gr_core is:

- `kerr.rs`: a second-order Mino integrator with `u = 1/r` regularization and DOPRI5,
  analytic Christoffels, and a Bardeen shadow curve.
- `metric.rs`: generic Riemann, Ricci and Kretschmann tensors.
- `gravitational_waves.rs`.
- `energy_conserving.rs`: its null-norm correction diverged from its Blackhole origin and
  is the correct one (F7).
- `novikov_thorne.rs`: its temperature units were fixed at port time. The 100x bug has
  been in Blackhole since commit `820e2ff` (2026-01-29) (F3).
- The speculative Cayley-Dickson modules.

The "verified" label on Blackhole's `src/physics/verified/*` does not certify the physics.
`rocq/theories/Metrics/KerrNewman.v` transcribes the wrong `g_tphi` (line 70) and the wrong
ISCO (lines 191-201) as `Definition`s. Its reduction theorems end in `Admitted.`
(lines 118, 177, 237, 251).

## Ranked findings

Severity reflects reach. LIVE means the value reaches pixels through
`src/render/lut_manager.cpp` or a shader. LATENT means only tests, the bench or the Blender
bridge call it.

**LUT reach.** `updateLuts` is called at `main.cpp:894` with `rs.physicsCore.kerrSpin`,
whose default is 0 (`render_state.h:186`). The spin-0 asset LUTs load whenever the spin
matches `assets/luts/lut_meta.json` (`lut_manager.cpp:177-180`). Any other spin
regenerates the LUTs through `lut.h`. `scripts/generate_luts.py:40-52` built the asset
LUTs with the same two formulas as `lut.h`.

- **Emissivity LUT:** sampled whenever the textures exist, which is the default
  (`main.cpp:841,957`; `blackhole_main.frag:354-356`).
- **Redshift LUT:** sampled only when `enableRedshift` is on (`blackhole_main.frag:373-379`).
  That flag defaults to false (`render_state.h:188`); the record profiles turn it on
  (`record_mode.cpp:200,254`).

The default fragment path traces Schwarzschild geodesics, so spin reaches pixels there only
through these LUTs.

### F1. Emissivity LUT uses an invented Kerr flux, and both repos label a Newtonian profile "Page & Thorne" (Blackhole LIVE by default, gr_core LATENT)

The default spin-0 asset LUT is the Newtonian profile (`generate_luts.py:44-46`).
OBSERVED: it peaks at 1.365 r_isco on the LUT grid, against the continuous Page-Thorne
peak at 1.592 r_isco (9.55M). The
normalized shape differs by up to 0.398. This is the emissivity every default frame
multiplies into disk density. It is ranked first because it has the widest reach.

- **Where:**
  - Blackhole: `thin_disk.h:243-270`. For a != 0 it computes
    `f = (1 - sqrt(r_in/r))(1 + 0.5 a sqrt(1/r))`. For a = 0 it uses
    `novikovThorneFactor` (`thin_disk.h:212-230`), with extra terms that match no
    published form. These feed `generateEmissivityLut` (`lut.h:66`) and so
    `lut_manager.cpp:267`.
  - Blackhole also carries `novikov_thorne.h:128-130` with the Newtonian
    Shakura-Sunyaev `f = 1 - sqrt(r_in/r)` labeled "Page & Thorne 1974".
  - gr_core copies the Newtonian form at `novikov_thorne.rs:86,112`.
- **OBSERVED (referee, f normalized so that f -> 1 at large r):**

| a | r | Page-Thorne | Newtonian (both repos) | Blackhole LUT (Kerr approx.) | Blackhole a=0 factor |
|---|---|---|---|---|---|
| 0 | 1.5 r_isco | 0.0822 | 0.1835 | -- | 0.0748 |
| 0.5 | 1.5 r_isco | 0.0908 | 0.1835 | 0.2017 | -- |
| 0.9 | 1.5 r_isco | 0.1198 | 0.1835 | 0.2278 | -- |
| 0.998 | 1.5 r_isco | 0.2186 | 0.1835 | 0.2507 | -- |

  - The normalized LUT shape departs from Page-Thorne by up to 0.38 (a=0.5).
  - Peak radius, Page-Thorne vs. LUT: 1.59 vs 1.52 r_isco at a=0; 1.48 vs 1.35 r_isco
    at a=0.9. The driver's LUT peak at a=0.9 is 1.353 r_isco, which matches.
  - `thin_disk.h:125-127` hard-codes the efficiency at 0.0572, or 0.3 when |a| > 0.9.
    The referee gives 0.0821 (a=0.5), 0.1558 (a=0.9) and 0.3210 (a=0.998).
  - That efficiency only scales Mdot. `generateEmissivityLut` divides by the maximum
    (`lut.h:77-86`), so the efficiency error leaves the rendered LUT shape unchanged. The
    shape error comes entirely from f(r).
- **Falsifier:** the closed-form Page-Thorne expression in `referee.py:page_thorne_closed`
  disagreeing with its own quadrature. It agrees to 6 digits.

### F2. Disk redshift LUT is static-emitter, spin-blind, and zero-filled inside the ergosphere (Blackhole, LIVE when redshift is enabled)

- **Where:**
  - `src/physics/lut.h:102-122` (`generateRedshiftLut`) calls `batch.h:666-677`
    (`kerrRedshiftBatch`), which calls `kerr.h:380-390` (`kerrRedshift` = `1/sqrt(1 - r_s r/Sigma) - 1`).
  - The LUT is uploaded at `lut_manager.cpp:269-273` and sampled at
    `shader/blackhole_main.frag:379,571` and `shader/include/interop_trace.glsl:418`.
- **OBSERVED (driver):**
  - At theta = pi/2, Sigma = r^2, so the value is independent of spin; spin only moves the
    sampled radius range.
  - At a=0.998, 53 of 256 bins read z = 0, including bin 0 at the ISCO. There,
    `1 - 2M/r < 0` produces +inf, which `batch.h:672` maps to 0.
  - The referee gives the circular-orbit (disk-emitter) value at that ISCO as
    `1/u^t = 0.0927`, which is z = 9.79.
  - At a=0.5 the LUT's z(ISCO) = 0.377 against the circular-orbit 0.659, because the
    transverse-Doppler part of `u^t` is missing.
  - Even the default spin-0 asset LUT stores z(ISCO) = 0.2247 (static emitter). The
    circular-orbit value is 1/u^t = 0.7071, which is z = 0.414.
- **Consequence:** with redshift enabled, every spin under-redshifts the disk. At
  a > 2*sqrt(2)/3 = 0.943, where the ISCO drops below 2M, the innermost annulus renders
  with no redshift at all. `blackhole_main.frag:571` also applies this LUT to background
  light at `minRadiusReached`.
- **Falsifier:** `blackhole_main.frag:373-379`, the site read above, samples the LUT
  whenever `enableRedshift > 0.5 && useLUTs > 0.5`. The finding fails if a
  circular-orbit redshift is computed downstream and overwrites `z` before
  `applyGravitationalRedshift`.

### F3. NovikovThorneDisk temperature is 100x too high (Blackhole LATENT; gr_core correct)

- **Where:** `novikov_thorne.h:118`, `cCgs = ::physics::C * 1e2`. `physics::C` is
  already 2.998e10 cm/s (`constants.h:23`).
- **OBSERVED:**
  - At r=9M, a=0, mdot=0.1, M=4e6 Msun: Blackhole gives 1.913e7 K, gr_core
    `disk_temperature` gives 1.912e5 K, and an independent evaluation gives 1.913e5 K.
    The ratio is 100.00.
  - `NovikovThorneDisk::integratedLuminosity` is unaffected, because c^2 cancels.
  - Callers are `tests/novikov_thorne_test.cpp` and `blender_bridge.cpp:482`, which uses
    efficiency only.
  - The docstring (`novikov_thorne.h:17,53`) claims eta = 0.42 at a=0.998. The code
    returns 0.3210, which is correct. The test `tests/novikov_thorne_test.cpp:61-67`
    accepts [0.30, 0.42], a window wide enough to pass both.
  - This is one of two inter-repo disagreements where gr_core is right.

### F4. Kerr-Newman ISCO moves the wrong way, and `g_tphi`/`omega` drop the Q^2 term (both repos, shared Rocq source)

- **Where:**
  - ISCO: `verified/kerr_newman.hpp:342-379` and `rocq/.../KerrNewman.v:191-201`;
    gr_core `kerr_newman.rs:158-187`. Both add `+Q^2/(2M^2)`, which is dimensionally a
    pure number added to a length.
  - `g_tphi`: `kerr_newman.h:201-204`, `verified/kerr_newman.hpp:434-437`,
    `kerr_newman.rs:218-221`, and `KerrNewman.v:70`.
  - omega: `kerr_newman.h:356`, `verified/kerr_newman.hpp:295`, `kerr_newman.rs:147`.
    All three write `2Mar/A`.
- **OBSERVED:**

| a, Q | Referee ISCO (prograde) | RN cubic | Repo value | Error |
|---|---|---|---|---|
| 0, 0.5 | 5.6066 | 5.6066 | 6.1250 | +9% |
| 0, 0.9 | 4.5137 | 4.5137 | 6.4050 | +42% |
| 0.5, 0.5 | 3.7321 | -- | 4.3580 | +17% |
| 0.9, 0.3 | 1.9804 | -- | 2.3659 | +19% |

  - Frame dragging at r=3, a=Q=0.5: referee `a(2Mr - Q^2)/A` = 0.03395; repos 0.03542.
  - gr_core pins the wrong direction with the test `test_isco_charge_increases_isco`
    (`kerr_newman.rs:453`).
  - Blackhole's `tests/kerr_newman_test.cpp` checks only Q=0 (line 158) and a=0 (line 121).
    Both limits hide the `a*Q^2` cross term.
- **Vector-potential sign, OBSERVED:**
  - `physics::knMagneticPotentialPhi` returns +0.0833. `verified::knPotentialPhi` and
    gr_core `potential_phi` return -0.0833 (`verified/kerr_newman.hpp:180`,
    `kerr_newman.rs:97`).
  - The sign of A_phi alone is a convention. The ratio A_phi/A_t is not: it is fixed at
    `-a sin^2(theta)` because the potential is proportional to `dt - a sin^2 dphi`.
  - With A_t = -Qr/Sigma in all three implementations, `physics::` is consistent. The
    verified header and gr_core flip the magnetic dipole relative to the spin.

### F5. Kerr-de Sitter is not the Carter metric (both repos, shared Rocq source)

- **Where:** `verified/kerr_de_sitter.hpp:82,134,247-291`, `KerrDeSitter.v:55`, and
  gr_core `kerr_de_sitter.rs:42,63,104-129`.
  - `Delta = r^2 - 2Mr + a^2 - Lambda r^2/3` is quadratic and dimensionally
    inconsistent, so it cannot have the cosmological root its own docstring promises.
  - `g_tt` carries `+Lambda r^2 sin^2/3`, which has the wrong sign and a spurious sin^2.
  - `g_tt` and `g_rr` disagree with each other even at a = 0.
- **OBSERVED (referee roots of the Carter quartic vs. the repos' horizons):**

| a, Lambda | r_+ referee | r_+ repo | r_c referee | r_c repo |
|---|---|---|---|---|
| 0, 1e-4 | 2.000267 | 2.000267 | 172.196 | 173.205 |
| 0, 1e-2 | 2.027794 | 2.026667 | 16.217 | 17.321 |
| 0.9, 1e-2 | 1.459196 | 1.445758 | 16.221 | 17.321 |
| 0.9, 0.1 | 1.782486 | 1.534573 | 3.941 | 5.477 |

  - Schwarzschild-de Sitter at r=10, Lambda=1e-2 gives `g_tt = -0.4667` and
    `g_rr = 2.143`. The repos give -1.1333 and 1.2552.
  - The referee's KdS ISCO at a=0.9 is 2.3224 (Lambda=1e-4) and 2.5625 (Lambda=1e-2).
    Neither repo computes it.
- **INFERRED:** the task premise that "Blackhole lacks Kerr-de Sitter" holds in substance.
  Blackhole has a KdS header and GLSL (`shader/include/verified/kerr_de_sitter.glsl`), but
  it is wrong. gr_core offers the same wrong code, so the fix is a fresh Carter-form
  implementation.

### F6. Blackhole's CPU Kerr ray tracer stalls at radial turning points (Blackhole LATENT; gr_core has the right scheme)

- **Where:** the first-order Mino form `kerr.cpp:47-51` (`sqrt(max(R,0))`) combined with
  the sign-flip rule at `raytracer.h:349-357`. Callers are `tests/physics_test.cpp` and
  `bench/physics_bench.cpp`.
- **OBSERVED (`bh/mino2.cpp`, a=0.9 equatorial ray from r=50, dlambda = 1e-5):**
  - b = 1.001 b_c: the first-order form sits at r = 1.58524 for 4,000,000 steps. That
    radius is the turning point, and the ray never escapes. A second-order form built from
    Blackhole's own `kerrPotentials().dRdr` and `.dThetadtheta` turns at r = 1.58524 and
    escapes in 386,754 steps.
  - b = 1.0001 b_c: the first-order form stalls at 1.56615, while the second-order form
    escapes.
  - b = 0.999 b_c (captured): both agree to 1e-5.
  - Cost: second-order 91 ns/step against 145 ns/step for first-order. The first-order
    count includes the extra potential evaluation that the sign rule needs.
- **Mechanism:** once a step lands where R < 0, every RK4 stage clamps dr/dlambda to 0, so
  the state cannot leave, and the ray ends as MaxSteps (`raytracer.h:371`).
- **gr_core:** `kerr.rs:172-270` uses the second-order form (`d^2 r/dlambda^2 = R'/2`)
  with `u = 1/r` and DOPRI5, which is the correct architecture.

### F7. Blackhole's "energy-conserving" null correction zeroes the radial velocity (Blackhole LATENT; gr_core correct)

- **Where:** `verified/energy_conserving_geodesic.hpp:228-240` and its GLSL copy
  `shader/include/verified/energy_conserving_geodesic.glsl:154-161`.
  - The code scales v^r and v^theta by `sqrt(|m^2/norm|)`. For a null ray, m^2 = 0, so the
    factor is 0 whenever |norm| >= 1e-10.
  - Even for timelike rays, scaling only part of the norm multiplicatively does not
    restore it.
- **OBSERVED (`bh/ecg.cpp`):** a Schwarzschild r=10 null ray with a 1e-6 v^r perturbation
  goes from `v_r = 0.963, norm = 2.3e-6` to `v_r = 0, norm = -1.16`. The correction turns a
  photon into a timelike state.
- **gr_core:** `energy_conserving.rs:242-280` solves the additive form
  `alpha^2 = (target - norm + spatial)/spatial`. The measurement above holds its null norm
  at 3.6e-15. It has been correct since it was created in commit `3b220fb4`.
- **Reach:** the only shader that includes the GLSL copy is `shader/raytracer.frag`. No
  `src/` or CMake file names that shader. INFERRED: it is not loaded; confidence medium.
- This is the one integrator component where open_gororoba holds the correct version and
  Blackhole does not.

### F8. gr_core's Kerr null integrator uses the timelike polar potential (gr_core only)

- **Where:** `kerr.rs:204,269,342` use `Theta = Q - cos^2 (a^2 (1 - E^2) + L^2/sin^2)`,
  which is the mu = 1 form. The null form is `Q + a^2 E^2 cos^2 - L^2 cot^2`, which
  Blackhole's `kerr.cpp:91` has correctly. The test `kerr.rs:1175` repeats the same wrong
  expression, so it is tautological.
- **OBSERVED:** for a=0.9, E=1, L=2, Q=10, `trace_null_geodesic` reaches a polar turning
  point at |cos theta|max = 0.845154. That equals the timelike prediction 0.845154 and
  misses the null prediction 0.851939.
- **Consequence:** off-equatorial photon paths are wrong whenever a != 0, and so is
  `shadow_ray_traced` at theta_obs != pi/2. The analytic Bardeen `shadow_boundary`
  (`kerr.rs:95-165`) is independent of this bug.

### F9. gr_core TaylorF2 phase is missing the 1/eta prefactor (gr_core only; Blackhole correct)

- **Where:** `gravitational_waves.rs:230`, `psi_leading = (3/128)/(pi M f)^{5/3}`, where M
  is the total mass. The standard form is `3/(128 eta v^5)`. Blackhole has it right at
  `gravitational_waves.h:357,476`.
- **OBSERVED:** for 30+30 Msun at 20 Hz, gr_core's `Psi + pi/4` is 2.580. An independent
  TaylorF2 2.5PN evaluation gives 10.319. The ratio is 0.2500 = eta.

### F10. Synchrotron F(x) and G(x) "Fouka & Ouichaoui" polynomial is not a fit (gr_core always; Blackhole GLSL and CUDA fallback)

- **Where:** gr_core `synchrotron.rs:125-160`. In Blackhole, `shader/include/synchrotron_emission.glsl:47-70`
  carries the polynomial, and `synchrotron.h:282-285` keeps it as a fallback. The CPU path
  uses Boost K_{5/3} quadrature, because `synchrotron.h:38` defines
  `PHYSICS_HAS_BOOST_BESSEL`.
- **OBSERVED (mpmath F vs. polynomial):**

| x | 0.01 | 0.1 | 1 | 3 | 10 |
|---|---|---|---|---|---|
| mpmath F | 0.4450 | 0.8182 | 0.6514 | 0.1286 | 1.92e-4 |
| polynomial | 0.4020 | 0.9208 | 1.5667 | 0.6333 | 2.70e-3 |

  - At x = 10 the polynomial jumps by 15x onto the asymptote. G(x) has the same fault:
    0.797 against 0.494 at x = 1.
  - The same G polynomial is the CUDA fallback at `src/cuda/device_physics.cuh:1064-1065`.
    It runs whenever the G LUT texture is absent (`d_tex_synch_g == 0`).
  - gr_core's tests check only the gyrofrequency scaling (`synchrotron.rs:245-295`).
- **INFERRED:** the GLSL copy is dead. No shader entry point includes
  `synchrotron_emission.glsl`; `grmhd_octree.glsl:14` only names it in a comment. The
  confidence rating is medium, and a runtime `#include` resolution trace would settle it.

### F11. Disk Doppler velocity is wrong for a != 0 (both repos), and Blackhole's Laor g-factor drops `1 + a r^{-3/2}`

- **Orbital velocity.** `doppler.h:380-410` and gr_core `doppler.rs:261-285` use
  `v = sqrt(M/(r - 2M + a sqrt(M/r)))`.
  - OBSERVED referee (BPT 1972 eq. 3.10, ZAMO frame): a=0.9, r=3 gives 0.562 against the
    repos' 0.811. a=0.998, r=1.5 gives 0.570 against 1.78c, which the code clamps to 0.99.
    `disk_doppler_boost` then hits its 1000 clamp.
  - The GLSL copy is at `shader/include/doppler_beaming.glsl:79`.
- **Schwarzschild disk.** gr_core `novikov_thorne.rs:206-238` multiplies
  `sqrt(1 - 3/r)` by a flat-space `1/(gamma(1 - beta_los))` with `beta = r^{-1/2}`. That
  counts transverse Doppler twice.
  - OBSERVED: at r=6 the flux factor (g delta)^4 is 0.354 of the local exact value; at
    r=10 it is 0.647.
- **Laor g-factor.** Blackhole `iron_kline.h:91-109` returns
  `sqrt(1 - 3/r + 2a r^{-3/2}) / (1 - sin phi sin i * r/(r^{3/2}+a))`.
  - The face-on value is `1/u^t = sqrt(f)/(1 + a r^{-3/2})`.
  - OBSERVED (`bh/gfac.cpp`) at the ISCO, face-on: 0.707107 at a=0, 0.465270 at a=0.9 and
    0.159896 at a=0.998. The referee gives 0.707107, 0.370868 and 0.092670.
  - At a=0 the forms agree, which is why a Schwarzschild-only test passes.
- **Orbital angular velocity.** gr_core `novikov_thorne.rs:191`
  (`angular_velocity_circular`) takes no spin argument.
  - OBSERVED: at a=0.9, r=3 it gives 0.19245, while Kerr's `1/(r^{3/2}+a)` gives 0.16404
    (Bardeen 1972).
  - Blackhole's `thin_disk.h:195` is labeled Schwarzschild and matches its label.

### F12. `kerrTimeDilation` is static-observer and returns NaN inside the ergosphere; gr_core has no ZAMO or circular-orbit lapse (Blackhole LATENT for rendering)

- **Where:** `kerr.h:348-362`.
- **OBSERVED:**
  - The function returns sqrt(-g_tt) = 0.577350 at r=3 for every spin.
  - At a=0.9, r=1.8, the driver prints `-nan`. The docstring says 0 is returned only
    inside the horizon.
  - The referee's ZAMO lapse `sqrt(Sigma Delta/A)` is 0.6067 at a=0.9, r=3 and 0.3015 at
    r=1.8.
  - The docstring's "simplified" ZAMO formula evaluates to 0.5658 at a=0.9, r=3, which is
    neither the static nor the ZAMO value.
  - gr_core offers `Schwarzschild::time_dilation_factor` only.
- `src/game/kerr_time_field.h:12` already avoids this function.

### F13. At a < 0 the ISCO and photon-orbit functions use opposite sign conventions (both repos)

- **OBSERVED:**
  - `kerrIscoRadius(a=-0.9, prograde=true)` = 2.3209, the orbit co-rotating with the
    hole. `kerrPhotonOrbitPrograde(a=-0.9)` = 3.9103, the orbit along +phi, which counter-rotates.
  - gr_core's `Kerr::isco_prograde` and `photon_orbit_prograde` at a=-0.9 split the same
    way (2.3209 / 3.9103).
  - `novikov_thorne::isco_radius(-0.9)` in both repos returns 8.7174 (signed convention).
- **Consequence:**
  - `generateSpinRadiiLut` (`lut.h:160-166`) stores (ISCO 8.7174, r_ph 1.5579) at
    spin -0.9. That pairs a counter-rotating ISCO with a co-rotating photon orbit. The
    referee's counter-rotating photon orbit is 3.9103.
  - No `.cpp` consumer was found, so this is LATENT.

### Items where the repos agree and are correct

All of the following matched the referee (M=1):

- **Kerr horizons:** r+ = 2, 1.866025, 1.435890 and 1.063214 at a = 0, 0.5, 0.9 and 0.998.
- **Ergosphere:** 2M at the equator.
- **BPT ISCO, prograde:** 6, 4.233003, 2.320883, 1.236971 at a = 0, 0.5, 0.9, 0.998.
- **BPT ISCO, retrograde:** 6, 7.554585, 8.717352, 8.994374 at the same spins.
- **Photon orbits, prograde:** 3, 2.347296, 1.557855, 1.073909 at the same spins.
- **Photon orbits, retrograde:** 3, 3.532089, 3.910268, 3.998222 at the same spins.
- **Frame dragging:** `2Mar/A` in Kerr.
- **Radiative efficiency:** `1 - sqrt(1 - 2/(3 r_isco))` gives 0.05719, 0.08212, 0.15575
  and 0.32099.
- **Surface gravity, Hawking temperature and horizon omega:** the formulas in
  `hawking.h:87-106` and `hawking.rs:70-92` are identical and match
  `kappa = (r+ - r-)/(2(r+^2 + a^2))`. Not executed; transcribed.

## Numeric cross-check table

| Quantity | Inputs (M=1) | Blackhole | open_gororoba | Reference (citation) | Verdict |
|---|---|---|---|---|---|
| r+ | a=0.9 | 1.435890 | 1.435890 | 1.435890 (Kerr 1963) | agree, correct |
| ISCO prograde | a=0.998 | 1.236971 | 1.236971 | 1.236971 (BPT 1972) | agree, correct |
| ISCO "prograde" | a=-0.9 | 2.320883 | 2.320883 | 8.717352 on +phi / 2.320883 co-rotating | convention split (F13) |
| photon orbit "prograde" | a=-0.9 | 3.910268 | 3.910268 | 3.910268 on +phi | inconsistent with ISCO (F13) |
| eta (NT) | a=0.998 | 0.320994 (doc says 0.42) | 0.320994 | 0.320994 (Bardeen 1970) | agree; Blackhole doc and test window wrong |
| T_disk | r=9, a=0, 0.1 Edd, 4e6 Msun | 1.913e7 K | 1.912e5 K | 1.913e5 K (same f(r)) | Blackhole 100x (F3) |
| flux f(r) | a=0.9, 1.5 r_isco | 0.2278 (LUT) | 0.1835 | 0.1198 (Page & Thorne 1974) | both wrong (F1) |
| redshift z at ISCO | a=0.998 | 0 (LUT, bin 0) | n/a | 9.79 circular orbit (Bardeen 1972) | Blackhole wrong (F2) |
| time dilation | a=0.9, r=3 | 0.577350 static | none | 0.606726 ZAMO (Bardeen 1972) | docstring wrong (F12) |
| time dilation | a=0.9, r=1.8 | NaN | none | 0.301511 ZAMO | Blackhole NaN (F12) |
| g-factor face-on | a=0.9, r_isco | 0.465270 (Laor path) | n/a | 0.370868 (Cunningham 1975) | Blackhole wrong (F11) |
| orbital Omega | a=0.9, r=3 | Schwarzschild-labeled only | 0.19245 (no spin argument) | 0.16404 (Bardeen 1972) | gr_core wrong (F11) |
| null-norm correction | Schwarzschild r=10, 1e-6 drift | v_r -> 0, norm -> -1.16 | norm 3.6e-15 | norm 0 with v_r kept | Blackhole wrong (F7) |
| disk v_phi | a=0.9, r=3 | 0.8112 | 0.8112 | 0.5624 (BPT eq. 3.10) | both wrong (F11) |
| (g delta)^4 | a=0, r=6 edge-on | n/a | 0.354 x exact | 1 | gr_core wrong (F11) |
| KN ISCO | a=0, Q=0.9 | 6.405 | 6.405 | 4.5137 (RN cubic) | both wrong (F4) |
| KN omega | a=Q=0.5, r=3 | 0.035424 | 0.035424 | 0.033948 (Carter 1968) | both wrong (F4) |
| KdS r+ | a=0.9, Lambda=0.1 | 1.534573 | 1.534573 | 1.782486 (Carter 1968 quartic) | both wrong (F5) |
| KdS r_c | a=0, Lambda=1e-2 | 17.3205 | 17.3205 | 16.2174 | both wrong (F5) |
| synchrotron F | x=1 | exact on CPU; GLSL 1.5667 | 1.5667 | 0.651423 (Rybicki & Lightman 6.31) | gr_core and GLSL wrong (F10) |
| TaylorF2 Psi + pi/4 | 30+30 Msun, 20 Hz | 3.5PN correct form | 2.580 | 10.319 at 2.5PN (Blanchet 2014) | gr_core low by eta (F9) |
| null polar turning | a=0.9, L=2, Q=10 | correct Theta (kerr.cpp:91) | 0.845154 | 0.851939 (Carter 1968) | gr_core wrong (F8) |
| turning-point pass | a=0.9, b=1.001 b_c | stalls (first-order) | passes (second-order) | turns at 1.58524 and escapes | gr_core scheme right (F6) |

## Integrator measurement (accuracy and cost on one hard ray)

Test ray: a=0.9 equatorial, b = 1.001 b_c (b_c = 2.84442), starting at r=50.

| Integrator | Turns and escapes | Relative drift of E and L | max null norm | ns/step |
|---|---|---|---|---|
| Blackhole `kerrStepMino` + `raytracer.h` sign rule, dlambda=1e-5 | no (stalls at 1.58524) | n/a (E, L are inputs) | n/a | 145 |
| Second-order Mino from Blackhole `kerrPotentials`, dlambda=1e-5 | yes (386,754 steps) | inputs | n/a | 91 |
| gr_core `rk4_geodesic_step`, affine h=0.01 | yes (11,708 steps) | 1.7e-13 / 2.1e-13 | 1.5e-10 | 326 |
| gr_core `energy_conserving_step` | yes (11,708 steps) | 1.7e-13 / 2.0e-13 | 3.6e-15 | 362 |

The nanoseconds per step compare different languages and step parameters. The second-order
Mino row is the only same-code comparison.

`energy_conserving_step` (`energy_conserving.rs:287-310`) is RK4 followed by an additive
rescale of v^r and v^theta that restores the null norm. It leaves v^t and v^phi untouched,
so E and L drift at plain RK4 rates. Despite its name, it does not conserve energy.

Blackhole's same-named header, which predates the gr_core copy, uses the multiplicative
form and destroys null rays (F7). The gr_core version is the one to take: the change is
about 10 lines, and it costs +11% per step.

## Crate triage (accuracy and efficiency axes)

"Novel" modules are judged by one question: does a computational technique reproduce GR at
lower cost or with a tighter bound? A physics claim that does not reduce to GR within a
stated tolerance stays out of the accuracy path.

| Crate / module | License (Cargo.toml) | Accuracy axis | Efficiency axis | Tests | Port verdict |
|---|---|---|---|---|---|
| gr_core `kerr.rs` | MIT | Metric, analytic Christoffels and shadow curve correct. Null Theta wrong (F8) | Second-order Mino + u=1/r + DOPRI5 removes the turning-point stall | Strong: vacuum-Einstein and Kretschmann checks (`kerr.rs:1609,1651`); polar test tautological | Reimplement the scheme in C++ with the null Theta |
| gr_core `metric.rs` | MIT | Generic Riemann/Ricci/Kretschmann by finite differences; an independent referee for any metric | Offline verification only | Christoffel vs. numerical (`kerr.rs:1553`) | Port the idea as a C++ test oracle (Ricci = 0 to a tolerance) for KN/KdS fixes |
| gr_core `kerr_newman.rs`, `kerr_de_sitter.rs` | MIT | Wrong (F4, F5) | n/a | Pin the bugs | Do not port |
| gr_core `novikov_thorne`, `doppler`, `synchrotron`, `hawking`, `penrose` | MIT | Ports of Blackhole with F1/F10/F11 defects; NT temperature units right (F3) | Scalar | Mostly scaling checks | Take only the `C_CGS` fix |
| gr_core `energy_conserving`, `null_constraint` | MIT | Null norm held to 3.6e-15 against 1.5e-10 unprojected; E and L not enforced. Blackhole's version zeroes v^r (F7) | +11% per step over RK4 | Schwarzschild only | Port the additive correction: replaces `applyConstraintCorrection`. Falsifier: `bh/ecg.cpp` keeps v_r = 0.963 and norm ~ 0 |
| gr_core `gravitational_waves` | MIT | TaylorF2 1/eta error (F9); 2.5PN only | Scalar | Monotonicity only | Blackhole's 4.5PN supersedes it |
| gr_core `lyapunov` | MIT | Generic Benettin accumulator, not wired to geodesics | n/a | 3 | The Kerr photon-ring exponent has a closed form (Johnson et al. 2020, Sci. Adv. 6, eaaz1310); implement that directly |
| gr_core `sedenion_geodesic` | MIT | Candidate replacement for the geodesic RHS. Euler position step; the velocity update depends only on `tanh(2Mar/Sigma)` and never on a Christoffel symbol | Two coherence evaluations per step, no geodesic content | Asserts only "velocity changed" | Replaces nothing. OBSERVED (`grx`): at a=0, 1000 steps from r=10 leave v_r at exactly -0.1, with no gravitational acceleration. Falsifier of any GR-accuracy claim: zero deflection at a=0 |
| gr_core `spacetime_algebra` | MIT | Candidate replacement for tetrad and Stokes frame transforms (`newman_penrose.h`, `stokes_transport.h`). Offers Cl(1,3) grade metadata, strings describing products, and a Dirac-spinor z-boost; there is no rotor-apply API for an arbitrary vector or bivector | n/a | Structural | Replaces nothing. Falsifier: a boost along an arbitrary direction applied to a 4-vector, reproducing the Lorentz matrix to 1e-15. No such function exists |
| gr_core `chingon_frame_dragging` | MIT | Candidate replacement for the frame-dragging omega. Returns `omega_KN (1 + alpha tau)`, whose base inherits the missing-Q^2 error (F4) | Adds a 64D algebra evaluation per point | Self-referential | Replaces nothing. Falsifier: any alpha > 0 gives `omega/omega_Carter - 1 = alpha tau != 0` at a=Q=0.5, r=3 |
| gr_core `cd_ladder_force` | MIT | Candidate addition to the geodesic RHS. Adds a drag term for algebra dimension >= 16 and is zero below it | Extra RHS term | Self-referential | Replaces nothing. Falsifier: at alpha > 0 a Kerr photon's E drifts, violating the Killing conservation that `energy_conserving.rs` measures at 1.7e-13 |
| gr_core `adm_algebra_bridge` | MIT | Candidate addition to ADM constraint sources, which Blackhole has no 3+1 path to use. At zero coupling it reduces to standard ADM by construction (`adm_algebra_bridge.rs` header) | Adds stress-energy terms | Self-referential | Replaces nothing. Falsifier: a nonzero coupling that leaves the Hamiltonian constraint of exact Kerr nonzero |
| gr_core `fractal_metric`, `warp_metric`, `nanograv_cd_fit` | MIT | Alternative metrics and fits outside GR | n/a | Self-referential | At most a labeled alternative metric, like `johannsen_psaltis.h` |
| gr_core `adm.rs`, `ppn_constraints.rs` | MIT | Standard ADM decomposition and PPN bounds | n/a | Present | Reference only; Blackhole has no 3+1 path |
| grmhd_core | GPL-2.0-or-later (workspace) | Real finite-volume GRMHD: Kastaun con2prim, HLL, PLM-minmod, CT, RK2 on a fixed Kerr BL grid. `lib.rs:1-6` calls itself "NOT intended as a production astrophysical code" and "for CD analysis". FM torus uses a Schwarzschild `l` (`torus.rs:38`). No shock-tube, Bondi, or convergence-order test | Real CUDA (`kernels_grmhd.cu` 337 LOC, launches at `gpu.rs:162-227`), CubeCL (`cubecl.rs` 807) and Vulkan (`vulkan.rs` 1168) | 59: roundtrips and finiteness | Not a replacement for iharm3d/KORAL/BHAC dumps. Use as a small-torus source only after a Balsara or Komissarov test passes |
| optics_core | MIT | GRIN ray equation, TCMT, Mie; analogue optics, not GR transport | CUDA GRIN (`algebraic_lensing_gpu.rs`) | 198 | Not relevant to accuracy |
| cosmology_core | MIT | FLRW distances, TOV, gravastar, bounce | Scalar | 383 | Not cross-checked (see Not run) |
| tensor_core | MIT | 303 LOC helper | n/a | 3 | Nothing to port |
| gororoba_gpu_cuda | GPL-2.0-or-later | Infrastructure: context and managed memory; no kernels of its own | Real only through consumers | 7 | Nothing to port |
| gororoba_gpu_vulkan | GPL-2.0-or-later | Pipeline and shader-module plumbing | Infrastructure | 6 | Nothing to port |
| gororoba_gpu_cubecl | GPL-2.0-or-later | 142 LOC wrapper | Wrapper | 3 | Not a performance source |
| gororoba_optix | GPL-2.0-or-later | 418 LOC: dlopen `libnvoptix`, function table, device context; no programs, SBT or BVH | Wrapper | 4 | Not a performance source |
| gororoba_view_core / view_raster | GPL-2.0-or-later / workspace | CPU ARGB slicing and blitting | Trivial | 3 / 1 | Nothing to port |

Licensing:

- **gr_core license and dependencies.** gr_core declares MIT but depends on `verified_core`,
  `cd_kernel` and `gororoba_algebra`, which are all GPL-2.0-or-later. Any binary that
  links gr_core is therefore GPL-2.0-or-later, which is compatible with Blackhole's
  GPL-3.0.
- **Relicensing.** The ported modules started life as Blackhole GPL-3.0 code and now carry
  MIT.
  - OBSERVED: `git log --format='%an <%ae>'` on the ported files on both sides shows one
    identity (eirikr / Eirikr Hinngart, the same noreply address). The relicense is
    therefore within the sole author's rights.
  - An outside contribution to those Blackhole files would change that.
- **Reimplementation.** Reimplementing from the cited literature, the path recommended
  below, carries no license question.

## Porting and integration recommendations (ranked by value/cost)

1. **Implement the closed-form Page-Thorne flux and a real efficiency (fixes F1).**
   - Formula: `referee.py:page_thorne_closed`, with roots
     `x_{1,2,3} = 2cos(acos(a)/3 -/+ pi/3)` and `-2cos(acos(a)/3)`.
   - Replace `thin_disk.h:212-270` and `125-127`.
   - Falsifier: agreement with direct quadrature to 1e-6. Continuous normalized peak at 1.592, 1.563,
     1.483 and 1.278 r_isco for a = 0, 0.5, 0.9, 0.998. Neither repo has this, so it is
     reimplemented.
2. **Replace the disk redshift LUT with the circular-orbit g-factor (fixes F2).**
   - Formula: `g = sqrt(1 - 3/r + 2a r^{-3/2}) / (1 + a r^{-3/2} - r^{-1/2} sin(phi) sin(i))`
     in the no-bending limit. The ray-traced form is `g = 1/(u^t (1 - Omega lambda))`
     with the photon's lambda = L/E.
   - Fix `iron_kline.h:103` with the same denominator.
   - Source: Cunningham 1975; Bardeen, Press & Teukolsky 1972. Reimplement; nothing to port.
   - Falsifier: face-on g at the ISCO equal to 0.3709 (a=0.9) and 0.0927 (a=0.998).
   - Cost: under 50 LOC plus a LUT regeneration.
3. **Switch `raytracer.h` to the second-order Mino form (fixes F6).**
   - `kerrPotentials` already returns `dRdr` and `dThetadtheta`.
   - Adopt gr_core's `u = 1/r` and DOPRI5 architecture. Blackhole already has RK45.
   - Keep Blackhole's correct null Theta.
   - Falsifier: the b = 1.001 b_c ray turns at r = 1.58524 and escapes.
   - Measured: 91 ns/step, down from 145 ns/step.
4. **Port gr_core's additive null-norm correction (fixes F7).**
   - This is the one direct port: `energy_conserving.rs:242-280` into
     `verified/energy_conserving_geodesic.hpp:228-240` and its GLSL copy.
   - It is about 10 lines, so reimplement rather than FFI. Both sides share one author, so
     no license question arises.
   - Falsifier: `bh/ecg.cpp` keeps v_r = 0.963 and restores |norm| < 1e-14.
5. **Delete the added charge "correction" from the KN ISCO and add the Q^2 term to g_tphi and omega (fixes F4).**
   - Use `g_tphi = -a sin^2 (2Mr - Q^2)/Sigma` and `omega = a(2Mr - Q^2)/A`.
   - Compute the KN ISCO by root-finding `dE/dr = 0` from the metric, as the referee does.
     No closed form covers a != 0 with Q != 0.
   - Correct the Rocq definitions so the generated GLSL follows.
   - Add a mixed a, Q test point (a = Q = 0.5, r = 3: omega = 0.033948, ISCO = 3.7321).
   - Falsifier: the RN cubic root 5.6066 at Q = 0.5.
6. **Rewrite Kerr-de Sitter in Carter form (fixes F5).**
   - Use `Delta_r`, `Delta_theta` and `Xi` as in `referee.py:kds_eq`. Horizons are the
     real roots of the quartic.
   - Falsifier: SdS `g_tt = -(1 - 2M/r - Lambda r^2/3)`, and horizons
     (2.027794, 16.217355) at a = 0, Lambda = 1e-2.
   - Validate with a C++ port of gr_core's `metric.rs` Ricci-flat-with-Lambda oracle:
     `R_mu_nu = Lambda g_mu_nu` within tolerance.
7. **Fix the NovikovThorneDisk units (F3) and its docstring and test window.** A one-line
   change: `cCgs = ::physics::C`. Narrow the test to |eta - 0.320994| < 1e-5.
8. **Photon-ring Lyapunov exponent.**
   - Implement the closed form for equatorial and spherical Kerr photon orbits
     (Johnson et al. 2020, Bardeen 1973). Schwarzschild reduces to gamma = pi per
     half-orbit.
   - gr_core's `lyapunov.rs` targets nothing here; the closed form is exact and cheap.
9. **Take nothing from grmhd_core for the accuracy path.** Blackhole's HDF5 ingestion of
   iharm3d/KORAL/BHAC dumps remains the better source of GRMHD fields.
   - grmhd_core becomes worth an FFI or CUDA-kernel look only after it passes the
     Komissarov 1999 1D tests and an FM torus with a Kerr `l`. That is a scope decision
     for the user.
10. **Do not take gr_core's GW phase (F9), synchrotron polynomial (F10) or Doppler
   velocity (F11).** Blackhole's CPU versions are already better, except for F11, which
   needs the BPT eq. 3.10 velocity in both repos.

open_gororoba's claims about Blackhole:

- `verified_core/src/monograph/topological_rendering.rs:9-31` describes Blackhole's
  logarithmic wiregrid as matching "the exponential divergence of the spatial metric". It
  also casts chromatic aberration as a "visual surrogate for the Associativity Violation
  Tensor". Both are narrative; neither names a Blackhole file, and the second has no
  physical content.
- `gororoba_cli_physics/src/bin/eht_pathion_separation.rs` defines its own `BlackHole`
  struct. It labels `G M / c^2` as the "Schwarzschild Radius", which is off by a factor of
  2 because it is r_g, not r_s. It makes no claim of compatibility with Blackhole.
- `data_core/.../insights_registry_mirror.rs:90` records that the `ellip` crate replaced a
  hand port of Blackhole's Carlson integrals.
- Blackhole's `docs/plans/local-repos.md` (99 lines) does not mention open_gororoba. The
  only Blackhole note on it is `docs/archive/physics-updates/rendering-research-notes.md:88-100`.
  That note borrows process ideas (SoA layouts, pinned memory, "three independent paths
  must agree") and makes no physics claim. The lineage finding above shows that the two
  repos do not yet supply independent paths for the modules they share.

## Not run

- **Blackhole `ctest` and open_gororoba `cargo test -p gr_core`:** not run. Header and
  crate drivers covered the quantities in question, and the full suites exercise the same
  tautological assertions noted above.
- **GPU crates and grmhd_core kernels:** not run. There was no device step in scope, and
  the verdicts above rest on reading the code (launch sites, kernel files).
- **cosmology_core vs. Blackhole `cosmology.cpp`/`verified/cosmology.hpp` distances, and
  TOV:** not run for lack of time. This is the next cross-check to make, because the same
  Rocq lineage applies.
- **Hawking temperature:** formulas compared by reading only. They are identical and
  correct, but neither side was executed.
- **Whether `synchrotron_emission.glsl` and `doppler_beaming.glsl` are live:** inferred
  from grep over `#include` directives, not from a shader-preprocessor trace.
- **Scratch artifacts** (not part of either repo): `referee.py`, `referee.json`, `bh/gfac.cpp`, `bh/ecg.cpp`,
  `bh/driver.cpp`, `bh/mino2.cpp` and `grx/`, all under
  `/tmp/claude-1000/-home-eirikr-Github-Blackhole/c0a73857-0507-4985-ac50-c6c55d3348bc/scratchpad/`.
