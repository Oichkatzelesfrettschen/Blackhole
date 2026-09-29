# Kerr spacetime structure and how it shapes the accretion flow

The disk a renderer draws is a consequence of five facts about Kerr
spacetime: the horizon and ergosphere fix where matter cannot stay, the
circular-orbit family fixes where it can, the epicyclic frequencies fix where
that orbit is stable and how it oscillates, the Lense-Thirring term fixes what
a misaligned disk does, and null geodesics fix how any of it reaches the
camera. The renderer implements the first and last two for an equatorial disk
and lacks the epicyclic, vertical-structure, plunging-region, and warp
layers. Section 5 maps each item to the tree and gives a build-out for each
gap. Observed appearance (EHT rings, RIAF versus thin disk, color, limb
darkening, the g table) lives in `docs/physics/accretion-flow-appearance.md`
and is cross-referenced, not repeated.

Tags: [CODE] read from the tree at this commit; [PUB] published result;
[CALC] computed for this note (script method stated); [INF] inferred here;
[UNVERIFIED] recalled but not fetched. Units are G = c = M = 1 unless stated,
so r_s = 2 and a is the dimensionless spin. The renderer's scene units use
r_s = 2 as well (`settings.h` camera distance 150 scene units is 75 r_s).

## 1. Kerr spacetime

### 1.1 Metric in Boyer-Lindquist coordinates

[PUB] Kerr 1963; textbook form in Misner, Thorne and Wheeler 1973 (Eq. 33.2)
and Chandrasekhar 1983, The Mathematical Theory of Black Holes (Ch. 6).

    Sigma = r^2 + a^2 cos^2(th)
    Delta = r^2 - 2 r + a^2
    A     = (r^2 + a^2)^2 - a^2 Delta sin^2(th)

    ds^2 = -(1 - 2r/Sigma) dt^2 - (4 a r sin^2(th)/Sigma) dt dphi
           + (Sigma/Delta) dr^2 + Sigma dth^2
           + (A sin^2(th)/Sigma) dphi^2

Structure that follows directly:

- Horizons: Delta = 0 gives r_pm = 1 +- sqrt(1 - a^2). No horizon exists for
  |a| > 1; the renderer clamps |a| at 0.9999 in the Page-Thorne code
  (`K_PAGE_THORNE_MAX_SPIN`).
- Ergosphere: g_tt = 0 gives r_E(th) = 1 + sqrt(1 - a^2 cos^2 th). It touches
  the outer horizon at the poles and reaches r = 2 at the equator for every
  spin. Inside it no observer is static: g_tt > 0.
- Frame dragging: the angular velocity of the zero-angular-momentum
  observers (ZAMOs) is

      omega = -g_tphi / g_phiphi = 2 a r / A.

  At large r, omega -> 2a/r^3 = 2J/r^3, the Lense-Thirring rate that
  reappears as the disk precession frequency in section 3.
- ZAMO lapse alpha = sqrt(Sigma Delta / A). A ZAMO measures photon energy
  E_z = (E - omega L_z)/alpha, which is the pivot of the redshift
  decomposition in section 4.2.

[CODE] `physics::kerrSigma`, `kerrDelta`, `kerrOuterHorizon`, `kerrInnerHorizon`,
`ergosphereRadius`, `frameDraggingOmega`, `kerrZamoLapse` in
`src/physics/kerr.h`; the ZAMO tetrad and lapse-shift primitives in
`src/physics/kerr_observer.h` (`zamoTetrad`, `equatorialFrame`).
`frameDraggingOmega` takes CGS mass and length inputs, not M = 1.

### 1.2 Kerr-Schild coordinates

Boyer-Lindquist coordinates are singular at both horizons, so a tracer that
must cross the horizon uses ingoing Kerr-Schild (KS) coordinates:

    g_mu_nu = eta_mu_nu + (2 r^3 / (r^4 + a^2 z^2)) l_mu l_nu
    l = (1, (r x + a y)/(r^2 + a^2), (r y - a x)/(r^2 + a^2), z/r)
    (x^2 + y^2)/(r^2 + a^2) + z^2/r^2 = 1     (defines r)

The map to Boyer-Lindquist is dt_KS = dt + (2r/Delta) dr and dphi_KS =
dphi + (a/Delta) dr [PUB, Kerr and Schild 1965; standard]. The metric is
regular at r_+, l is a principal null direction, and the flat-space limit is
exact at r -> infinity. A ray tracer gains a Cartesian chart, no pole
singularity at sin th = 0 (only the azimuth rotation offset), and a smooth
horizon crossing.

[CODE] `shader/include/kerr_schild.glsl` (outgoing KS helpers) and the
ingoing-KS Mino tracer in `shader/include/kerr.glsl` (`kerrChartPosition`,
`kerrKsAzimuthOffset`, `kerrDragAndTimeRates`). Tests:
`tests/kerr_schild_test.cpp`, `tests/kerr_shader_capture_test.cpp`.

### 1.3 Null and timelike geodesic constants

Killing symmetries give E = -p_t and L_z = p_phi. The hidden symmetry gives
the Carter constant Q (Carter 1968, [PUB]). With lambda = L_z/E and
eta = Q/E^2 for a photon:

    Sigma dr/dtau  = +-sqrt(R),  R = ((r^2+a^2) E - a L_z)^2
                                     - Delta (Q + (L_z - a E)^2)
    Sigma dth/dtau = +-sqrt(Th), Th = Q - cos^2(th)(L_z^2/sin^2(th) - a^2 E^2)

Mino time dlambda_M = dtau / Sigma separates the equations:
dr/dlambda_M = +-sqrt(R), dth/dlambda_M = +-sqrt(Th). Turning points are
roots of R and Th; a renderer that steps sqrt(max(R,0)) to first order stalls
at every turning point.

[CODE] `physics::kerrStepMino`, `kerrPotentials`
(`src/physics/kerr.h`); float twin `kerrStep`, `kerrProjectOnShell` in
`shader/include/kerr.glsl`; CUDA twin `d_kerr_step`
(`src/cuda/device_physics.cuh`). Tests: `tests/kerr_shader_capture_test.cpp`
(falsifiers named there: an lz^2/sin^2 polar potential shortens R by
Delta L_z^2, and a first-order step stalls at the turning point).

### 1.4 Circular-orbit family (Bardeen, Press and Teukolsky 1972)

[PUB] BPT 1972, ApJ 178, 347. For a prograde (upper sign) or retrograde
(lower sign) circular equatorial orbit:

    Omega = +-1 / (r^{3/2} +- a)
    E = (r^{3/2} - 2 r^{1/2} +- a) / (r^{3/4} sqrt(r^{3/2} - 3 r^{1/2} +- 2a))
    L = +-(r^2 -+ 2a r^{1/2} + a^2) / (r^{3/4} sqrt(r^{3/2} - 3 r^{1/2} +- 2a))
    u^t = (1 +- a r^{-3/2}) / sqrt(1 - 3/r +- 2a r^{-3/2})

A timelike circular orbit exists only where the square root is real, i.e.
outside the photon orbit; the family therefore has three radii that a
renderer needs in closed form:

    r_ph = 2 (1 + cos((2/3) arccos(-+a)))              photon orbit
    r_mb = 2 -+ a + 2 sqrt(1 -+ a)                     marginally bound
    Z1 = 1 + (1-a^2)^{1/3} ((1+a)^{1/3} + (1-a)^{1/3})
    Z2 = sqrt(3 a^2 + Z1^2)
    r_isco = 3 + Z2 -+ sqrt((3 - Z1)(3 + Z1 + 2 Z2))   marginally stable

Values: a = 0 gives 3, 4, 6; a = 0.9 prograde gives r_ph = 1.557, r_isco =
2.321 [CALC, formulas above; r_isco checked to 5 digits by the script below];
a -> 1 prograde gives all three radii -> 1. The efficiency eta = 1 - E(r_isco)
runs from 5.72% at a = 0 to 42% at a -> 1 [PUB, Novikov and Thorne 1973].

[CODE] `physics::kerrIscoRadius`, `kerrPhotonOrbit` (`kerr.h`);
`kerrCircularOrbit`, `pageThorneIscoRadius`, `novikovThorneEfficiency`
(`page_thorne.h`); `keplerianOmega`, `circularEmitterUt`
(`disk_transfer.h`); `circularOrbit`, `marginallyBoundOffset`,
`photonOrbitOffset` in `kerr_observer.h` with spin-deficit parameterization
for near-extremal spin; float `isco_radius` in
`shader/include/disk_profile.glsl`. Tests: `tests/kerr_observer_test.cpp`,
`tests/disk_transfer_test.cpp`.

### 1.5 Epicyclic frequencies

A circular orbit perturbed radially or vertically oscillates at the epicyclic
frequencies (Okazaki, Kato and Fukue 1987, PASJ 39, 457; Kato 1990;
[PUB], formulas below also in Wagoner 1999, Phys. Rep. 311, 259
[UNVERIFIED as to page]). In M = 1 units with Omega = Omega_phi:

    Omega_r^2     = Omega^2 (1 - 6/r + 8 a r^{-3/2} - 3 a^2/r^2)
    Omega_theta^2 = Omega^2 (1 - 4 a r^{-3/2} + 3 a^2/r^2)

with nu = Omega/(2 pi M) after restoring units. Consequences for disks:

- Radial: Omega_r^2 = 0 exactly at r_isco (definition of marginal stability)
  and is negative inside it. Inside the ISCO a small radial perturbation
  grows, which is why matter plunges rather than orbiting.
- Vertical: Omega_theta sets the restoring force on vertical displacements,
  so it sets the hydrostatic scale height H = c_s / Omega_theta (section
  2.3) and the frequency of vertical corrugation modes.
- Nodal precession: Omega_phi - Omega_theta is the nodal (Lense-Thirring)
  precession rate. It tends to 2a/r^3 at large r and differs from that at
  small r (verified below). It is the frequency at which a tilted ring's
  line of nodes rotates.
- Periastron precession: Omega_phi - Omega_r.
- a = 0 gives Omega_theta = Omega_phi (spherical symmetry, no nodal
  precession).

[CALC] A double-precision `$PYTHON` script (not checked in) checked the formulas:
Omega_r^2(r_isco) is below 1e-17 for a = 0, 0.5, 0.9, 0.998; it is positive
at 1.05 r_isco and negative at 0.95 r_isco for all four spins;
Omega_theta = Omega_phi to 0.0 at a = 0 for r = 6, 10, 100; and for a = 0.9,
(Omega_phi - Omega_theta)/(2a/r^3) = 0.932, 0.979, 0.993 at r = 1e2, 1e3,
1e4. The approach is slow (1 - O(r^{-1/2})), so the weak-field 2a/r^3 is
wrong by 7% at r = 100 M, and at r = 10 M it overstates Omega_LT/Omega_K by
24% (a = 0.9: 0.0458 exact versus 0.0569 from 2a/r^{3/2}).
Nodal period at a = 0.9 [CALC]: M87* (6.5e9 Msun) 390 d at r = 6 M, 1650 d at
10 M, 12200 d at 20 M; Sgr A* (4.3e6 Msun) 372 min at 6 M, 1574 min at 10 M.

[CODE] Not implemented anywhere in `src/`, `shader/`, or `src/cuda/`
(grep for epicyclic, Lense-Thirring precession, Toomre returns only
`docs/physics/lacunae.md`, which counts the frame-drag function as
"Lense-Thirring"). See G5 in section 5.

## 2. Why a disk forms, and where its edges are

### 2.1 Angular-momentum transport

Gas with angular momentum cannot fall in until it sheds it, so it settles
onto the circular orbit of its specific angular momentum and spreads. A
Keplerian disk has d Omega/dr < 0, so it needs a stress coupling adjacent
rings. Two published layers:

- [PUB] Shakura and Sunyaev 1973, A&A 24, 337: parameterize the
  r-phi stress as t_rphi = alpha P with alpha < 1. Then the viscosity is
  nu = alpha c_s H, and the surface density obeys
  dSigma/dt = (3/r) d/dr [ r^{1/2} d/dr (nu Sigma r^{1/2}) ].
- [PUB] Balbus and Hawley 1991, ApJ 376, 214: the magnetorotational
  instability (MRI) is a linear instability of a weakly magnetized
  differentially rotating plasma whenever d Omega^2/d ln r < 0, and its
  nonlinear saturation supplies the stress with alpha ~ 0.01-0.1 in
  simulation. This is the physical origin of the alpha prescription and of
  the turbulence the RIAF/thin-disk images show (see the appearance note,
  section 4).

### 2.2 Radial structure and the inner boundary

Steady-state conservation of rest mass, energy, and angular momentum in the
equatorial plane [PUB] (Novikov and Thorne 1973; Page and Thorne 1974, ApJ
191, 499) gives, with a zero-torque condition at the ISCO, the flux

    F(r) = Mdot f(r) / (4 pi r)     (sqrt(-g) = r in the equatorial plane)
    f(r) = -Omega_,r / (E - Omega L)^2 * integral_{r_isco}^{r} (E - Omega L) L_,r dr

The closed form in x = sqrt(r) with the three roots of x^3 - 3x + 2a = 0 is
the one implemented in `pageThorneFluxShape`. F is exactly zero at r_isco and
peaks at r = 9.6 M for a = 0 (see the appearance note, section 5) with an
r^-3 tail.

The zero-torque boundary is an assumption, and the literature disputes it:

- [PUB] Agol and Krolik 2000, ApJ 528, 161 (arXiv:astro-ph/9908049): a
  magnetic stress at the ISCO transfers extra energy and angular momentum
  from the plunging gas to the disk. With finite ISCO stress the efficiency
  rises (the paper reports a spin-equilibrium efficiency of 36% at
  a = 0.94), the spectrum extends to higher frequency, and limb brightening
  strengthens.
- [PUB] Simulation finds stress and emission inside the ISCO (Zhu et al.
  2012, MNRAS 424, 2504; arXiv id not confirmed). Mummery and Balbus 2022,
  PRL 129, 161101 (arXiv:2209.03579) give exact test-particle inspirals from
  the ISCO with a radial four-velocity of universal form independent of
  spin, which makes the plunging region analytically tractable. An earlier
  Mummery and Balbus 2019 MNRAS paper on the same boundary is cited in
  the literature but not fetched here [UNVERIFIED]. Fits of soft-state
  MAXI J1820+070 spectra find plunging emission dominant at 6-10 keV
  (Mummery et al. 2024, arXiv:2405.09175, as recorded in the appearance
  note).
- [INF] A renderer that clips emission at the ISCO produces a dark ring at
  r_isco whose contrast is set by the model, not by any measurement. The
  physical alternatives are a finite stress parameter delta_isco added to
  the Page-Thorne torque term (Agol-Krolik) or an emissivity that continues
  inside r_isco along the plunging orbit.

[CODE] `pageThorneFluxShape` returns 0 for r <= r_isco;
`bhDiskInnerRadius` returns the ISCO (`interop_trace.glsl`), so both the
flux and the intersection annulus end there. CUDA uses the host-uploaded
`d_isco`.

### 2.3 Vertical structure

Hydrostatic balance in the vertical direction, using the vertical epicyclic
frequency rather than the Newtonian Omega:

    dP/dz = -rho Omega_theta^2 z   =>   H = c_s / Omega_theta,  H/R = c_s/(R Omega_theta)

For Kerr, Omega_theta differs from Omega_phi (section 1.5), by O(2a r^{-3/2})
at large r, but the relativistic thin-disk vertical structure of Novikov and
Thorne 1973 carries an additional vertical-gravity factor that goes to 1
far out [PUB, not re-derived here]. The regimes:

- Gas-pressure dominated outer disk: H/R = (c_s/v_K) rises slowly with r.
- Radiation-pressure dominated inner disk [PUB, Shakura and Sunyaev 1973]:
  H = (3/(8 pi)) (kappa_es Mdot / c) [1 - (r_in/r)^{1/2}] in the Newtonian
  limit. Restoring Mdot = mdot Mdot_Edd with Mdot_Edd = L_Edd/(eta c^2) gives
  H = (3/2)(mdot/eta) r_g, independent of r far from r_in. [CALC by hand from
  the SS73 form.] At mdot = 0.1 and eta = 0.1, H = 1.5 r_g, so H/R
  drops from 0.25 at r = 6 M to 0.075 at r = 20 M. The disk is thickest at
  small radius, opposite to the gas-pressure trend.
- Thick flows (RIAF, MAD): H/R = 0.25-0.3 (Porth et al. 2019, appearance
  note section 3), where the thin-disk equation does not apply.

[CODE] The GLSL RTE and Stokes paths model the disk as a flared Gaussian
layer exp(-z^2/2h^2) with h = `diskScaleHeight` * rho (default H/r 0.03,
`bhDiskScaleHeight` in `interop_trace.glsl`, floored at 0.02 r_s). The CUDA
twin keeps a fixed h = 0.1 r_s (`h_disk` in `device_physics.cuh`); the
legacy path uses `adiskHeight = 0.2`. The flare is a constant H/r: no
Omega_theta profile, no radiation-pressure regime. G4 in section 5.

### 2.4 Outer edge

A thin disk has no intrinsic outer edge (F ~ r^-3). Physical truncation
mechanisms [PUB, standard; not fetched individually]:

- Self-gravity: Toomre Q = Omega_r c_s / (pi G Sigma) falls below 1 at large
  r for gas disks around supermassive holes, and the disk fragments into
  stars (Goodman 2003, MNRAS 339, 937 [UNVERIFIED]); the radius is 1e3-1e4
  r_g for AGN parameters. Note the use of the epicyclic frequency Omega_r in
  Q, not Omega_K.
- Tidal truncation by a companion, at a fraction of the Roche lobe
  (Paczynski 1977 [UNVERIFIED]).
- Feeding: the circularization radius r_circ = l^2/(G M) of the inflow
  (about twice the pericenter for a tidal disruption).

[CODE] The renderer's hard cut at 20 r_s (`BH_DISK_OUTER_RADIUS_RS`,
duplicated in `renderer_contract.h` and `device_physics.cuh` and pinned by
`tests/settings_persistence_test.cpp`) is a compute cap. The appearance note
R1 replaces it with the flux fall-off. This note adds only that the physical
edge is set by Q(r) = 1 and depends on accretion rate, so an adjustable edge
should be exposed as a Toomre or tidal radius parameter, not as a fixed
constant.

## 3. The disk itself warped: tilted disks

### 3.1 Lense-Thirring precession and the Bardeen-Petterson effect

A ring of gas whose orbital angular momentum l is tilted by beta from the
spin axis precesses about the spin at the nodal rate. Weak field:

    Omega_LT(r) = 2 J / r^3 = 2 a / r^3    (M = 1)

(exact rate Omega_phi - Omega_theta from section 1.5.) Because Omega_LT falls
as r^-3, adjacent rings precess at different rates and the disk winds into a
warp unless viscosity or pressure communicates the tilt.

[PUB] Bardeen and Petterson 1975, ApJ 195, L65: viscous coupling between
rings, acting against differential precession, aligns the inner disk with
the hole's equator inside a transition radius r_BP while the outer disk keeps
its original tilt. Consequently the observer sees a disk that is planar at
large r and lies in the spin equatorial plane at small r.

[CALC] Order-of-magnitude r_BP. In the diffusive regime (alpha > H/R) warp
diffuses with viscosity nu_2 = nu_1/(2 alpha^2) (Papaloizou and Pringle 1983
[PUB, ratio recalled, UNVERIFIED]) and nu_1 = alpha (H/R)^2 r^{1/2} in M = 1
units. Equating the precession rate to the warp diffusion rate,
2a/r^3 = nu_2/r^2, gives

    r_BP = (4 alpha a (R/H)^2)^{2/3}    (M = 1)

For alpha = 0.1, a = 0.9, H/R = 0.03 this is 54 M. The GRMHD run of Liska et
al. 2019 at H/R = 0.03 found alignment inside about 5 r_g (arXiv:1810.00883,
as reported in its abstract). The estimate over-predicts by an order of
magnitude, which the source attributes in part to the effective magnetized
viscosity not following the alpha model (this attribution is [INF]). A
renderer must therefore take r_BP as a parameter, not derive it.

### 3.2 Warp propagation regimes

[PUB] Papaloizou and Pringle 1983 (MNRAS 202, 61) treat the warp as
diffusing when alpha > H/R. Ogilvie 1999 (MNRAS 304, 557;
arXiv:astro-ph/9812073) derives the nonlinear warped-disk equations with the
transition: for alpha < H/R a warp propagates as a bending wave at speed
about c_s/2, so the warp is communicated in a sound-crossing time rather than
a viscous time. Consequences for appearance: a wave-like warp lets a disk
precess rigidly as a whole with the mass-weighted rate

    Omega_p = integral Omega_LT(r) L(r) dr / integral L(r) dr,
    L(r) = Sigma r^3 Omega_K   (per dr)

[UNVERIFIED as to the exact weighting; this form appears in Lubow, Ogilvie
and Pringle 2002 and Fragile et al. 2007, not fetched]. Rigid precession is
what the GRMHD tilted runs show for thick disks.

### 3.3 Tearing and simulation

- [PUB] Nixon, King, Price and Frank 2012, ApJL 757, L24 (arXiv:1209.1393):
  when the Lense-Thirring torque exceeds the viscous coupling, the disk
  breaks into rings that precess independently and interact, so a tilted
  disk near a spinning hole tears into discrete annuli.
- [PUB] Fragile, Blaes, Anninos and Salmonson 2007, ApJ 668, 417
  (arXiv:0706.4303): a global GRMHD simulation of a tilted thick disk. The
  disk precesses as a whole (abstract page only).
- [PUB] Liska et al. 2018, MNRAS 474, L81 (arXiv:1707.06619): tilted thick
  discs launch jets along the disk's rotation axis rather than the hole's
  and the inner disk and jet precess. Liska et al. 2019, MNRAS 487, 550
  (arXiv:1810.00883): thin (H/R = 0.03) disk, first MHD demonstration of
  Bardeen-Petterson alignment, inner disk aligned inside about 5 r_g.
  Liska et al. 2021, MNRAS 507, 983 (arXiv:1904.08428): highly tilted thin
  discs tear.

### 3.4 Observational links

- [PUB] Ingram, Done and Fragile 2009, MNRAS 397, L101 (arXiv:0901.1238):
  low-frequency QPOs in black-hole binaries as Lense-Thirring precession of
  the hot inner flow. The QPO frequency is the precession rate, so
  1-10 Hz for a 10 Msun hole corresponds to Omega_LT at the flow's outer
  edge.
- [PUB] Cui et al. 2023, Nature 621, 711 (arXiv:2310.09015): 22 years of M87
  jet monitoring show an approximately 11-year period in the jet position
  angle, read as Lense-Thirring precession of a misaligned disk. [CALC] With
  the 1650 d and 12200 d periods at r = 10 and 20 M above (a = 0.9), an
  11-year (4000 d) period corresponds to a precessing region near r = 14 M,
  so the interpretation needs a rigidly precessing region with a
  mass-weighted radius near 14 M (the weighting of section 3.2).

### 3.5 An evaluable warped-disk surface

A renderer needs z = z(rho, phi, t) or an implicit F(x, t) = 0. Use spin
along +z. Let l(rho, t) be the local unit normal to the disk, parameterized
by tilt beta and twist psi:

    l = (sin(beta) cos(psi), sin(beta) sin(psi), cos(beta))
    beta = beta(rho),  psi = psi(rho, t)

The local disk plane is l . x = 0, giving the exact per-ring form

    z = -rho tan(beta(rho)) cos(phi - psi(rho, t))    (rho cylindrical, phi spin-frame azimuth)

For beta <~ 0.3 rad, z ~ -rho beta cos(phi - psi). The disk is at z = 0
where beta = 0 and reproduces today's equatorial surface exactly. Sign check:
the normal leans toward azimuth psi, so the disk is lower on that side.

Profiles [INF, parametrized from section 3.1-3.3, not fitted]:

    beta(rho) = beta_out * S((rho - r_BP)/w_BP)
    psi(rho, t) = psi_out + Omega_p t + dpsi(rho)
    S(x) = smoothstep(-1, 1, x)   (0 well inside r_BP, 1 outside)

with beta_out the outer tilt, r_BP the Bardeen-Petterson radius (the
parameter of section 3.1), w_BP its width (about r_BP/2), Omega_p the
precession rate of section 3.2 (rigid) or the local Omega_LT(rho) for a
torn or differentially precessing disk, and dpsi(rho) a small twist that
vanishes at large rho. For a torn disk, replace S by a step at r_break and
give each annulus its own psi_i(t) = psi_i0 + Omega_LT(rho) t.

The intersection test changes from a z = 0 sign change to a sign change of

    F(x, t) = z + rho tan(beta(rho)) cos(phi - psi(rho, t))

along the step chord. Inside r_BP the disk is equatorial and the ring
parameterization reduces to z = 0. The precession clock is the Boyer-Lindquist
coordinate time at the emission event, which is why slow-light rendering
(4.3) matters: a ray that carries t_emit lets the disk be evaluated where it
was when the light left.

A ring of tilted orbit is not equatorial, so the disk-transfer g of
`dtDiskTransferG` (a function of lambda = L_z/E only) does not apply: the
photon's full covariant momentum (E, L_z, p_theta, p_r) is needed. Use the
ZAMO tetrad: the emitter has local speed v = v_K(r) along the ring tangent t^
relative to the ZAMO, and

    g = E / (gamma E_z (1 - v n . t^))

with E_z = (E - omega L_z)/alpha and n the photon direction in the ZAMO
frame. See 4.2.

## 4. Light-bending consequences a renderer reproduces

### 4.1 Photon sphere, shadow, and the subring hierarchy

Photon orbits bound the shadow. In Schwarzschild the critical impact
parameter is b_c = 3 sqrt(3) M = 2.598 r_s (the analytic oracle is
`tests/analytic_shadow_size_test.cpp`). For Kerr the shadow edge is Bardeen's
curve (1973), traced by the two equatorial photon orbits and the family
between. The photon ring's subrings are exponentially demagnified with a
factor e^-gamma per half orbit, where gamma is the Lyapunov exponent of the
unstable photon orbit in units of the half-orbit time. Schwarzschild
derivation [CALC by hand]: the Lyapunov exponent of the photon orbit
equals the orbital angular frequency, lambda_L = Omega_c = 1/(3 sqrt(3) M),
and a half orbit takes pi/Omega_c, so gamma = pi and the n-th subring is
e^{-n pi} = 4.3% (n = 1), 0.19% (n = 2) of the previous flux. This matches
Johnson et al. 2020 (appearance note, section 4) and the appearance-note
figure of 13% at a = 1, i = 17 degrees. The Kerr exponent depends on spin
and inclination (Gralla and Lupsasca 2020, "Lensing by Kerr black holes",
arXiv id not fetched [UNVERIFIED]).

The renderer produces higher-order images without extra code by continuing
the geodesic after it misses the annulus. An opaque disk stops at the first
plane crossing inside the annulus (`BH_TERMINAL_DISK_HIT`), so only the
volumetric RTE and Stokes paths, which composite every crossing, show
higher-order disk images over the disk itself. This is physically correct
for an optically thick disk and incorrect for a thin RIAF.

### 4.2 Redshift decomposition

For a photon with conserved E and L_z received at infinity by a static
observer, and an emitter moving with speed v relative to the local ZAMO
(velocity component along phi):

    g = nu_obs/nu_emit = E / E_emit
    E_z    = (E - omega L_z)/alpha                     (ZAMO-frame energy)
    E_emit = gamma E_z (1 - v cos(xi)),  cos(xi) = p_(phi)/E_z, p_(phi) = L_z/varpi

so

    g = [ alpha ]  *  [ 1/(1 - omega lambda) ]  *  [ 1/gamma ]  *  [ 1/(1 - v cos xi) ]
        gravitational   frame dragging            transverse        longitudinal Doppler

with lambda = L_z/E, varpi = sqrt(A/Sigma) sin(th). For an equatorial
Keplerian emitter the product collapses to the BPT form
g = 1/(u^t (1 - Omega lambda)) implemented in `dtDiskTransferG`. In
Schwarzschild alpha = sqrt(1 - 2/r), v = sqrt(1/(r-2)), gamma =
sqrt((r-2)/(r-3)), so alpha/gamma = sqrt(1 - 3/r), the combined
gravitational and transverse factor in the appearance-note g table. The
specific intensity scales as g^3 and the bolometric intensity as g^4
(Liouville). The camera's own state adds a uniform factor 1/sqrt(-g_tt) that
`disk_transfer.h` states the renderer omits, so the sky and disk appear
shifted relative to an observer at infinity, not to the camera.

### 4.3 Time delay: slow light versus fast light

A ray leaving the disk at coordinate time t_e reaches the camera at
t_o = t_e + T(x_e), with T the light-travel time. Two rendering modes:

- Fast light: draw the disk at the observer's t, ignoring T. The image is a
  snapshot of the disk at one coordinate time, as if light were instant.
- Slow light: draw each pixel with the disk state at t_e = t_o - T(pixel),
  so the image contains the light-travel delay across the field of view.
  This is the default in physical ray-tracing codes for time-dependent
  flows (ipole, GRay2 and others [UNVERIFIED as a general statement]).

The difference matters when the disk state changes on the scale of T. [CALC by
hand, flat-space near/far-side delay 2 r sin(i) at i = 85 deg, orbital
period 2 pi r^{3/2}]: at r = 6 M, delay about 12 M out of a period 92 M, so
a phase error of 47 degrees; at r = 20 M, delay 40 M out of 562 M, 26
degrees. A hot spot on the ISCO would be displaced by nearly one eighth of an
orbit between the fast-light and slow-light images, and a precessing warp
(section 3) rotates by Omega_LT T. The delay itself: radial Schwarzschild
delay (r2 - r1) + 2 ln((r2 - 2)/(r1 - 2)); Kerr principal-null delay
`physics::kerr_observer::principalNullDelay`.

[CODE] `kerrStep` accumulates `ray.t += dlam * dt` with the ingoing-KS time
rate `kerrDragAndTimeRates` (`kerr.glsl`), so the coordinate time along the
ray exists. `HitResult` does not carry it (fields: terminal, hitPoint, phi,
photonLambda, minRadius, closest-approach data). The disk's own time
dependence uses the wall-clock `time` uniform times `diskTimeScale`
(default 10 GM/c^3 per wall second), which advances the turbulence pattern
of `disk_turbulence.glsl`; it is independent of any light-travel delay.

## 5. Map against the renderer

Status: done means a shipped implementation and a test that pins it;
partial means implemented with a named limitation; missing means absent.
Default path at this commit: `RendererContract` defaults to
`RenderBackend::Fragment` and `GeodesicModel::KerrReference`
(`src/render/renderer_contract.h`), and `uniform_binding.cpp` enables the
interop tracer whenever the geodesic model is not `LegacyBeauty`, so the
Kerr Mino tracer is what a user sees at launch. Older audit notes
(`docs/audits/physics-and-game-engine/01-renderer-accuracy.md`, F1-F5) that
say the Kerr tracer is wrong or that no g-factor exists predate
`kerr_shader_capture_test` and `disk_transfer_shader_test` and are stale on
those points.

| Item | Status | Site and test |
|---|---|---|
| Kerr BL metric, horizons, ergosphere | done | `kerr.h`; wiregrid overlay; `kerr_geodesic_test` |
| Kerr-Schild chart | done | `kerr.glsl`, `kerr_schild.glsl`; `kerr_schild_test` |
| Frame dragging omega, ZAMO lapse and tetrad | done (host) | `kerr.h`, `kerr_observer.h`; `kerr_observer_test`. No GPU use except the zamo redshift LUT fallback (`cuda_zamo_redshift_test`) |
| Circular-orbit E, L, Omega, u^t | done | `page_thorne.h`, `disk_transfer.h`; `disk_transfer_test` |
| Photon orbit, marginally bound, ISCO closed forms | done | `kerr.h`, `kerr_observer.h`, `disk_profile.glsl` `isco_radius` (float twin) |
| Second-order Mino null geodesic, turning points | done | `kerr.glsl` `kerrStep`; `kerr_shader_capture_test`, `cuda_kerr_geodesic_test` |
| Page-Thorne flux, zero-torque ISCO edge | done | `pageThorneFluxShape`, `dtPageThorneShape`; `disk_transfer_shader_test`, `cuda_disk_transfer_test` |
| Orbiting-emitter g, equatorial | done | `diskTransferG`, `dtDiskTransferG` |
| Photon ring and higher-order images | done for RTE/Stokes, partial for the opaque path | `bhAdaptiveStep` refines near the photon sphere; the surface path terminates at the first hit |
| Redshift decomposed (gravitational/drag/transverse/Doppler) | partial | only the product is computed, from lambda; no term-by-term diagnostic view |
| Epicyclic frequencies | missing | nowhere in tree |
| Radial instability inside ISCO / plunging emission | missing | flux is zero at r <= r_isco; no plunging orbit; `analytic_kerr_geodesic.h` and `device_analytic_kerr.cuh` have plunging Kerr geodesics but no render path calls them |
| Finite ISCO stress | missing | |
| Vertical structure H(r) | partial | GLSL RTE/Stokes flare h = `diskScaleHeight` * rho (constant H/r 0.03); CUDA keeps fixed h = 0.1 r_s; no Omega_theta profile |
| Outer edge | partial | thin-surface disk keeps the hard 20 r_s cap in GLSL and CUDA; the GLSL volumetric disk tapers past 20 r_s (`bhDiskTaper`, 8 r_s width, volume to 44 r_s); Toomre and tidal edges missing |
| Tilt, twist, warp, precession | missing | disk plane hard-coded at z = 0 in `bhCheckDiskIntersection`, `d_check_disk`, `bhDiskSegment` |
| Tilted-emitter g (full covariant) | missing | `dtDiskTransferG` is lambda-only |
| Slow-light rendering | partial | `ray.t` integrated in `kerr.glsl`, not exported |
| Hot-spot / QPO time dependence | missing | |
| Observer-sky Kerr sky map | done (separate path) | `observer_sky.frag`, double-precision CPU map |
| Turbulence | partial | log-normal Keplerian emissivity texture `bhDiskTurbulenceFactor` (`shader/include/disk_turbulence.glsl`, `diskTurbulence` default 0.6) on the GLSL interop path; CUDA draws the smooth disk; not a Lee-Gammie field |

Frame: the interop path uses `bhWorldToPhysics(v) = (v.x, -v.z, v.y)`, spin +z and
disk xy; tilt belongs in that frame only, since the legacy path spins about world +y.

### Build-outs, in order

Costs are [INF] design estimates from per-step operation counts; none was
measured.

#### G2. Export the emission time (slow light)

- Equations: t_emit = t_camera - T where T is the coordinate time accumulated
  along the traced (time-reversed) ray to the hit; sign fixed by test.
- Sites: add `float tHit` to `HitResult` (`interop_trace.glsl`, the CUDA
  `HitResult` in `device_physics.cuh`, `ray_terminal.h`) set in
  `bhTraceGeodesic`; shading of any time-dependent disk feature reads it in
  place of `time`. `bhDiskSegment` accumulates over the chord.
- Tests: (1) a=0 flat limit (`gravitationalLensing = 0`): T equals the
  Euclidean distance from camera to hit, to 1e-5. (2) Schwarzschild radial
  ray: T equals (r2-r1) + 2 ln((r2-2)/(r1-2)). (3) Hot spot on r = 10 M,
  i = 85 deg: phase difference between slow and fast light equals the delay
  over the orbital period, 2 r sin(i) Omega. Falsifier: swapping the sign of
  T moves the spot the wrong way.
- Cost: one float per hit, no extra ALU; about 0.

#### G4. Vertical structure H(r)

- Status: partly addressed by the constant-H/r flare `bhDiskScaleHeight`
  (h = `diskScaleHeight` * rho, GLSL only). The physical c_s/Omega_theta
  profile and the radiation-pressure switch remain.
- Equations: h(r) = (c_s/Omega_theta) with c_s from the outer boundary
  H/R = 0.03-0.1 as a parameter; a radiation-pressure switch
  h = (3/2)(mdot/eta) r_g (1 - sqrt(r_in/r)).
- Sites: replace the constant-ratio `bhDiskScaleHeight(rho, r_s)` (and the
  CUDA fixed `h_disk`) with a `bhDiskHeight(rho)` built on Omega_theta; twin
  `d_disk_height` in `device_physics.cuh`; float `omegaTheta` in
  `shader/include/disk_transfer.glsl` and `device_disk_transfer.cuh`.
- Tests: `Omega_theta = Omega_phi` at a=0 (analytic); Omega_theta positive
  and less than Omega_phi for a > 0 at r > r_isco (computed above);
  `h(r)` in the radiation regime constant to 1% for r > 3 r_in. Falsifier:
  Omega_phi used in place of Omega_theta at a=0.9, r=6 M gives H low by
  Omega_theta/Omega_phi = 0.91, a 10% error [CALC].
- Cost: a few flops per RTE step; RTE already integrates the Gaussian.

#### G3. Plunging region and finite ISCO stress

- Equations: extend emission to r < r_isco on the circular-to-plunging
  radial velocity of Mummery and Balbus 2022 (arXiv:2209.03579); or add the
  Agol-Krolik stress term to Page-Thorne torque with parameter delta_isco.
- Sites: `pageThorneFluxShape` and `dtPageThorneShape` (both spin-dependent
  closed forms) get a `deltaIsco` argument; `bhDiskInnerRadius` drops to
  the horizon (or to a photon-orbit-limited floor) when plunge emission is
  on; g must use the plunging four-velocity for r < r_isco, not
  `circularEmitterUt`, which returns 0 there.
- Tests: delta_isco = 0 reproduces the existing flux bit-for-bit (regression
  of `disk_transfer_test`); flux continuous at r_isco; total luminosity
  equals Mdot (1 - E_isco) for zero stress (`novikovThorneEfficiency`) and
  exceeds it for delta > 0. Falsifier: any discontinuity at r_isco in the
  radial flux profile.
- Cost: one extra branch per hit; the plunging g adds an orbit evaluation.

#### G1. Tilted and warped disk

- Equations: sections 3.5 and 4.2.
- Sites: new registry rows in `interop_uniform_registry.h`:
  `diskTiltDeg`, `diskTwistDeg`, `diskWarpRadius`, `diskWarpWidth`,
  `diskPrecessionRate`; CUDA needs matching `BH_LaunchParams` fields, which
  are outside the registry and behind `bh_device_launch_params_abi()`
  (`cuda_kernel_launch_test`). Replace the z = 0 sign test in
  `bhCheckDiskIntersection` with the sign of F; the `bhDiskSegment` chord
  test becomes an intersection with a tilted plane whose normal varies with
  rho. The g factor moves from lambda-only to the full ZAMO-boost form using
  `p_theta` from `KerrConsts`.
- Tests: beta_out = 0 gives an image bit-equal to today's (regression); flat
  limit (`gravitationalLensing = 0`) plane hit equals the analytic
  t = -(l . x0)/(l . d) to 1e-5; nodal rate of a marked ring equals
  Omega_phi - Omega_theta to 1e-3 over 10 periods; tilted-emitter g at
  beta = 0 equals `dtDiskTransferG` to 1e-5; a polar ring (beta = pi/2)
  g at the equator crossing matches the ZAMO-boost value from
  `orbitingTetrad`. Falsifier: precession at 2a/r^3 instead of the exact
  rate is off by 7% at r = 100 M and by 24% at r = 10 M.
- Cost: sincos and a smoothstep per step with the disk tested, and one atan
  per hit; roughly 3-5% of a step (`kerrStep` is the dominant cost). The
  implicit test replaces a sign test, so it does not add a loop.

#### G5. Epicyclic diagnostics and QPO

- Equations: Omega_r, Omega_theta, Omega_LT in section 1.5; drive a hot-spot or
  ring modulation at Omega_LT or Omega_theta; QPO band from the
  Ingram-Done-Fragile picture, f = Omega_LT(r_out)/(2 pi M).
- Sites: new `src/physics/epicyclic.h` (header-only, `noexcept`) with GLSL and
  CUDA twins gated by the same test pattern as `disk_transfer_shader_test`
  and `cuda_disk_transfer_test`; UI readout only.
- Tests: values of section 1.5 to 1e-12 (double) and 1e-5 (float); Omega_r
  zero at `kerrIscoRadius` for a = -0.9..0.998.
- Cost: none to the render loop; a diagnostic. Evaluate Omega_phi - Omega_theta
  in closed form: in float32 both terms approach r^{-3/2} and the 2a/r^3
  difference cancels, as `kerr_observer.h` avoids for the lapse and shift.

#### G6. Physical outer edge parameters

- Toomre Q = 1 and tidal radius feed the appearance-note R1 taper;
  `BH_DISK_OUTER_RADIUS_RS` becomes one registry uniform, collapsing the three
  copies pinned by `settings_persistence_test`.

## References

Fetched (abstract page or search index) unless marked.

- Bardeen, Press and Teukolsky 1972, ApJ 178, 347. Circular orbits, ISCO
  and photon orbit closed forms. [Textbook and journal; not fetched.]
- Bardeen and Petterson 1975, ApJ 195, L65. [Not fetched.]
- Balbus and Hawley 1991, ApJ 376, 214. [Not fetched.]
- Shakura and Sunyaev 1973, A&A 24, 337. [Not fetched.]
- Novikov and Thorne 1973 (Les Houches); Page and Thorne 1974, ApJ 191, 499.
  [Not fetched.]
- Misner, Thorne and Wheeler 1973; Chandrasekhar 1983, The Mathematical
  Theory of Black Holes. [Textbooks; not fetched.]
- Okazaki, Kato and Fukue 1987, PASJ 39, 457; Wagoner 1999, Phys. Rep. 311,
  259. [Not fetched.]
- Papaloizou and Pringle 1983, MNRAS 202, 61. [Not fetched.]
- Ogilvie 1999, MNRAS 304, 557, arXiv:astro-ph/9812073.
- Agol and Krolik 2000, ApJ 528, 161, arXiv:astro-ph/9908049.
- Mummery and Balbus 2022, PRL 129, 161101, arXiv:2209.03579.
- Nixon, King, Price and Frank 2012, ApJL 757, L24, arXiv:1209.1393.
- Fragile, Blaes, Anninos and Salmonson 2007, ApJ 668, 417, arXiv:0706.4303.
- Liska et al. 2018, MNRAS 474, L81, arXiv:1707.06619; Liska et al. 2019,
  MNRAS 487, 550, arXiv:1810.00883; Liska et al. 2021, MNRAS 507, 983,
  arXiv:1904.08428.
- Ingram, Done and Fragile 2009, MNRAS 397, L101, arXiv:0901.1238.
- Cui et al. 2023, Nature 621, 711, arXiv:2310.09015.
- James, von Tunzelmann, Franklin and Thorne 2015, arXiv:1502.03808 (cited by
  `disk_transfer.h`; tetrad and g).
- Zhu et al. 2012, MNRAS 424, 2504; Goodman 2003, MNRAS 339, 937; Gralla and
  Lupsasca 2020; Paczynski 1977. [UNVERIFIED: identifiers not fetched.]
