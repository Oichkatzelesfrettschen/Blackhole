# Observed and simulated appearance of black hole accretion flows

Real accretion flows have no sharp outer edge, no opaque plate, and no orange
color. The resolved images (EHT, GMVA) show a thick ring of lensed, hot,
optically thin plasma; thin-disk theory predicts a flux that falls as r^-3
with no cutoff; the renderer's default (thin Page-Thorne disk, hard edge at
BH_DISK_OUTER_RADIUS_RS = 20 r_s, camera at 75 r_s and 5 degrees above the
plane) reproduces neither. This note separates what is observed, what is
simulated, and what is inferred, and ends with ranked, falsifiable changes.

Tags used throughout: [OBS] measured by an instrument, [SIM] produced by a
simulation, [INF] inferred here from those sources, [CALC] computed for this
note (script method stated), [UNVERIFIED] recalled but not fetched.

## 1. Direct imaging

### M87* (mass 6.5e9 Msun, distance 16.8 Mpc class source)

- [OBS] The 2017 EHT image at 1.3 mm is an asymmetric ring of diameter
  42 +/- 3 uas with a central brightness depression about 10 times fainter
  than the ring (EHT Collaboration 2019, Paper I, arXiv:1906.11238). In
  gravitational units that is roughly 11 GM/c^2 or 5.5 r_s across, and the
  ring is the lensed photon-orbit region, not a disk edge.
- [OBS] The ring persists at 43.9 +/- 0.6 uas across 2017, 2018, and 2021
  while the azimuthal brightness distribution changes from year to year
  (EHT Collaboration 2025, arXiv:2509.24593). The brightness peak wanders
  (2017 to 2018 papers, A&A 681 A79); the size does not.
- [OBS] Linear polarization of the ring drops from about 15% in 2017 to
  about 5% in 2018 and 2021, and the electric-vector pattern changes
  helicity in 2021 (arXiv:2509.24593). Only part of the ring is polarized
  (EHT Paper VII, arXiv:2105.01169). Circular polarization averages below
  3.7% (EHT Paper IX, arXiv:2311.10976). Consequence for rendering: the
  polarized emission is structured and time dependent, not a uniform sheet.
- [OBS] The 3.5 mm GMVA+ALMA+GLT image (Lu et al. 2023, Nature,
  arXiv:2304.13252) shows a ring 8.4 +0.5/-1.1 r_s in diameter, about 50%
  larger and thicker than at 1.3 mm, attributed to a substantial
  contribution from the accretion flow with absorption in addition to the
  lensed ring, and an edge-brightened jet that connects to the ring. The
  longer the wavelength, the larger and more diffuse the emitting region:
  the flow is optically thick at longer wavelengths and thins toward 1 mm.
- [OBS] A 345 GHz VLBI detection exists (Raymond et al. 2024, AJ, "First
  Very Long Baseline Interferometry Detections at 870 um", reported via
  the EHT/CfA news page; arXiv id not verified). No 345 GHz image of M87*
  has been published in the sources fetched here.
- [OBS] What is not seen: no thin, sharply bounded, edge-on-looking plate;
  no resolved outer disk edge; no bright, opaque inner disk. The ring
  brightness is set by hot plasma within a few r_s, and the dark interior
  is 10 times fainter, not black.
- [UNVERIFIED] The ring fractional width quoted in the EHT Paper IV
  (arXiv:1906.11241) as a value below one half; the fetched abstract does
  not state it.

### Sgr A* (mass about 4e6 Msun)

- [OBS] The 2017 image is a thick ring of diameter 51.8 +/- 2.3 uas with
  modest azimuthal asymmetry and a comparatively dim interior, with
  intrahour variability (EHT Sgr A* Paper I, arXiv:2311.08680). The
  dynamical time at the ring is minutes, so the image changes during an
  observing night.
- [OBS] Millimeter light curves show variability down to timescales of
  about a minute and a red-noise character (Wielgus et al. 2022,
  arXiv:2207.06829); the strongest variability follows an X-ray flare.
- [OBS] The ring is strongly polarized with a spiral electric-vector
  pattern, peak fractional linear polarization about 40% in the western
  ring, and 5-10% circular polarization in a dipole pattern (EHT Sgr A*
  Paper VII, ApJL 964 L25, DOI 10.3847/2041-8213/ad2df0; arXiv id not
  confirmed). Paper VIII (DOI 10.3847/2041-8213/ad2df1) reports 24-28%
  resolved linear polarization and reads it as favoring dynamically
  important magnetic fields (verified via search index, not fetched).
- [OBS] Model comparison favors magnetically arrested disks (MAD) with
  inclination i <= 30 degrees and disfavors high inclination, non-spinning,
  or retrograde flows; every model in the library failed at least one
  constraint, variability most often (EHT Sgr A* Paper V,
  arXiv:2311.09478; Paper I, arXiv:2311.08680).
- [OBS] GRAVITY near-infrared interferometry tracks a compact polarized
  hot spot on a loop of about 150 uas at 6-10 gravitational radii with a
  45 +/- 15 min period, at about 30% of light speed (GRAVITY 2018,
  arXiv:1810.12641). The 2023 update reports four astrometric and six
  polarimetric flares, orbits at about 9 r_g, consistent with the known
  mass, and a predominantly vertical magnetic field (GRAVITY 2023,
  arXiv:2307.11821). Later joint fits report clockwise motion on a near
  face-on orbit (inclination 150-160 degrees), from the search index
  (arXiv:2408.07120, not fetched).
- [OBS] Consequence: no imaged flow is near edge-on. Every imaged source is viewed within 30-40 degrees of
  the spin axis (M87 jet angle about 17 degrees; Sgr A* i <= 30 degrees).
  The renderer's near-edge-on default has no imaging analog and rests on
  simulation.

## 2. JWST, X-ray, microlensing, reverberation, and larger scales

- [OBS] JWST NIRCam monitored Sgr A* at 2.1 and 4.8 um for about 48 hours
  over seven epochs in 2023-2024: continuous flickering on few-minute
  timescales, hour-long flares a few times a day, and a low steady
  pedestal; the 4.8 um emission lags and steepens against 2.1 um, which
  indicates synchrotron cooling (Yusef-Zadeh et al. 2025, ApJL,
  arXiv:2501.04096). MIRI detected a flare lasting about 40 minutes
  (arXiv:2511.14836, part II of the mid-infrared series, from the search
  index). Consequence: at IR wavelengths the flow is a flickering point
  source plus flares, and never a resolved disk.
- [UNVERIFIED] Chandra and NuSTAR X-ray flares of Sgr A* are established
  in the literature; no primary source was fetched here. Simultaneous
  JWST/NuSTAR/VLA monitoring appears in arXiv:2512.20786 (search index
  only). The renderer needs only the statement that flares last tens of
  minutes to hours, which the JWST and GRAVITY items above support.
- [OBS] Quasar microlensing gives thin-disk sizes at rest-frame 2500 A
  about a factor 4 larger than the size required to produce the observed
  flux thermally (Morgan et al. 2010, arXiv:1002.4160):
  log(R_2500/cm) = 15.78 +/- 0.12 + (0.80 +/- 0.17) log(M_BH/1e9 Msun).
  Swift/HST reverberation of NGC 5548 finds UV-optical lags following
  tau ~ lambda^(4/3), the thin-disk temperature scaling, but a radius
  about 3 times larger than thin-disk prediction, about 0.35 light days at
  1367 A (Edelson et al. 2015, arXiv:1501.05951). Consequence: real
  luminous-AGN disks emit more from large radii than the Page-Thorne
  profile predicts, so a short outer radius is the wrong direction.
- [OBS] At larger scale, MATISSE mid-infrared interferometry resolves a
  thick dust ring around NGC 1068 (Gamez Rosas et al. 2022, Nature 602,
  403, DOI 10.1038/s41586-021-04311-7). This is the ESO VLTI, not JWST;
  no JWST nuclear-torus image was fetched. The torus is thick and dusty
  and is not the accretion disk.

## 3. Regimes and what each looks like

### Radiatively inefficient flow (RIAF/ADAF/MAD): M87*, Sgr A*

- Hot accretion flows are virially hot, optically thin, and radiate
  inefficiently, with energy advection important (Yuan and Narayan 2014,
  arXiv:1401.0586). [Review; observed as low-luminosity AGN and hard-state
  binaries.]
- [SIM] GRMHD gives a geometrically thick flow: density scale height
  H/R = 0.25-0.3 between r = 10 and 50 r_g in the code-comparison torus
  with a = 0.9375 (Porth et al. 2019, arXiv:1904.04923, Fig. 15 and
  Sec. 5). Strongly magnetized MAD states sit at similar or larger H/R.
- [INF] In visible light such a flow is invisible: the 230 GHz emission is
  synchrotron from electrons at Theta_e = kT_e/(m_e c^2) of order 10 or
  below, and the accretion power is emitted mainly at mm, IR, and X-ray.
  There is no thermal optical continuum and no "color." Any visible-band
  rendering of M87* or Sgr A* is false color mapped from mm intensity.
- [INF] At the renderer's camera (i = 85 degrees) a RIAF would appear as a
  fat, soft-edged, fuzzy torus wrapping the hole, the photon ring and
  lensed emission still dominating near the shadow, and a jet base above
  and below the pole. Not a plate. This is inferred from simulation
  images; no such inclination was imaged.

### Radiatively efficient thin disk: quasars, soft-state X-ray binaries

- [INF/OBS] Optically thick, geometrically thin, blackbody-like locally
  (Page-Thorne/Novikov-Thorne; T_eff ~ r^-3/4 far out). Thin-disk peak
  emission is UV for an AGN (T_peak ~ 1e5 K) and soft X-ray for a
  stellar-mass hole (1e7 K). The optical/visible band comes from the
  cooler outer disk, which per microlensing and reverberation lies at
  larger radii than the standard profile predicts (Sec. 2).
- Real efficient systems add a hot corona, a warm Comptonizing layer,
  disk winds, and in hard states a truncated inner disk (Yuan and Narayan
  2014 for the truncation picture; other sources not fetched).
- [OBS] The intra-ISCO region radiates: fitting the soft state of MAXI
  J1820+070 finds emission from within the ISCO dominant between 6 and
  10 keV for low spin, a hot, small quasi-blackbody component (Mummery et
  al. 2024, arXiv:2405.09175). Simulation shows the stress does not drop
  to zero at the ISCO (Zhu et al. 2012, MNRAS 424, 2504; cited via search
  index, not fetched).
- [INF] Seen near edge-on, an efficient disk is a bright, optically thick
  band with limb darkening, a lensed upper arc over the shadow, and a
  faint lower arc; the corona and wind add diffuse glow above the plane.
  It is the only regime where the renderer's plate is qualitatively
  reasonable, and even there the outer edge is a compute cap.

## 4. GRMHD structure

- [SIM] The EHT/Porth code comparison shows nine codes agree on disk
  structure with agreement improving with resolution (Porth et al. 2019).
  The flow is turbulent with MRI-driven structure, not smooth.
- [SIM] Electron temperature follows the R_high prescription:
  T_p/T_e = R_high b^2/(1 + b^2) + R_low/(1 + b^2), with b = beta/beta_crit
  and beta_crit = 1 (Moscibrodzka, Falcke and Shiokawa 2016, A&A 586 A38,
  arXiv:1510.07243). High beta (disk body) has cool electrons, so the
  bright emission comes from the magnetized funnel wall and inner disk,
  and R_high = 1-100 sets the disk-to-jet contrast. Raising R_high dims
  the disk body.
- [SIM] MAD two-temperature simulations reproduce the M87 spectrum and jet
  power (Chael, Narayan and Johnson 2019, arXiv:1810.01983).
- [SIM] Plasmoid-mediated reconnection ejects magnetic flux bundles that
  orbit as low-density hot spots: dissipation lasts about 30 min and the
  spot orbits for about 150 min for Sgr A* parameters (Ripperda et al.
  2022, ApJL, arXiv:2109.15115). This matches the GRAVITY orbits in
  Sec. 1.
- [SIM] Density fluctuations have broken power-law temporal and spatial
  spectra whose break frequency falls with radius; SANE and MAD differ
  (Hallur et al. 2025, arXiv:2510.09746). Numerical slopes were not
  extracted here.
- [SIM/INF] Radial emissivity: the Broderick et al. RIAF fit uses
  n_e = n_0 (r/r_S)^-1.1 exp(-z^2/2 rho^2) and T_e = T_0 (r/r_S)^-0.84
  (Broderick et al. 2011, arXiv:1011.2770, Eqs. 2-3, as read from the
  PDF). Synchrotron emissivity j ~ n_e B^2 f(Theta_e) with B^2 ~ r^-2
  to r^-2.5 gives j ~ r^-3 to r^-3.5 for an equipartition-like field, an
  inference from the fit above and not a fitted value. The image
  intensity is then integrated along the line of sight with absorption
  that grows toward long wavelengths (Lu et al. 2023).
- [SIM] Photon ring: successive subrings are exponentially demagnified,
  e^-gamma per half orbit, with gamma = pi for Schwarzschild, a factor
  e^-pi about 4%, and up to 13% for a = 1 at 17 degrees (Johnson et al.
  2020, Sci. Adv. 6, arXiv:1907.04329, text of Sec. on flux ratios).
  Only n = 1 is visible in any near-term image; the n = 2 ring is about
  0.16% of n = 0 in flux for Schwarzschild.
- [SIM/INF] Inner edge: emission continues inside the ISCO with a
  plunging-region component (Mummery et al. 2024; Zhu et al. 2012). A
  thin-disk model that drops to zero at r_ISCO leaves a darker ring
  edge that observations and simulations do not show for RIAFs.

## 5. Color and brightness asymmetry

- [CALC] Thin disk, Schwarzschild, Novikov-Thorne/Page-Thorne flux
  integrated numerically in units G = c = M = 1 (E, L, Omega of circular
  orbits; f = -Omega_,r/(E - Omega L)^2 * integral of (E - Omega L)L_,r dr;
  F = f Mdot/(4 pi r)); peak at r = 9.6 M = 4.8 r_s, and relative to the
  peak the flux is 0.35 at 10 r_s (r = 20 M), 0.066 at 20 r_s
  (r = 40 M), 0.023 at 30 r_s, 0.0057 at 50 r_s. Effective temperature
  at the 20 r_s edge is 0.51 of peak. This is the size of the step the
  hard cutoff creates: a jump from 6.6% of peak flux to zero.
- [CALC] Doppler and gravitational factors for a circular orbit seen at
  i = 85 degrees, g = sqrt(1 - 3M/r)/(1 -/+ v sin i) with v = (r - 2M)^
  (-1/2) (local orbital speed), lensing ignored, at the approaching and
  receding tangent points:

  | r (r_s) | g approaching | g receding | I ratio g^3 | bolometric g^4 |
  |---------|---------------|------------|-------------|----------------|
  | 3       | 1.41          | 0.47       | 27          | 79             |
  | 5       | 1.29          | 0.62       | 9.1         | 19             |
  | 10      | 1.21          | 0.75       | 4.2         | 6.8            |
  | 20      | 1.15          | 0.83       | 2.7         | 3.7            |

  The specific-intensity scaling g^3 is Liouville's theorem (James et al.
  2015). The inner disk therefore shows a dynamic range of 30-80 between
  its two sides.
- [OBS-derived] James et al. 2015 (arXiv:1502.03808), from the PDF text:
  the Interstellar disk was a "position-independent temperature T = 4500 K"
  blackbody, "physically thin and marginally optically thick," with
  Doppler shifts omitted in the film because the lopsided disk with them
  was judged too confusing for a mass audience; spin was slowed from 0.999
  to a/M = 0.6; with shifts on, the approaching side is blue and bright
  and the receding side red and dim, "by multiplicative factors of order
  1.5 and 0.4" (Doppler plus about 20% gravitational redshift). The orange
  look is the 4500 K film choice, not physics.
- [INF] Thin-disk color: AGN peak temperature about 1e5 K
  puts the visible band on the Rayleigh-Jeans tail, where color is
  nearly constant blue-white; only the outer parts cooler than about 1e4
  K approach white to yellow. A stellar-mass disk peaks in X-rays and is
  blue-white in the optical. No supported physical case exists for a
  uniform 4500 K orange disk near a black hole. RIAF: synchrotron with no
  intrinsic visible color; any hue is a chosen false-color ramp.

## 6. Renderer state (read from the tree)

- src/settings.h: K_DEFAULT_CAMERA_DISTANCE = 150 scene units = 75 r_s
  (scene r_s = 2), K_DEFAULT_CAMERA_PITCH_DEG = 5.
- shader/include/interop_trace.glsl: BH_DISK_OUTER_RADIUS_RS = 20 (also
  src/render/renderer_contract.h and src/cuda/device_physics.cuh).
- shader/blackhole_main.frag: outerRadius = iscoRadius * 4.0 in the
  legacy path with a linear radial01 falloff; adiskHeight = 0.2;
  emission = density * adiskLit * alpha * abs(noise) * innerBoost with the
  noise factor a product of noiseTexture samples (adiskNoiseLOD octaves).
- shader/include/interop_trace.glsl (Kerr interop path): the thin-surface
  default disk is opaque with the hard 20 r_s edge, shaded by
  `bhDiskEmission` (g^4 F/F_peak bolometric law). The volumetric RTE and
  Stokes disk sets absorption alpha = `rteOpacityScale` * <rho> (GLSL and
  CUDA), flares as h = `diskScaleHeight` * rho (default H/r 0.03,
  `bhDiskScaleHeight`), tapers past 20 r_s as a Gaussian of width
  `BH_DISK_TAPER_WIDTH_RS` = 8 r_s (`bhDiskTaper`, volume out to 44 r_s,
  `bhDiskVolumeOuterRadius`), and advances its pattern on the disk clock
  `diskTimeScale` (default 10 GM/c^3 per wall second). Flare, taper, and
  clock are GLSL only; CUDA keeps the fixed 0.1 r_s layer and the 20 r_s
  edge.
- shader/include/disk_turbulence.glsl: `bhDiskTurbulenceFactor` multiplies
  the Page-Thorne emissivity by a log-normal factor exp(sigma n - sigma^2/2)
  of four-octave value noise sheared at the Keplerian angular velocity;
  uniform `diskTurbulence` (default 0.6, 0 restores the smooth disk). GLSL
  only; CUDA draws the smooth disk.
- The camera sits outside the 20 r_s edge, so the whole disk edge is in
  frame; any taper that starts inside 20 r_s or any cutoff at 20 r_s is
  visible.

## 7. Recommendations, ranked by visual impact

Each entry states the change, its support, and what falsifies it.

### R1. Replace the hard outer edge with the physical flux fall-off

- Status: realized for the volumetric disk, open for the thin surface. In
  the volumetric model the outer Gaussian taper (`bhDiskTaper`) with
  density-proportional absorption delivers the soft edge, because thin
  outer gas is transparent. The thin-surface disk is opaque and its
  bolometric law (`bhDiskEmission`, g^4 F/F_peak) makes an annulus past
  20 r_s nearly black while it still hides the sky, so extending the opaque
  surface works only with a band-limited visible-light intensity law (R4).
- Change: let disk emission be F(r) = Page-Thorne (Novikov-Thorne) flux
  with no outer clip, extend the integration domain to at least
  3 x the camera distance (150+ r_s), and use T_eff = T_peak (F/F_peak)^(1/4).
  If a compute cap is required, apply
  w(r) = exp(-((r - r_c)/w_c)^2) for r > r_c with r_c >= 60 r_s and
  w_c = 20 r_s, so the cap lies below 1e-3 of peak flux and out of frame
  for the default camera.
- Support: [CALC] F(20 r_s)/F_peak = 0.066 and F(50 r_s)/F_peak = 0.0057
  for a = 0; microlensing and reverberation find disks larger, not
  smaller, than the thin-disk profile ([OBS], Morgan 2010, Edelson 2015).
- Falsifier: if the rendered edge at 20 r_s is invisible after the
  default tone map (edge contrast under 1 JND at the chosen exposure),
  the cutoff was already hidden and R1 is cosmetic. Check with the
  per-pixel log-luminance step across r = 20 r_s in the default frame.

### R2. Add an optically thin RIAF/torus volume mode

- Status: partly realized by the flared volumetric disk (`diskScaleHeight`
  * rho, absorption `rteOpacityScale` * <rho>, in the RTE and Stokes
  traces). Remaining: an EHT-calibrated RIAF profile (n_e, T_e, B slopes
  and R_high) and the face-on ring test below.
- Change: volumetric emission along each ray with
  n_e = n_0 (r/r_S)^-1.1 exp(-z^2 / 2 rho^2), rho = H = (0.25-0.3) r
  (Porth 2019 SIM value; MAD equal or larger),
  T_e = T_0 (r/r_S)^-0.84 (Broderick et al. 2011), B^2 ~ r^-2.5, and
  j = n_e B^2 g(Theta_e) with R_high electron temperatures.
  Use r_S here for the Schwarzschild radius as in the paper. Include a
  plunging-region extension inside r_ISCO with density continuity and
  radial infall speed, and absorption coefficient alpha = j / B_nu(T_e)
  for the wavelength of the mode. Camera i = 85 degrees is allowed but
  labeled unimaged.
- Support: [SIM] GRMHD, [SIM/INF] Broderick fit, [OBS] EHT/GMVA rings and
  the 3.5 mm thickness.
- Falsifier: for i = 17 or 30 degrees the rendered ring diameter must land
  within the observed 42 +/- 3 uas (M87) and 51.8 +/- 2.3 uas (Sgr A*)
  scaled by mass and distance, and the brightness contrast between ring
  and interior must be about 10:1. A mode that misses either has wrong
  emissivity slope or absorption.

### R3. Replace the log-normal product texture with a spiral Gaussian random field

- Status: the legacy product texture is superseded by the shipped
  log-normal factor `bhDiskTurbulenceFactor` (`disk_turbulence.glsl`,
  sigma default 0.6, mean 1, Keplerian shear with a cross-faded winding
  period). It is a sheared value-noise texture, not the Lee-Gammie field:
  it has no imposed pitch angle, no correlation time proportional to
  1/Omega_K, and no r-proportional correlation lengths, so the change below
  remains open. It is GLSL only.
- Change: multiplicative fluctuation f(r, phi, t) with local pitch angle
  about 20 degrees (major axis), correlation time lambda_0 proportional
  to 1/Omega_K (about one orbital period), correlation lengths
  lambda_1 proportional to r (a fraction of the local scale height) and a
  fixed anisotropy lambda_2/lambda_1, advected at Keplerian angular
  speed (Lee and Gammie 2021, arXiv:2011.07151, Sec. 4: line-quoted
  "opening angle ... 20 deg", "lambda_0 proportional to 1/Omega_K",
  "lambda_1 proportional to r", sigma = 1). Map to brightness as
  exp(sigma f - sigma^2/2) so the mean is 1; start with sigma_lnI = 1.
  Shear the pattern differentially so no frame is a static image.
- Support: [SIM] Lee and Gammie fit GRMHD-like local shearing-box
  results; the mm modulation index is a red-noise process (Wielgus
  2022); the correlation time is the orbital period near the ISCO
  (about 31 min for Sgr A* and about 34 days for M87* at r = 6 M, [CALC] from 2 pi 6^1.5 GM/c^3).
- Not supported by data: exact sigma. It was not extracted; treat it as
  a tunable and report it.
- Falsifier: a power spectrum of the rendered field that lacks a
  power-law falloff at small scales (Matern-like) or a temporal
  correlation independent of radius contradicts Lee and Gammie and the
  GRMHD break-frequency trend (Hallur 2025).

### R4. Separate thin-disk color from RIAF color

- Thin-disk mode: integrate a blackbody spectrum at T_obs = g T_eff
  through the CIE 1931 matching functions, convert to linear sRGB, and
  scale by g^3 (specific intensity) or g^4 (bolometric). Use
  T_peak = 1e5 K for an AGN scale and a physically fixed mass and
  accretion rate; the visible band then reads blue-white with a cooler
  outer disk. Keep 4500 K orange as a stylized, labeled preset only,
  citing James et al. 2015.
- RIAF/mm mode: map intensity (not temperature) through a documented
  false-color ramp; state in the UI that the hue is chosen.
- Falsifier: for T_peak = 1e5 K the 550 nm/450 nm intensity ratio must
  be within the Rayleigh-Jeans limit (per unit frequency, (450/550)^2 = 0.67), giving a nearly
  achromatic blue-white; if the renderer shows orange for that T, the
  color pipeline is not spectral.

### R5. Tone mapping to hold the beamed/receding dynamic range

- Change: keep an HDR linear buffer, set exposure from the 99th percentile
  of the disk luminance (as the record exposure rule already does), and
  apply a filmic curve with a shoulder. Design target: at the default
  view the fraction of disk pixels clipped at 1.0 stays under 0.5% and
  the receding side remains above the 8-bit floor (its g^4-scaled
  value at 5 r_s is 1/19 of the approaching side, [CALC]).
- Support: [CALC] the approaching-to-receding ratio is 3.7 at 20 r_s,
  6.8 at 10 r_s, 19 at 5 r_s, and 79 at 3 r_s for i = 85 degrees; the
  Interstellar result (factors 1.5 and 0.4 at v about 0.55c) gives a
  brightness contrast of about (1.5/0.4)^3 = 53 to (1.5/0.4)^4 = 198.
- Falsifier: any pixel-count report showing more than 0.5% clipped
  disk pixels, or a receding-side mean below 1/255 in display space,
  means the curve or exposure is wrong.

### R6. Limb darkening for the thin-disk mode

- Change: I(mu) = I_0 (1 + 2.06 mu)/(3.06) with mu = cos of the emergent
  angle, the Chandrasekhar electron-scattering atmosphere law for
  optically thick disks, so an edge-on view is fainter at the limb.
  [UNVERIFIED: standard textbook result; not fetched here.]
- Falsifier: the disk intensity per pixel at i = 85 degrees is
  (1 + 2.06 cos 85)/3.06 = 0.39 of face-on for the same surface flux,
  a factor a plate model without limb darkening lacks.

### R7. Label the near-edge-on default as unimaged

- Change: state in docs and UI that the default 5-degree pitch has no
  imaging analog (every imaged source is within about 30-40 degrees of
  the spin axis) and offer 17-degree (M87-like) and 30-degree (Sgr A*
  like) presets.
- Falsifier: an EHT or GMVA image of a near-edge-on source would
  supersede this.

## 8. Open items

- Extract numeric sigma of log intensity and correlation time from a
  GRMHD run (ipole/iharm3d output) rather than adopting the
  Lee-and-Gammie values.
- Fetch Chandra/NuSTAR flare and JWST torus sources if the X-ray and
  torus appearance become in-scope.
- Confirm the Sgr A* Paper VII arXiv id; only the DOI was verified.

## References

Fetched (abstract page, PDF text, or both) unless marked otherwise.

- EHT Collaboration 2019, First M87 EHT Results I, ApJ 875 L1,
  arXiv:1906.11238. IV: arXiv:1906.11241.
- EHT Collaboration 2021, First M87 EHT Results VII, Polarization of the
  Ring, arXiv:2105.01169.
- EHT Collaboration 2023, First M87 EHT Results IX, Circular
  Polarization, arXiv:2311.10976.
- EHT Collaboration 2024, The persistent shadow of the supermassive black
  hole of M87 I, A&A 681 A79, https://ui.adsabs.harvard.edu/abs/2024A&A...681A..79E
  (search index only).
- EHT Collaboration 2025, Horizon-scale Variability of M87* 2017-2021,
  arXiv:2509.24593.
- EHT Collaboration 2022, First Sgr A* EHT Results I, arXiv:2311.08680;
  V arXiv:2311.09478; VI arXiv:2311.09484 (search index for V).
- EHT Collaboration 2024, First Sgr A* EHT Results VII, ApJL 964 L25,
  DOI 10.3847/2041-8213/ad2df0, and VIII, DOI 10.3847/2041-8213/ad2df1
  (search index only).
- Lu, R.-S. et al. 2023, Nature (2023), arXiv:2304.13252.
- Raymond, A. W. et al. 2024, AJ, First VLBI Detections at 870 um
  (search index only; arXiv id unverified).
- GRAVITY Collaboration 2018, arXiv:1810.12641; 2023, arXiv:2307.11821.
- Wielgus, M. et al. 2022, arXiv:2207.06829.
- Yusef-Zadeh, F. et al. 2025, arXiv:2501.04096; MIRI II
  arXiv:2511.14836, JWST/NuSTAR/VLA arXiv:2512.20786 (search index).
- Morgan, C. W. et al. 2010, arXiv:1002.4160.
- Edelson, R. et al. 2015, arXiv:1501.05951 (search index).
- Gamez Rosas, V. et al. 2022, Nature 602, 403, DOI
  10.1038/s41586-021-04311-7 (search index).
- Yuan, F. and Narayan, R. 2014, arXiv:1401.0586.
- Porth, O. et al. 2019, arXiv:1904.04923.
- Moscibrodzka, M., Falcke, H., Shiokawa, H. 2016, arXiv:1510.07243.
- Broderick, A. E. et al. 2011, arXiv:1011.2770.
- Chael, A., Narayan, R., Johnson, M. D. 2019, arXiv:1810.01983
  (search index).
- Ripperda, B. et al. 2022, arXiv:2109.15115 (search index).
- Hallur, P. et al. 2025, arXiv:2510.09746.
- Lee, D. and Gammie, C. F. 2021, arXiv:2011.07151.
- Johnson, M. D. et al. 2020, arXiv:1907.04329.
- Mummery, A., Ingram, A., Davis, S., Fabian, A. 2024, arXiv:2405.09175.
- Zhu, Y. et al. 2012, MNRAS 424, 2504 (not fetched).
- James, O., von Tunzelmann, E., Franklin, P., Thorne, K. S. 2015,
  arXiv:1502.03808.
- Page, D. N. and Thorne, K. S. 1974, ApJ 191, 499 (not fetched).
