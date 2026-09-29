# Rendered-output validation

The `render-output` CTest label measures pixels from the desktop renderer.
`render_output_metrics` checks the image analysis on synthetic arrays without
a GL context. `rendered_output_validation` starts the shipping `Blackhole`
executable with `--export-raw-frame` and `--export-frame`, then reads its HDR
PFM, display PNG byte companion (PPM), and terminal PGM. The PFM is the ray
target before bloom and tone mapping; the PNG is the tone-mapped target.
Each export has a JSON sidecar with the renderer contract, scene, camera,
tier, spin, dimensions, and terminal counts. The image test writes a metrics
JSON file per capture and difference heatmaps for backend comparisons in
`build/<preset>/render-output-artifacts`.

Run the minimal scene with `PYTHON` set to the configured interpreter:

```sh
PYTHON=${PYTHON:?} scripts/ci/render_output_probe.sh build/Release
```

The probe starts Xvfb, forces Mesa llvmpipe, checks for a GL 4.6 core
context, runs `ctest -L render-output`, and verifies the passing render
receipt. Set `BLACKHOLE_RENDER_FULL=1` for scenes B, C, Cd, and D and the
backend comparisons. `BLACKHOLE_RENDER_DISPLAY=existing` uses a pre-existing
display. The test skips without a context when invoked directly; the probe
rejects an unavailable context before it runs CTest. Scene A on llvmpipe and
on an NVIDIA GPU produces identical raw and terminal hashes.

## Reference scenes

The one-shot CLI accepts `--reference-scene A|B|C+|C-|Cd+|Cd-|D`,
`--reference-backend fragment|compute|cuda`, and
`--reference-quality balanced|reference`. Pair a scene with both export
flags. Every scene fixes time at zero, a camera distance of 30 M, a 30-degree
vertical field of view (3 degrees in scene D), mass M = 1 (r_s = 2), a
160-pixel square target
(`K_REFERENCE_SCENE_EXTENT`), and a solid cubemap. Noise, synthetic
photon-sphere glow, Hawking glow, grain, vignette, chromatic aberration,
bloom, the explanation overlay, and the controls overlay are disabled, so
the display bytes hold scene pixels only.

| Scene | Spacetime | Source | Camera pitch |
|-------|-----------|--------|--------------|
| A | Schwarzschild | white sky, no disk | 0 |
| B | Kerr tracer at a = 0 | dim sky, thin disk | 30 degrees |
| C+ / C- | Kerr, a/M = +0.6 / -0.6 | white sky, no disk | 30 degrees |
| Cd+ / Cd- | Kerr, a/M = +0.6 / -0.6 | dim sky, thin disk | 30 degrees |
| D | Schwarzschild | white sky, no disk; 3-degree view aimed at right critical edge | 0 |

The backlit scenes (A, C, D) make the captured region the shadow alone; a
disk would occlude part of it and bias every extent measure.

## Camera model and oracles

`kerrInitGeodesic` (`shader/include/kerr.glsl`) takes the pixel direction as
the coordinate spatial velocity at the camera radius r. A ray at angle psi
from the inward radial then carries `k^r = -cos(psi)` and
`r k^phi = sin(psi)`, the null condition fixes `E = f k^t` with
`f = 1 - 2M/r`, and its impact parameter is

`b(psi) = r sin(psi) / sqrt(cos^2(psi) + f sin^2(psi))`.

For `b_c = 3 sqrt(3) M`, the asymptotic impact parameter of the unstable
orbit at r = 3M, this gives `sin^2(psi) = b_c^2 / (r^2 + (1 - f) b_c^2)`,
and the pinhole maps `tan(psi)` to pixels through `fovScale = tan(fov/2)`:
52.45 pixels at the reference camera. A flat projection `b_c / D` would give
51.7 pixels and a static-observer tetrad 50.7; the coordinate-direction
camera is the model the renderer implements.

The Kerr oracle samples `physics::criticalImpactParams` across the photon
orbit radii and projects Bardeen's `alpha = -xi / sin(i)` and
`beta = +/-sqrt(eta + a^2 cos^2(i) - xi^2 cot^2(i))` at inclination
i = 60 degrees through the same camera map. The screen sign follows from the
camera basis: yaw -90 degrees puts screen right along world +z, which
`bhWorldToPhysics` maps to physics -y, the sky direction of photons with
`L_z < 0` for a camera at azimuth 180 degrees, so +alpha is screen right.
The C test compares the signed bounding-box center, width, and height; a
mirrored spin moves the shadow to the wrong side and fails it.

The emitting disk rotates in physics +phi for either spin sign:
`dtDiskTransferG` uses `Omega = 1 / (r^(3/2) + a)`, which remains positive
at both reference ISCOs. The negative-spin disk is retrograde. With the
camera at physics azimuth 180 degrees, screen right points toward physics
-y, where +phi disk motion recedes. The left disk-hit half should therefore
have greater mean raw luminance for both spins (measured 0.183 against
0.033 at a/M = +0.6 and 0.114 against 0.043 at -0.6). The center column
below the shadow samples the directly viewed near side; its first disk-hit
pixel lies farther from the image center for retrograde spin (51.5 against
22.5 pixels). The Bardeen-Press-
Teukolsky formula gives 3.829 M at a/M = +0.6 and 7.851 M at a/M = -0.6.

## Measurements and tolerances

A captured run from pixel xmin to xmax spans `xmax - xmin + 1` pixels edge
to edge, so each extent carries +-1 pixel of quantization. Scene A holds the
mean terminal radius within 1 pixel of the oracle, the luminance edge within
1.5 pixels (1-pixel radial bins), circularity within 0.02, the center within
0.5 pixel, and the display luminance of escaped pixels within 2/255. Scene C
holds the signed center within 1 pixel and width and height within 1.5.

Scene B anchors the radial profile on the oracle circle, since at a = 0 the
critical curve is image-centered for any inclination while the disk biases
the captured centroid. The lensed disk images of order n >= 1 approach the
critical curve from outside and narrow by about e^-pi per order, so at this
scale the first one is a ring about a pixel wide within a few pixels outside
the curve. The test requires a local maximum of the profile between the
critical radius and 3 pixels outside it, rising at least 10% above the
profile three bins to either side, 1 to 4 pixels wide. A hard black matte
steps from dark to disk with no local maximum and fails the contrast check.
Scene A has a sharp capture boundary because its source has no emitting
disk; that edge alone does not diagnose a source model.

Scene D aims the center ray at the right critical-curve edge using the
coordinate-direction oracle angle. Its 3-degree field of view resolves about
53 pixels per degree across the critical region, against 5.3 in scene A, and
the sidecar records the world-space aim target. The test requires the tier
captures to differ, the reference tier to reduce the max-step fraction or the
center-row critical-edge column error while increasing neither, and no
invalid terminals. The reference tier covers twice the selected affine range
at step 0.02 (`rendererStepBudget`): near-critical rays exhaust a budget by
running out of range, so balanced (500 x 0.04) exhausts 82 pixels, a
same-range 1000 x 0.02 budget exhausts 84, and the reference tier's 2001 x
0.02 exhausts none, with the captured set and the critical edge (0 pixel
error on the center row) unchanged.

The fragment/compute and fragment/CUDA comparisons report MAE, PSNR, and a
structural score and retain heatmaps; scene A's raw frame is 0 or 1 per
pixel, so MAE is the fraction of pixels whose classification differs, held
under 1%. The backends share their GLSL or ported components, so these
comparisons establish plumbing parity. CUDA writes through CUDA-GL interop,
which needs the GL context on an NVIDIA device: the CUDA test skips on any
other vendor, and the desktop refuses a CUDA reference export before
interop initializes. CUDA terminal codes are absent from the desktop
terminal SSBO.

The image test writes a pass receipt only after the scene A assertions pass.
`verify_claims_matrix.py --require-render-passing` accepts the rendered claim
only with a receipt newer than the test sources, binary, and manifest; CTest
registration alone records a pending execution status.

## Default scene

`DefaultSceneDiskStaysLit` renders the desktop's first frame from an empty
working directory, so fresh `Settings` supply the camera (75 r_s out, 5
degrees above the disk plane), the star-field cubemap sky, and the exposure.
It reads the per-pixel terminal map and requires the disk to cover at most
35% of the frame, the shadow to be present, and at most 5% of disk pixels to
fall below 1% of the disk's 99th-percentile raw luminance, which the record
exposure rule displays as black. An opaque disk edge far outside the emitting
radii fails the last check: the disk then hides the sky while its outer
annulus shows no emission. The disk outer edge is `K_DISK_OUTER_RADIUS_RS`
(20 r_s) in `render/renderer_contract.h`, and `settings_persistence_test`
holds the GLSL and CUDA copies equal to it. A settings file written before
`K_PRESENTATION_SCHEMA_VERSION` takes the default camera, sky, and exposure
once on load. Fresh-settings frames at the earlier and the current
defaults: [before](figures/default-scene-before.jpg),
[after](figures/default-scene-after.jpg).

## Scope

EHT images constrain a broad asymmetric emission ring and central brightness
depression. The emission ring depends on source emissivity and transfer; it
is distinct from the geodesic critical curve and from the narrower
higher-order photon subrings, which approach the critical curve and become
exponentially narrower and weaker with order. The reference scenes test
renderer geometry and source morphology, not EHT instrument calibration or
resolved subring order.

References: Schwarzschild (1916), *Sitzungsberichte der Koeniglich
Preussischen Akademie der Wissenschaften*, 189-196; Bardeen (1973), in
*Black Holes*, ed. DeWitt and DeWitt, 215-239; Event Horizon Telescope
Collaboration (2019), *ApJL* 875 L1, doi:10.3847/2041-8213/ab0ec7;
Event Horizon Telescope Collaboration (2022), *ApJL* 930 L12,
doi:10.3847/2041-8213/ac6674; Gralla, Holz, and Wald (2019),
*Physical Review D* 100 024018, doi:10.1103/PhysRevD.100.024018;
Johnson et al. (2020), *Science Advances* 6 eaaz1310,
doi:10.1126/sciadv.aaz1310.
