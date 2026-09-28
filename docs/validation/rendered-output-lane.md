# Rendered-output validation

The `render-output` CTest label measures pixels from the desktop renderer's
fragment path. `render_output_metrics` checks the image analysis on synthetic
arrays without a GL context. `rendered_output_validation` starts the shipping
`Blackhole` executable with `--export-raw-frame` and `--export-frame`, then
reads its HDR PFM, display PNG byte companion (PPM), and terminal PGM. The PFM
is the ray target before bloom and tone mapping; the PNG is the tone-mapped
target. Each export
has a JSON sidecar with the renderer contract, scene, camera, tier, spin,
dimensions, and terminal counts. The image test writes a metrics JSON file and
a fragment/compute difference heatmap in `build/<preset>/render-output-artifacts`.

Run the minimal scene with `PYTHON` set to the configured interpreter:

```sh
PYTHON=${PYTHON:?} scripts/ci/render_output_probe.sh build/Release
```

The probe starts Xvfb, forces Mesa llvmpipe, checks for a GL 4.6 core
context, runs `ctest -L render-output`, and verifies the passing render
receipt. Set `BLACKHOLE_RENDER_FULL=1` for scenes B, C, and D and the
fragment/compute comparison. `BLACKHOLE_RENDER_DISPLAY=existing` uses a
pre-existing display. The test skips without a context when invoked directly;
the probe rejects an unavailable context before it runs CTest.

The one-shot CLI accepts `--reference-scene A|B|C+|C-|D`,
`--reference-backend fragment|compute|cuda`, and
`--reference-quality balanced|reference`. Pair a scene with both export
flags. The scene preset fixes time at zero, a 30 scene-unit camera distance,
a 30-degree vertical FOV, mass length M=1, a 160-pixel window, and a solid
cubemap. The ray target follows the viewport dimensions recorded in the
sidecar. The camera is on the negative world x axis; scene A and D use zero
pitch, while B and C use 30 degrees above the disk plane. Noise, synthetic
photon-sphere glow, Hawking glow, grain, vignette, chromatic aberration, and
bloom are disabled. Scene A has a white sky and no disk. Scene B has a dim
gray sky and thin disk. C+ and C- use the same disk with a/M=+0.6 and -0.6.
Scene D uses the A source with balanced and reference numerical tiers.
Reference tier means 1000 steps at step size 0.02; balanced uses 500 at 0.04.

## Geometric oracle and measurements

For Schwarzschild spacetime, the unstable circular null orbit lies at
`r=3M`. The asymptotic critical impact parameter is `b_c=3 sqrt(3) M`.
The independent CPU projection uses
`x_px=(W/2)+b_x H/(2 D tan(FOV_y/2))` and
`y_px=(H/2)+b_y H/(2 D tan(FOV_y/2))`. Pixel centers are sampled at
`(x+0.5,y+0.5)`; the vertical FOV fixes both axes through the image height.
The A test allows six pixels for finite-camera and numerical integration
effects and two pixels for boundary discretization at the small viewport.
The captured terminal map determines its measured radius and circularity;
the luminance profile independently locates the strongest local edge and
measures the visual limb.

The Kerr CPU oracle samples `physics::criticalImpactParams` across unstable
photon orbit radii and projects Bardeen coordinates
`alpha=-xi/sin(i)` and
`beta=+/-sqrt(eta+a^2 cos(i)^2-xi^2 cot(i)^2)` at inclination `i=60` degrees.
The C test compares displacement magnitude within eight pixels and requires
opposite displacement signs for opposite spins. The world camera uses y-up,
while the Kerr physics chart uses z-up; the measured sign reversal is checked
without assuming the two horizontal axis labels are identical.

The metrics JSON records terminal fractions, radius and diameter, center
offset, circularity, radial luminance, limb peak and width, center/ring ratio,
finite fractions, ranges before and after tone mapping, and stage hashes.
The fragment/compute comparison reports MAE, PSNR, and a structural score
and retains a heatmap. Those backends share GLSL components, so the
comparison establishes plumbing parity. CUDA terminal codes are currently
absent from the desktop terminal SSBO; CUDA pixel parity needs a device and
separate capture evidence.

Scene B requires a localized, nonzero emission limb wider than two pixels
outside the captured center. A hard black matte with a single-pixel
brightness jump fails the width check. The A scene deliberately has a sharp
capture boundary because its source has no emitting disk; that edge alone
does not diagnose the screenshot's source model. The D test compares the
max-step terminal fraction across quality tiers and preserves exhaustion as
its own class. The image test writes a pass receipt only after A assertions
pass. `verify_claims_matrix.py --require-render-passing` accepts the rendered
claim only with that receipt; CTest registration alone records a pending
execution status.

EHT images constrain a broad asymmetric emission ring and central brightness
depression. The emission ring depends on source emissivity and transfer; it
is distinct from the geodesic critical curve and from the narrower
higher-order photon subrings. Successive subrings approach the critical
curve and become exponentially narrower and weaker with order. The small
reference scenes test renderer geometry and source morphology, not EHT
instrument calibration or resolved subring order.

References: Schwarzschild (1916), *Sitzungsberichte der Koeniglich
Preussischen Akademie der Wissenschaften*, 189-196; Bardeen (1973), in
*Black Holes*, ed. DeWitt and DeWitt, 215-239; Event Horizon Telescope
Collaboration (2019), *ApJL* 875 L1, doi:10.3847/2041-8213/ab0ec7;
Event Horizon Telescope Collaboration (2022), *ApJL* 930 L12,
doi:10.3847/2041-8213/ac6674; Gralla, Holz, and Wald (2019),
*Physical Review D* 100 024018, doi:10.1103/PhysRevD.100.024018;
Johnson et al. (2020), *Science Advances* 6 eaaz1310,
doi:10.1126/sciadv.aaz1310.
