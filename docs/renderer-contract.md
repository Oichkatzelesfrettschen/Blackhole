# Desktop renderer contract

The desktop state stores backend, geodesic model, radiative model, and quality
tier in `RenderState::dispatch.contract`. The startup log and each recorded
frame's JSON sidecar identify those four fields. The default remains the
fragment Kerr path with thin-surface emission and balanced quality. The
legacy beauty tracer remains a labeled fragment-only selection. Compute and
CUDA use the interop geodesic contract. Reference quality integrates at a
0.02 step parameter over twice the affine range of the displayed step
controls, and at least 40 (2001 steps), capped at 20000 steps
(`rendererStepBudget` in `src/render/renderer_contract.h`). Near-critical rays
exhaust a budget by running out of range, so halving the step over the same
range leaves them exhausted: the zoomed rendered-output scene D exhausts 82
pixels at 500 x 0.04, 84 at 1000 x 0.02, and none at 2000 x 0.02. Balanced
uses the displayed step controls; interactive caps steps at 300 and sets a 0.1 step-size floor.
The legacy fragment loop always uses 300 steps and a 0.1 step parameter,
regardless of its quality label.

## Geometry and units

- The camera and sky use a right-handed world frame with +y up. The camera
  basis columns are right, up, and forward. A pixel ray starts in local
  coordinates as `(uv.x * tan(fov/2), uv.y * tan(fov/2), 1)` and the basis
  maps the normalized direction to world coordinates. The vertical UV range
  is [-1, 1], and horizontal UV includes the aspect ratio.
- The interop and CUDA geodesics use a physics frame with spin along +z and
  the disk in the xy plane. Both rotate world `(x,y,z)` to physics
  `(x,-z,y)` and invert with `(x,z,-y)`. The disk midplane is physics z=0;
  cylindrical disk radius is `sqrt(x*x+y*y)`. The legacy beauty fragment
  tracer uses its own world-frame disk convention and does not establish
  geometric parity with interop.
- The shader and CUDA `kerrToCartesian` functions project chart values with
  `(r sin(theta) cos(phi), r sin(theta) sin(phi), r cos(theta))`. The ray
  position is `r*n`. This is a spherical visualization of the geodesic
  chart, rather than the oblate embedding of Boyer-Lindquist coordinates.
  Geodesic state and chart projection must remain distinguishable when
  comparing images or disk crossings.
- Rendered distances use scene units. `blackHoleMass` is the scene mass
  scale `M`; `r_g=M` and `r_s=2M`. The host passes `r_s`, dimensionless
  `a/M`, and the prograde disk ISCO in scene units to fragment, compute,
  and CUDA. The GLSL and CUDA geodesics form `a=0.5*(a/M)*r_s`.
  `blackHoleMass` sent to Hawking shaders is a separate mass in grams.
- The outer Kerr horizon is `r_+=M+sqrt(M*M-a*a)`. The Schwarzschild
  horizon is `r_s`; its photon sphere is `3M=1.5r_s`. A Kerr photon region
  is spin and orbit-sense dependent, so the Schwarzschild photon-sphere
  radius is a visual/step-refinement reference rather than a Kerr
  critical-curve measurement. The prograde disk ISCO comes from
  `physics::kerrIscoRadius`; `3r_s` applies only at zero spin.

`camera_math_test` checks camera axes, the typed default and reference
budget, plus the GL/CUDA frame rotations, chart projection, and ISCO uniform
declarations. `physics_test` checks horizon, photon, and spin-dependent ISCO
values. Shader validation compiles the GL paths, and the CUDA build compiles
the device paths. Those checks do not measure rendered critical curves,
terminal-class frequencies, or image quality.

## Promotion boundary

The shared terminal identifiers in `shader/include/ray_terminal.h` include
horizon, escape, disk hit, maximum-step exhaustion, non-finite state, and
invariant failure. The fragment and compute paths write one terminal code per
pixel to an SSBO. The host folds the codes into per-frame counts and writes
them to PNG and PFM JSON sidecars. The diagnostics panel displays the counts
and offers a color-coded terminal map; the map is off at startup. CUDA and
non-black-hole scenes report unavailable counts as JSON `null`. The GL-free
`terminal_counts_test` checks the fold, and `kerr_shader_capture_test` checks
the attachment on a GL 4.6 host. Default promotion requires rendered-output
gates, controlled scene metrics, GPU performance measurements, and before/after
captures.
