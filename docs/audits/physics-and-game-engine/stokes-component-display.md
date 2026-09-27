# Polarization components, device cost, and observer-sky reconstruction

The useful connection between multidimensional algebra and rendering is a
choice of representation: store the quantities that the next operation needs,
preserve the relevant invariant, and avoid reconstructing discarded coordinates.
Blackhole's polarization display provides a small, executable application.
Observer-sky pixel integration offers a larger follow-on experiment.

## Source boundary

The investigation used Blackhole base
`91a86b5f63e133f4d6f6712e2b542c48a2e6e982` and read-only open_gororoba
`006230b603c2f1705a72c6bb32348833abfb4565`.

The donor's `crates/gororoba_algebra/src/physics/quat_rotation.rs` expresses
rotations with quaternion components and provides a direct matrix formula for
batch use. Its `crates/gr_core/src/photon_graviton/quadrature.rs` implements
weighted Gaussian integration and compares fine and coarse orders. These are
representation and error-control patterns. The implementation below derives
its formula directly; it copies neither donor code nor donor physical models.

The [earlier numerical audit](05-open-gororoba-novel-numerics.md) already
investigated exact Stokes propagation, Carlson integrals, precision tiers,
compensated accumulation, and transform compression. Live source contains
`src/physics/stokes_exact.h` and the quaternion-pair SO(4) implementation in
`src/render/tesseract/so4.h`. Their presence is existing work, rather than a new
result of this investigation. Runtime adoption requires checking each caller;
a numerical reference header alone establishes a narrower boundary.

## Implemented: remove the polarization angle round trip

The linear polarization is the complex quantity

\[
z=Q+iU=L\exp(2i\chi),\qquad L=\sqrt{Q^2+U^2}.
\]

The factor of two records the fact that rotating a polarization direction by
180 degrees gives the same direction. Blackhole's visualization reconstructs
the angle, then immediately evaluates its sine and cosine. For admitted
positive intensity, the clamped display weights simplify to

\[
\min(L/I,1)(\cos 2\chi,\sin 2\chi)
=\frac{(Q,U)}{\max(I,L)}.
\]

The GLSL `stokesDisplayColor` and CUDA `d_stokes_display_color` now evaluate the
right-hand side. The implementation divides all three components by
`max(I, abs(Q), abs(U))` before forming the norm. At least one scaled component
has magnitude one, so the maximum of squared intensity and squared linear
norm lies in `[1,2]` in exact arithmetic. A reciprocal square root of that
maximum supplies the normalization directly. Zero polarization produces zero
linear tint weights directly. Large
finite Q and U values retain their direction when their unscaled squares would
overflow FP32.

Each displayed polarized ray loses one inverse tangent, one sine, and one
cosine at the source level. The scaled norm adds arithmetic. Device compilation,
buffer traffic, and the rest of the frame determine the realized cost.

The implementation preserves the existing backend contracts:

| Behavior | GLSL | CUDA |
|---|---|---|
| Intensity source | Supplied Stokes I | Mean accumulated RGB |
| Darkness rule | Black below `1e-10` | Disable polarization tint at or below `1e-10` |
| Final RGB clamp | `[0,10]` | Lower bound zero |
| Circular indicator | Clamp V/I to `[-0.5,0.5]` | Same |

CUDA's pre-existing RGB sum must remain representable. The scaling protects
the polarization norm, not an already overflowed intensity reduction.
The CPU EVPA API still returns an angle and retains its `atan2` operation.

## Device observations

The local device was an NVIDIA GeForce RTX 4070 Ti, OpenGL 4.6, driver
615.71.09. The Release configuration enabled warnings as errors and CUDA
architecture 89. The benchmark's host-side validation uses value-safe
floating point even in a fast-math configuration.

- All 24 `KerrShaderCaptureTest` tests passed on the GL context.
- All 9 `CudaStokesTest` tests passed on the CUDA device.
- The new GL comparison covers 345 inputs; the new CUDA comparison covers 40.
  Both use an independent double-precision angular oracle. Cases include axes,
  quadrants, zero polarization, saturation, cutoff boundaries, clipping, and HDR.
- `validate-shaders` passed for the shipped shader entry points.
- The GCC 14 ordinary and fast-math/LTO CI replicas each passed 143 tests.

`stokes_display_bench` reads 1,048,576 deterministic Stokes/color samples and
writes one RGBA output per sample. Eight warmup pairs precede 31 timed pairs;
lane order alternates. `GL_TIME_ELAPSED` measures the dispatch and its memory
barrier. The benchmark reads both output buffers and checks agreement. The
angular GLSL reference's undefined zero-Q cases are excluded from the reference
difference; every Cartesian output still receives a finite-value check.

| Formulation and run | Angular median, ms | Cartesian median, ms | Median paired angular/Cartesian |
|---|---:|---:|---:|
| Square root then division, first | 0.064512 | 0.072704 | 0.906250 |
| Square root then division, repeat | 0.063488 | 0.071680 | 0.900000 |
| Reciprocal square root, first | 0.065536 | 0.062464 | 1.056604 |
| Reciprocal square root, repeat | 0.065536 | 0.064512 | 1.017241 |

The intermediate square-root/division version regressed despite removing
trigonometric calls. Moving the squared maximum inside a reciprocal square
root eliminated the extra normalization division. The final runs measured
paired display-kernel speed ratios of `1.017` to `1.057` and a maximum
defined-domain absolute component difference of `4.76837158e-7`. The small
timing gains apply to this device and workload; whole-frame improvement
remains unmeasured. The numerical improvements are a defined Cartesian result
at the angular singularity and a bounded HDR norm. Operation counts alone
would have missed the intermediate regression.

Replay after the repository's Conan install and ImPlot fetch:

```sh
cmake --preset release -DENABLE_CUDA=ON -DCMAKE_CUDA_ARCHITECTURES=89 \
  -DENABLE_CLANG_TIDY=OFF -DENABLE_CPPCHECK=OFF -DENABLE_BLENDER_BRIDGE=OFF
cmake --build build/Release --parallel "$(nproc)" --target \
  kerr_shader_capture_test cuda_stokes_test stokes_display_bench validate-shaders
ctest --test-dir build/Release --output-on-failure \
  -R '^(cuda_stokes|kerr_shader_capture)$'
./build/Release/stokes_display_bench
```

The test harness can skip unavailable devices. Inspect the test output for
actual execution. The benchmark exits with an error when GL execution is
unavailable.

## What a viewer sees

An unpolarized ray retains its accumulated RGB under the existing backend
cutoffs and clamps. A polarized ray retains the same red/green directional
tint and blue circular indicator within the measured numerical tolerance.
The display encodes polarization for inspection. An unaided human eye does
not see that tint as a direct polarization measurement. The renderer's
geodesic path, emitted spectrum, absorption, and bloom remain separate causes
of physical image accuracy.

## Higher-impact proposal: integrate the light reaching each pixel

The observer sky already uses a log-polar bright-patch tile, direction-map
classification, source-footprint filtering, cumulative CMB ring flux, and a
single-pixel deposit for the unresolved inner patch. Relevant boundaries are
`readDirectionMap`, `tileSample`, `tileFluxInside`, and `main` in
`shader/observer_sky.frag`, plus flux preparation and double-precision pixel
projection in `src/render/observer_sky_view.cpp`.

The unresolved branch assigns the inner patch's flux to the pixel containing
its center. As the center crosses a pixel boundary, the receiving pixel
changes. The resolved branch also evaluates a center direction and sometimes
selects a nearest classified texel. A diagnostic render must distinguish those
mechanisms before attributing the supplied screenshots' blockiness to either.

The desired pixel value before display mapping is

\[
\bar L_p=\frac{1}{\Omega_p}\int_{\Omega_p}L(\omega)\,d\Omega.
\]

A bounded prototype retains flux per existing tile cell, projects each cell's
finite footprint, and distributes its flux with nonnegative overlap weights.
Visible-pixel weights plus off-screen coverage sum to one. Mixed escape/shadow
cells receive extra boundary classification before smooth quadrature applies.
The donor's fine/coarse Gaussian integration pattern estimates error in the
smooth Jacobian and radiance portions. Coarse/fine agreement is an estimator,
so a separately converged reference remains necessary.

The implementation must replace the old unresolved contribution in its region
to prevent double counting, and integrate radiance before `displayMapped`.
Tone mapping is nonlinear: averaging displayed colors generally differs from
displaying the average received radiance.

Proposed acceptance experiment, with fixed LUT and observer parameters:

1. Disable bloom and label the patch sampling branches in diagnostic output.
2. Move the camera through one pixel in 32 subpixel increments at wide,
   transitional, and resolving fields of view.
3. Compare retained-flux reconstruction, the existing renderer, and two
   independently refined reference resolutions.
4. Require reference error below the candidate's thresholds; target less than
   0.5% integrated RGB flux error, 0.1-pixel centroid error, and 0.25-pixel
   boundary error over the measured views.
5. Compare source/geodesic evaluation count at matched image error, along with
   CPU preparation time, GPU time, upload bytes, and memory.

The expected computational saving comes from reusing traced flux and spending
extra samples only where a classified footprint exceeds its error budget.
The prototype can cost more than a single lookup; cheaper computation is a
hypothesis relative to converged brute-force supersampling. Conservative
weights cannot recover unresolved sky structure. Any additional optical blur
requires a declared camera response.

## Synthesis

Three connected ideas support further work: represent polarization with its
components, propagate transformations with their preserved structure, and
integrate conserved flux over the receiving pixel. The first is implemented
here, the second already has substantial support in Blackhole, and the third
has a concrete falsifiable experiment. Higher Cayley-Dickson dimensions alone
provide neither a demonstrated renderer speedup nor a physical image model.
