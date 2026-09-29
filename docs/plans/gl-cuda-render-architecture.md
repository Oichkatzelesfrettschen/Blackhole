# OpenGL and CUDA division of labor for the renderer

The renderer runs four tracers that each carry their own copy of the physics,
and the CUDA copy has grown into a second renderer: about 2,400 lines of
`device_physics.cuh` mirror roughly 1,800 counted lines of GLSL, feature by feature,
including shading, sky sampling, and the wiregrid overlay that have no reason
to live in a compute backend. The copies have already drifted in ways that
change the image. The recommendation is a hybrid of options (a) and (b): one
source of physics for the trace and transfer kernels, and a terminal-record
seam that lets CUDA act as a compute service while OpenGL owns all shading and
presentation. That retires about 1,000 lines of CUDA shading without removing
a CUDA capability. Every claim below carries one of three tags.

Tags: [CODE] observed in the tree at this commit (file named); [PUB]
published or vendor-documented; [INF] design inference from those
observations, with its falsifier stated where it drives a decision.

## 1. The four render paths

The user's premise is that OpenGL presents and CUDA computes. The tree
confirms the intent and shows the drift from it.

| Path | Entry | Physics source | Output |
|---|---|---|---|
| Legacy fragment | `blackhole_main.frag` with `interopParityMode = 0` | its own Schwarzschild ray-march and noise-texture disk (`adiskNoiseLOD` loop) | GL framebuffer |
| Interop fragment | `blackhole_main.frag` with `interopParityMode = 1`, includes `interop_trace.glsl` | `kerr.glsl` Mino tracer, `disk_transfer.glsl` | GL framebuffer |
| GL compute | `geodesic_trace.comp`, includes `interop_trace.glsl`, `kerr.glsl`, `wiregrid.glsl` | same as interop fragment | image2D, terminal-code SSBO |
| CUDA | `CudaRenderManager` -> `bh_launch_geodesic_kernel` | `device_physics.cuh` (Kerr Mino twin, own shading) | linear device framebuffer, blit to GL texture |

[CODE] `RendererContract` defaults to `RenderBackend::Fragment` with
`GeodesicModel::KerrReference` (`src/render/renderer_contract.h`), and
`uniform_binding.cpp` (line 203) enables the interop tracer whenever the
geodesic model is not `LegacyBeauty`, so a user gets the interop fragment
path at launch. `main.cpp` (line 1134) documents the CUDA branch as one that
"bypasses both fragment and compute GLSL paths". Two desktop variants exist
beyond the contract: `BLACKHOLE_APP_VARIANT_GLSL_ONLY` and
`BLACKHOLE_APP_VARIANT_CUDA_ONLY` (`main.cpp`, lines 150-158), the second of
which builds the `BlackholeCUDA` executable.

### 1.1 How CUDA output reaches GL

[CODE] `src/cuda/cuda_gl_interop.cu`: the kernel writes a linear
`float4` device framebuffer (coalesced), and `interopBlitToGl` maps the
registered GL texture (`cudaGraphicsGLRegisterImage`, write-discard) and
copies with `cudaMemcpy2DToArrayAsync` on a blit stream.
`cuda_backend.cu` (line 110) calls `cudaStreamSynchronize` on the compute
stream before the blit, so the copy is stream-ordered but the CPU waits for
the kernel. The GL texture is `texBlackhole`, the same target the GLSL paths
render to, so bloom, tone mapping, and presentation are GL for every path.

[INF] Because CUDA already hands GL a finished image and GL post-processes it,
the seam for option (a) is one stage earlier: hand GL the terminal record, not
the colored pixel. Registering a GL buffer with `cudaGraphicsGLRegisterBuffer`
instead of a texture is the documented CUDA-GL buffer interop [PUB, CUDA
runtime API], so no new mechanism is needed.

### 1.2 CUDA structure

[CODE] `src/cuda/` is 5,804 lines. `device_physics.cuh` is 2,730 of them.
Four kernel variants (`kernel_registry.cu`: FP32 baseline, FP32 coarsened,
FP16 storage, FP16 H2 ILP) are chosen by SM version and register budget, in
`kernels_fp32.cu` (441), `kernels_fp16.cu` (271), and `kernels_fp16_h2.cu`
(417). `BH_LaunchParams` (`kernel_launch.h`) is the POD firewall between the
C++23 host and C++17 nvcc, copied to `__constant__` memory field by field;
`bh_device_launch_params_abi()` and `tests/cuda_kernel_launch_test.cpp` keep
the two compilers' layouts equal. `lut_manager.cu` (479) registers GL LUT
textures as CUDA texture objects in slots (emissivity, redshift, spectral, GRB,
galaxy, GRMHD, synchrotron G, GRMHD right).

Dispatch inside the kernel [CODE, `kernels_fp32.cu` lines 49-91]: Stokes if
`d_stokes_enabled`, else volumetric RTE if `d_rte_enabled`, else
`d_trace_geodesic` plus `d_shade_hit`.

### 1.3 The uniform registry and binding

[CODE] `src/render/interop_uniform_registry.h` is an X-macro of 34 float
rows `X(field, glslName, default)` that expands into the `InteropUniforms`
struct, the fragment-path uniform writes, and the compute-path `glUniform1f`
calls. `uniform_binding.cpp` (337 lines) applies it and adds typed specials
(`cameraPos`, `cameraBasis`, `maxSteps`, `iscoRadius`). The header states
what it excludes: the CUDA `BH_LaunchParams` fill, because it applies
semantic transforms (thresholds, bool packing) and has its own ABI guard.
The registry therefore makes the two GLSL paths drift-proof against each
other and leaves the CUDA path as a hand-fanned third copy.

## 2. Who has what

Line counts are per feature and come from function-boundary ranges
(`grep -n` of function starts; each range runs to the next function or
section marker), comments included. They are approximate to about 5% and
are not whole-file counts. The GLSL column sums the shader files named.

| Feature | GLSL lines | CUDA lines | Status |
|---|---|---|---|
| Kerr geodesic integrator (init, Mino step, shell projection) | 366 (`kerr.glsl`) | 397 (`device_physics.cuh` 282-678) | duplicated, twin tests exist |
| Schwarzschild RK4 tracer | 45 (`bhSchwarzschildAccel`, `bhStepRK4`; called by no shader) | 64 (`d_schwarzschild_accel`, `d_step_rk4`) | GLSL copy is dead; CUDA copy runs only if `kerr_enabled = 0` |
| Disk-plane crossing | 22 | 38 | duplicated |
| Trace loop | 130 (`bhTraceGeodesic`) | 167 (`d_trace_geodesic` and photon-lambda helper) | duplicated |
| Disk flux, g, blackbody chroma, emission | 149 (`disk_transfer.glsl` 95, `bhDiskEmission` 54) | 210 (`device_disk_transfer.cuh` 115, `d_disk_emission`/`d_disk_color` 95) | duplicated, tested to C++ |
| Wiregrid overlay | 181 (`wiregrid.glsl`) | 173 (`device_physics.cuh` 781-953) | duplicated |
| Sky and background sampling | 56 (`bhSampleBackgroundLayers`, `bhBackgroundColorFromDir`) | 335 (hash, cubemap, layered equirect by hand, 1313-1647) | CUDA reimplements sampling the GL sampler does in hardware |
| Escaped-sky shaper | not counted (in `blackhole_main.frag`) | 198 | duplicated |
| Hit shading | 47 (`bhShadeHit`) | 111 (`d_shade_hit`) | duplicated |
| Volumetric RTE | 350 (`interop_trace.glsl` 262, `rte_step.glsl` 88) | 391 | duplicated |
| Stokes IQUV transport | 427 (`interop_trace.glsl` 162, `stokes_transport.glsl` 265) | 327 | duplicated |
| GRMHD volume sample | not counted | 56 | duplicated |
| Analytic Kerr (Jacobi elliptic, plunging orbits) | 0 | 504 (`device_analytic_kerr.cuh`) | CUDA only, reached only from tests |
| Disk turbulence | about 25 in the legacy `blackhole_main.frag` octave loop, plus the host FastNoise2 volume | 0 | GLSL only, legacy path only |
| Camera and LUT plumbing | typed uniforms in `uniform_binding.cpp` | about 3,200 (kernels 1,129, launch 583, manager and backend 497, interop 281, LUT manager 613, registry 157) | CUDA host machinery |

Totals over the rows with both counts: about 2,200 CUDA lines against about
1,800 GLSL lines that implement the same features [CODE, arithmetic of the
table]. The CUDA side is larger where it reimplements what the GL pipeline
provides (background sampling, wiregrid, shaping) and smaller nowhere.

### 2.1 Drift found in the tree

Each item is observed; the image effect is stated where it follows.

1. **RTE and Stokes reach only one of four kernels.** `d_rte_enabled` and
   `d_stokes_enabled` are read at `kernels_fp32.cu` lines 49 and 69, in the
   baseline kernel. The coarsened and both FP16 kernels never read them, and
   `bh_launch_geodesic_kernel` does not force the baseline when they are set.
   [INF] On an SM8.9 device the registry auto-selects the H2 ILP variant, so
   enabling RTE or Stokes changes nothing there. Falsifier: launch with
   `rte_enabled = 1` on the auto-selected variant and diff against
   `rte_enabled = 0`; identical output confirms the drift. The existing RTE
   and Stokes tests run the baseline explicitly, which is why they pass.
2. **Dead and live-only-in-tests integrator branches.** GLSL says "one
   integrator for every spin" and never calls `bhStepRK4`. The host sets
   `cp.kerr_enabled = 1` unconditionally (`uniform_binding.cpp` line 268);
   the CUDA Schwarzschild branch (`d_step_rk4`, 64 lines, plus
   `d_kerr_enabled == 0` shaping at `device_physics.cuh` lines 1753 and
   1959) runs only under test.
3. **Two sources for the ISCO.** GLSL computes the inner edge in-shader with
   float `isco_radius(kerrSpin)` (`interop_trace.glsl` line 262); CUDA reads
   the host-computed `d_isco` uploaded in `BH_LaunchParams`. They agree to
   float rounding today, and nothing asserts it.
4. **Shared constants are checked by source scraping.** The disk outer edge
   exists as `BH_DISK_OUTER_RADIUS_RS` (GLSL), `D_DISK_OUTER_RADIUS_RS`
   (CUDA), and `K_DISK_OUTER_RADIUS_RS` (C++). `tests/settings_persistence_test.cpp`
   (lines 200-203) extracts the numbers from the source text and compares
   them. That pins the value and is the strongest cross-language check in
   the tree; it does not extend to functions.
5. **Turbulence exists only in GLSL.** The noise-texture octave loop lives
   in `blackhole_main.frag` (lines 295-310) and reads the host volume; neither
   the interop path nor CUDA has it. A disk-appearance feature written for
   one path is invisible in the others.
6. **CUDA-only code that never renders.** `device_analytic_kerr.cuh` (504
   lines: AGM Jacobi elliptic functions for O(1) photon-ring rays) is
   included by `tests/cuda_analytic_kerr_test.cu` and
   `tests/cuda_geodesic_orbit_test.cu` and by no kernel.
7. **CUDA reimplements the sampler.** The 335-line background block
   reproduces cubemap face selection and layered equirect filtering that the
   fragment and compute paths get from `texture()`; any change to layer
   handling (`background_layer_params`, LOD bias) is made twice.

Findings 1, 3, and 5 change what a user sees or silently drop a requested
feature; 2, 6, and 7 are maintenance cost.

## 3. Parity tests that exist

[CODE] Every twin test compares a GPU implementation against the double
precision C++ reference. No test compares GLSL output against CUDA output.

| Test | What it holds equal | Runs where |
|---|---|---|
| `tests/kerr_shader_capture_test.cpp` | `kerr.glsl` capture edges versus Bardeen and CPU integrator; pole and axis cases | GL 4.6 context |
| `tests/disk_transfer_shader_test.cpp` | `disk_transfer.glsl` versus `physics::pageThorneFluxShape`, `diskTransferG`, `blackbodyChromaLinearSrgb` | GL 4.6 context |
| `tests/cuda_disk_transfer_test.cu` | `device_disk_transfer.cuh` versus the same C++ header | CUDA device |
| `tests/cuda_kerr_geodesic_test.cu`, `cuda_device_physics_test.cu` | device Kerr helpers and end-to-end launches with analytic scenes | CUDA device |
| `tests/cuda_variants_test.cu` | four kernel variants against each other (coarsened within 1e-4 RMSE of baseline) | CUDA device |
| `tests/cuda_rte_test.cu`, `cuda_stokes_test.cu` | baseline-kernel RTE and Stokes properties | CUDA device |
| `tests/cuda_kernel_launch_test.cpp` | `BH_LaunchParams` host/nvcc layout | CUDA build |
| `tests/gpu_cpu_parity_test.cpp` | `shader/include/verified/*` modules versus `src/physics/verified` | GL 4.6 context |
| `tests/glsl_parity_test.cpp` | C++ code that simulates float32 rounding; it does not execute GLSL | plain C++ |
| `tests/wiregrid_overlay_test.cpp` | a C++ port of the GLSL and CUDA overlay math | plain C++ |
| runtime compare sweep (`compare_sweep`, `rs.compare.compareComputeFragment`) | compute path versus fragment path captures in the app | manual, GL |

[CODE] `.github/workflows/ci.yml` contains no CUDA or nvcc step. The lanes are
`ci`, `ci-analysis`, `ci-release`, `ci-clang`, `ci-clang-fast-math`, and
`ci-sanitize`, with a software OpenGL display for the GL-context tests
(`gpu_cpu_parity` and `kerr_shader_capture` are excluded in the sanitizer
lane). `ENABLE_CUDA` defaults to OFF (`CMakeLists.txt` line 345). Every
`cuda_*` test therefore runs only on a developer machine.

[INF] This is the strongest constraint on the choice of architecture. A
2,400-line CUDA shading copy that no required check compiles or runs can
drift on any push; each line retired from it, or moved into a shared source
that CI does compile, removes an unchecked line.

## 4. Options

### (a) CUDA as a compute service, GL owns shading and presentation

CUDA produces geodesic and terminal buffers, sky maps, LUTs, and volumetric
transport. GL turns those into color.

- For: it matches the user's premise; it removes the 1,000 lines of CUDA
  shading and sky sampling (background 335, shaper 198, wiregrid 173, hit
  shading 111, disk color about 210) [INF from the table]; and a new
  appearance feature (turbulence, tilt, slow-light emission time) is written
  once in GLSL. The observer-sky path already works this way: a
  double-precision CPU trace builds a map, and `observer_sky.frag` shades
  from it [CODE].
- Against: a terminal record crossing to GL costs bandwidth and an
  interop sync; volumetric RTE and Stokes fold shading into transport, so
  they resist the split.
- Cost of the record [INF]: a 48-byte record per pixel (terminal code, hit
  point, lambda, emission time, min radius, closest-approach data) at 4K is
  8.3M pixels x 48 B = 400 MB per frame, and a 32-byte record is 265 MB.
  Neither can cross the host; the record must stay on the GPU as a GL buffer
  object that CUDA writes and GL reads with no host copy, and the size
  argues for the 32-byte form. Falsifier: measure the write and read
  time of the buffer on the target device against the shading cost it
  replaces.

### (b) One source for the physics kernels

The trace and transfer functions are pure float functions of a few scalars.
They can live once and compile three ways.

- Precedent in the tree [CODE]: `shader/include/ray_terminal.h` is included by
  `device_physics.cuh` and `main.cpp`; `synchrotron_lut_domain.h` is included
  by GLSL, CUDA, `lut_texture.h`, `synchrotron.h`, and `lut_manager.cpp`;
  `scripts/cpp_to_glsl.py` and `shader/include/verified/` carry a
  Rocq-to-C++-to-GLSL pipeline; `compile_shaders_spirv.sh` targets SPIR-V.
  `disk_transfer` already has three hand-kept twins (C++, GLSL, CUDA)
  each tested against the C++.
- Mechanism [INF]: write the shared functions in the GLSL subset that also
  compiles as C++ (no `inout` semantics that C++ lacks beyond references, no
  swizzle-assignment, `vec3` as a type), and provide a small shim header per
  target: `bh_core_glsl` (identity), `bh_core_cuda.cuh` (a `vec3` struct over
  `float3` with operators plus `mix`, `clamp`, `fract`), `bh_core_cpp.h` (the
  same over `std::array`). Slang, a shading language that emits GLSL, SPIR-V,
  and CUDA, is the off-the-shelf alternative [PUB, Khronos-hosted project; its
  fit to this tree is not evaluated here]; it swaps a hand-written shim for a
  new compiler dependency in the build.
- For: it makes drift structurally impossible for the shared functions, and
  the existing twin tests become tests of one source.
- Against: nvcc float and GLSL float can still differ by FMA contraction and
  transcendental implementations (the repo already traced one compute versus
  fragment divergence to driver FMA at horizon-grazing rays, Issue-009), so a
  parity test is still needed even with one source.

### (c) Retire the duplicated CUDA shading path

Delete the CUDA shading and keep CUDA only for what GLSL cannot do. Without a
measured reason CUDA is worth its lines, this is the cleanest end state. The
data to decide is absent: no GLSL-versus-CUDA frame-time comparison was read
for this note, and the CUDA path is unverified in CI. (c) is therefore the
outcome of stages 0 to 3 below when the measurement says so, and not a first
move.

### Where CUDA does work GLSL cannot

[INF, from the tree] Three things justify a CUDA backend even under (a):

1. Double precision. Float32 near the horizon is a documented gap
   (`docs/physics/lacunae.md`, section 2.7) and the observer-sky path
   already avoids it on the CPU; a CUDA double-precision Kerr trace serves
   near-extremal spin, where GLSL float cannot.
2. The analytic Kerr solver (`device_analytic_kerr.cuh`), which turns a
   1,000-step photon-ring ray into one elliptic evaluation. Today it renders
   nothing.
3. Large-batch volumetric transport and GRMHD sampling where FP16 storage
   and register-tuned variants (`kernel_registry.cu`) pay off.

## 5. Recommendation

Adopt (a) and (b) together, and let (c) follow for the shading code:

1. **Trace and transfer functions have one source** (option b), shimmed into
   GLSL, CUDA, and C++, and covered by the twin tests that already exist.
2. **CUDA emits a terminal record, GL shades it** (option a). The record is a
   GL buffer object, std430-compatible with a C struct whose layout a
   `static_assert` on `sizeof` and `offsetof` pins, the same pattern as
   `BH_LaunchParams`. The existing `TerminalCodes` SSBO (binding 7,
   `terminal_output.glsl`) and `ray_terminal.h` codes are the first field of
   the record.
3. **New appearance features are written once, in the shared core or in the
   GL shading pass, never in CUDA shading.** The acceptance test of the
   architecture is that tilt, warp, slow-light emission time
   (`docs/physics/spacetime-and-disk-dynamics.md`, G1 and G2), and turbulence
   each land with zero new lines in `device_physics.cuh` shading.
4. **CUDA keeps its compute roles**: double-precision and analytic Kerr traces,
   volumetric RTE and Stokes transport as a radiance service behind a shared
   transport core, and LUT and sky-map builds.
5. **CUDA gets a required compile lane** and a self-hosted GPU lane for
   `cuda_*` tests. A hosted runner can install the toolkit and compile
   without a device [INF; a hosted-runner nvcc install was not tested here],
   which catches every syntax and ABI break even where it cannot run the
   kernels.

Why not (b) alone: it leaves 1,000 lines of CUDA shading that no feature
needs and the sampler reimplementation. Why not (c) now: it discards the only
double-precision and analytic paths before measuring them, and the measured
comparison does not exist. Why not (a) alone: the trace and transfer twins
would still be hand-kept, and drift finding 1 would recur in a new shape.

## 6. Staged migration

Each stage has its own gate and ships alone. The order puts the checks first
so every later move is measured.

### Stage 0. Measure and pin

- Add the missing direct check: a fixed scene rendered by interop fragment,
  GL compute, and CUDA (auto and baseline variants), compared per pixel with
  stated tolerances, run in the GPU lane. This is the first test that
  compares GLSL against CUDA.
- Time trace-only versus shade-only on the CUDA path and the GL compute
  path; record the device and driver beside the numbers (repo convention).
- Extend the source-scraping constant pin to `iscoRadius` semantics: assert
  the host `kerrIscoRadius`, the GLSL `isco_radius`, and the value in
  `BH_LaunchParams.isco` agree to 1e-5 relative.
- Gate: tests pass on the current tree, tolerances recorded. No behavior
  change.

### Stage 1. Fix silent drift

- Make `bh_launch_geodesic_kernel` fall back to the baseline kernel when
  `rte_enabled` or `stokes_enabled` is set, or move the dispatch into the
  other variants; add a test that `rte_enabled = 1` changes the image on the
  auto-selected variant.
- Delete `bhStepRK4` and `bhSchwarzschildAccel` (dead in GLSL) and, once the
  tests that drive `kerr_enabled = 0` move to the Kerr integrator at a = 0
  (exact there per `kerr.glsl`), the CUDA Schwarzschild RK4 and the
  `d_kerr_enabled == 0` shaping branches.
- Gate: stage 0 parity unchanged; the new RTE-on-auto test fails before the
  fix and passes after.
- Removes about 110 lines and one silent-drop bug.

### Stage 2. One source for the pure kernels

- Start with the functions that already have three twins and tests:
  `pageThorneFluxShape` / `dtPageThorneShape`, `diskTransferG`, blackbody
  chroma. Move each to a shared core header in the GLSL subset with the three
  shims. `disk_transfer_shader_test` and `cuda_disk_transfer_test` then test
  one source.
- Then the Kerr Mino step (`kerr.glsl` 366 lines against the 397-line CUDA
  twin): the gate is `kerr_shader_capture_test` and `cuda_kerr_geodesic_test`
  passing on the shared source with the capture-edge falsifiers intact, plus
  the stage 0 image parity.
- Then the wiregrid math; `wiregrid_overlay_test` already holds a C++ port,
  so it becomes the third consumer rather than a fourth copy.
- Gate per function: both GPU tests pass unchanged; the shared file is the
  only definition (a repository check that fails if a known function name is
  defined twice).
- Removes about 800 CUDA lines of true duplicates and leaves no hand-kept
  twin for those functions.

### Stage 3. Terminal-record seam, retire CUDA shading

- Define the record (32 bytes target) with a shared C header; CUDA writes it
  to a GL-registered buffer, GL compute or fragment shades it. The first GL
  consumer reads the existing terminal-code SSBO fields.
- Move disk color, hit shading, sky sampling, the escaped-sky shaper, and
  the wiregrid overlay to the GL side only. Delete the CUDA copies (about
  1,000 lines) and the 335-line background block with its texture-object
  registration for the background.
- Gate: GL shading of the CUDA terminal buffer equals GL shading of the GL
  compute terminal buffer per pixel within the stage 0 tolerance; frame time
  is not worse than stage 0 by more than a stated budget; `cuda_*` tests that
  called shading move to terminal-record assertions.
- Falsifier: if the record write and read costs more than the CUDA shading it
  replaces, keep shading in CUDA for that path and retain the shared core of
  stage 2 (this is the branch where (a) is rejected on data and (b) stands).

### Stage 4. Volumetric transport decision

- RTE and Stokes fold shading and transport together. Measure whether GL
  compute matches CUDA transport within tolerance and time. If yes, port to
  GL and delete; if CUDA wins, keep it as a radiance service on the shared
  transport core (`rte_step`, `stokes_transport`) so the 350 and 427 GLSL
  lines and the 391 and 327 CUDA lines become one source.
- Gate: `cuda_rte_test` and `cuda_stokes_test` invariants (I^2 >= Q^2 + U^2 +
  V^2, exact rotation, absorption limits) hold on the chosen implementation,
  and the RTE and Stokes flags are honored on every variant (stage 1 test).

### Stage 5. Features written once

- Land the tilted-disk surface and emission time
  (`docs/physics/spacetime-and-disk-dynamics.md`, G1 and G2) and a disk
  turbulence field in the shared core or the GL shading pass. The turbulence
  becomes available on the interop and CUDA-fed paths for the first time.
- Gate: each feature's analytic-oracle tests from that note pass on GLSL and
  on CUDA-fed output; the diff adds no shading lines to `src/cuda/`.

### Stage 6. CUDA compute roles

- Wire the analytic Kerr solver into a kernel for rays that would step
  through the photon ring (impact parameter within a stated band of critical)
  and add a double-precision trace for near-extremal spin.
- Gate: `cuda_analytic_kerr_test` and `cuda_geodesic_orbit_test` extend to
  image-level agreement against the Mino tracer outside the ring band and
  higher accuracy inside it; a CUDA compile lane is required (recommendation
  item 5).

## 7. What would change this recommendation

- If stage 0 shows CUDA trace-only is not faster than GL compute trace-only on
  the target GPUs, CUDA's remaining case is double precision and the analytic
  solver, and (c) applies to all single-precision paths.
- If the terminal-record round trip is slower than in-kernel shading (stage 3
  falsifier), keep CUDA shading but on the shared core.
- If nvcc cannot compile the GLSL-subset shim without contortions in the
  Kerr step, use Slang or a generator for that function and leave the others
  on the shim.
- If the CUDA-only desktop variant is retired, the GL-only path becomes the
  default target and stages 3 to 6 collapse to deletion plus the analytic and
  double-precision work moving to CPU maps like the observer sky.

## 8. Sources

[CODE] paths named inline. [PUB] items: the CUDA runtime API's OpenGL
interoperability (`cudaGraphicsGLRegisterBuffer`, `cudaGraphicsGLRegisterImage`,
`cudaGraphicsMapResources`) is documented in NVIDIA's CUDA runtime API
reference, not fetched here; Slang is a shading language project hosted by
Khronos, not evaluated for this tree. The Kerr and disk physics behind the
shared kernels is cited in `docs/physics/spacetime-and-disk-dynamics.md` and
`docs/physics/accretion-flow-appearance.md`.
