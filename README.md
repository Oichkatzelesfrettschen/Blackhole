# Blackhole

![Screenshot](docs/blackhole-screenrecord.gif)

Real-time black hole rendering and validation workbench with a shared desktop UI,
GLSL and CUDA rendering paths, and a Blender bridge.

## Highlights
- Shared desktop application in C++23 + OpenGL 4.6.
- Pure GLSL desktop workflow and CUDA-enabled desktop workflow via CMake presets.
- Blender bridge/addon support for the external Blender track.
- LUT-driven emissivity/redshift and validation assets in `assets/`.
- Repo-truth reporting that inventories the configured build, presets, tools, and tests.

## Prerequisite

- [cmake](https://cmake.org/)
- [conan](https://conan.io/) package manager (repo-local home; see `scripts/conan_env.sh`)
- C++23-capable compiler
- OpenGL 4.6-capable GPU/driver

## Build the code

Install dependencies with repo-local Conan (output folder must match your CMake build dir).

Preferred invocation (Conan 2.x):

```bash
# repo-local cache
./scripts/conan_install.sh Release build
./scripts/fetch_implot.sh

# Configure the project and generate a native build system.
cmake --preset release
cmake --build --preset release

# Generate the measured repo inventory for this build tree.
cmake --build --preset release --target repo-truth
```

If you must use raw conan commands, prefer the 2.x syntax:

```bash
conan install . --output-folder=build --build=missing -s build_type=Release -s compiler.cppstd=23
```

Optional build flags:

```bash
# Optional RmlUi overlay (MangoHUD port groundwork).
cmake --preset release -DENABLE_RMLUI=ON

# Optional Tracy profiling.
cmake --preset release -DENABLE_TRACY=ON

# Or explicit configure/build.
cmake -DCMAKE_BUILD_TYPE=Release -S . -B build/Release \
  -DCMAKE_TOOLCHAIN_FILE=build/Release/generators/conan_toolchain.cmake
cmake --build build/Release
```

## Product workflows

- `release`: baseline desktop build.
- `glsl-only`: shared desktop UI without CUDA or Blender bridge.
- `cuda-only`: shared desktop UI with CUDA enabled.
- `blender-bridge`: bridge-focused build without the desktop app.
- `full-dev`: shared desktop UI, CUDA, Blender bridge, tools, and tests.

Install Conan dependencies into the matching build directory before configuring a
product preset. Example:

```bash
./scripts/conan_install.sh Release build/GLSL-Only/Release
cmake --preset glsl-only
cmake --build --preset glsl-only
ctest --preset glsl-only
```

Blender bridge packaging and staging:

```bash
./scripts/conan_install.sh Release build/BlenderBridge/Release
cmake --preset blender-bridge
cmake --build --preset blender-bridge --target blackhole_bridge package-blender-addon verify-blender-addon-package verify-blender-bridge-abi stage-blender-addon
```

Blender and Octane smoke validation:

```bash
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
cmake --preset full-dev
cmake --build --preset full-dev --target blender-addon-smoke verify-blender-smoke-report
cmake --build --preset full-dev --target octane-addon-smoke verify-octane-smoke-report
ctest --preset full-dev -R "blender_bridge_abi|blender_addon_package|blender_addon_stage|blender_addon_smoke|blender_smoke_report|octane_addon_smoke|octane_smoke_report"
```

Blender interactive benchmark lane:

```bash
cmake --build --preset full-dev --target benchmark-blender-interactive verify-blender-interactive-benchmark
ctest --preset full-dev -R "blender_interactive_benchmark|blender_interactive_benchmark_report" --output-on-failure
```

Dream Textures runtime verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-blender
ctest --preset full-dev -R "dream_textures_blender" --output-on-failure
```

Dream Textures direct Blackhole disk-material verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-blender
ctest --preset full-dev -R "dream_textures_blender_direct" --output-on-failure
```

Dream Textures image-conditioned Blackhole disk-material verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-blender-conditioned
ctest --preset full-dev -R "dream_textures_blender_conditioned_direct" --output-on-failure
```

Dream Textures depth-conditioned Blackhole disk-material verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-blender-depth
ctest --preset full-dev -R "dream_textures_blender_depth_direct" --output-on-failure
```

Dream Textures image+depth-conditioned Blackhole disk-material verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-blender-image-depth
ctest --preset full-dev -R "dream_textures_blender_image_depth_direct" --output-on-failure
```

Dream Textures direct Blackhole world-environment verification in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-blender-background
ctest --preset full-dev -R "dream_textures_blender_background_direct" --output-on-failure
```

Dream Textures conditioning sweep in Blender 5.2 (`none`, `image`, `depth`, `image_depth`):

```bash
cmake --build --preset full-dev --target verify-dream-textures-conditioning-sweep-blender
ctest --preset full-dev -R "dream_textures_blender_conditioning_sweep" --output-on-failure
```

Dream Textures harsh-lighting conditioning sweep in Blender 5.2:

```bash
cmake --build --preset full-dev --target verify-dream-textures-harsh-conditioning-sweep-blender
ctest --preset full-dev -R "dream_textures_blender_harsh_conditioning_sweep" --output-on-failure
```

Dream Textures direct lookdev integration guide:

- [`docs/developer-guide/dream-textures-integration.md`](docs/developer-guide/dream-textures-integration.md)
- The automated depth lane uses `carsonkatri/stable-diffusion-2-depth-diffusers`
  for unattended verification and still documents
  `stabilityai/stable-diffusion-2-depth` as the canonical upstream model.

Octane interactive benchmark lane:

```bash
cmake --build --preset full-dev --target probe-octane-readiness benchmark-octane-interactive verify-octane-interactive-benchmark
ctest --preset full-dev -R "octane_readiness|octane_interactive_benchmark|octane_interactive_benchmark_report" --output-on-failure
```

Dream Textures runtime verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-octane
ctest --preset full-dev -R "dream_textures_octane" --output-on-failure
```

Dream Textures direct Blackhole disk-material verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-octane
ctest --preset full-dev -R "dream_textures_octane_direct" --output-on-failure
```

Dream Textures image-conditioned Blackhole disk-material verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-octane-conditioned
ctest --preset full-dev -R "dream_textures_octane_conditioned_direct" --output-on-failure
```

Dream Textures depth-conditioned Blackhole disk-material verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-octane-depth
ctest --preset full-dev -R "dream_textures_octane_depth_direct" --output-on-failure
```

Dream Textures image+depth-conditioned Blackhole disk-material verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-octane-image-depth
ctest --preset full-dev -R "dream_textures_octane_image_depth_direct" --output-on-failure
```

Dream Textures direct Blackhole world-environment verification in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-direct-octane-background
ctest --preset full-dev -R "dream_textures_octane_background_direct" --output-on-failure
```

Dream Textures conditioning sweep in OctaneBlender (`none`, `image`, `depth`, `image_depth`):

```bash
cmake --build --preset full-dev --target verify-dream-textures-conditioning-sweep-octane
ctest --preset full-dev -R "dream_textures_octane_conditioning_sweep" --output-on-failure
```

Dream Textures harsh-lighting conditioning sweep in OctaneBlender:

```bash
cmake --build --preset full-dev --target verify-dream-textures-harsh-conditioning-sweep-octane
ctest --preset full-dev -R "dream_textures_octane_harsh_conditioning_sweep" --output-on-failure
```

Cross-host conditioning parity checks:

```bash
cmake --build --preset full-dev --target \
  verify-dream-textures-conditioning-parity \
  verify-dream-textures-harsh-conditioning-parity
ctest --preset full-dev -R "dream_textures_.*conditioning_host_parity" --output-on-failure
```

Scene-aware conditioning policy and trend summary:

```bash
cmake --build --preset full-dev --target \
  verify-dream-textures-conditioning-policy-blender \
  verify-dream-textures-harsh-conditioning-policy-blender \
  verify-dream-textures-conditioning-policy-octane \
  verify-dream-textures-harsh-conditioning-policy-octane \
  verify-dream-textures-conditioning-trends
ctest --preset full-dev -R "dream_textures_.*conditioning_policy|dream_textures_conditioning_trends" --output-on-failure
```

Current repo policy from the generated reports:

- interactive default: `image`
- production default: `image_depth`
- both `baseline` and `harsh_lighting` scenes currently agree across Blender
  5.2 and OctaneBlender

The addon UI now exposes those as direct conditioning choices:

- `Auto (interactive)`
- `Auto (production)`

When the generated trend report is present, the addon resolves those modes from
the measured policy; otherwise it falls back to the same current defaults.

It now also exposes one-click quick actions in the Blackhole > Stable
Diffusion panel:

- `Regenerate Disk (Interactive Policy)`
- `Regenerate Disk (Scene Policy)`
- `Regenerate Background (Scene Policy)`
- `Prepare Scene for Policy Generation`
- `Invalidate Disk Texture Artifacts`
- `Invalidate Background Texture Artifacts`
- `Invalidate Policy Prerequisites`

Those actions apply slot-specific defaults automatically:

- disk interactive -> measured fast policy
- disk -> production policy
- background -> reliable unconditioned text-to-image lane

The disk quick action is now scene-constructive too. When the resolved policy
needs conditioning inputs, it automatically prepares the prerequisites before
generation:

- creates a lensing map when needed
- creates a scene camera when depth conditioning needs one
- creates `EventHorizon` and `AccretionDisk` geometry when missing

The cache-aware preparation path is now verified directly in both hosts, and
the warm pass reuses the prepared lensing input instead of rebuilding it:

- [`build/Release/reports/dream_textures_blender_policy_generation_verified.json`](build/Release/reports/dream_textures_blender_policy_generation_verified.json)
- [`build/Release/reports/dream_textures_octane_policy_generation_verified.json`](build/Release/reports/dream_textures_octane_policy_generation_verified.json)

Stale-refresh verification is now tracked separately too. After mutating the
scene from the baseline profile into the harsh-lighting profile, the next
prepare pass refreshes the now-stale prerequisites instead of incorrectly
reusing them:

- [`build/Release/reports/dream_textures_blender_policy_stale_refresh_verified.json`](build/Release/reports/dream_textures_blender_policy_stale_refresh_verified.json)
- [`build/Release/reports/dream_textures_octane_policy_stale_refresh_verified.json`](build/Release/reports/dream_textures_octane_policy_stale_refresh_verified.json)

The background and production prepare-only lanes are now also tracked
explicitly:

- [`build/Release/reports/dream_textures_blender_policy_background_prepare_verified.json`](build/Release/reports/dream_textures_blender_policy_background_prepare_verified.json)
- [`build/Release/reports/dream_textures_blender_policy_production_prepare_verified.json`](build/Release/reports/dream_textures_blender_policy_production_prepare_verified.json)
- [`build/Release/reports/dream_textures_octane_policy_background_prepare_verified.json`](build/Release/reports/dream_textures_octane_policy_background_prepare_verified.json)
- [`build/Release/reports/dream_textures_octane_policy_production_prepare_verified.json`](build/Release/reports/dream_textures_octane_policy_production_prepare_verified.json)

Actual rendered black hole frames are now promoted into stable showcase
galleries backed by verified benchmark reports:

- stock Blender gallery report: [`build/Release/reports/blender_showcase_render.json`](build/Release/reports/blender_showcase_render.json)
- Octane gallery report: [`build/Release/reports/octane_showcase_render.json`](build/Release/reports/octane_showcase_render.json)
- stock Blender baseline final: [`build/Release/reports/blender_showcase_artifacts/baseline_final.png`](build/Release/reports/blender_showcase_artifacts/baseline_final.png)
- stock Blender harsh-lighting final: [`build/Release/reports/blender_showcase_artifacts/harsh_lighting_final.png`](build/Release/reports/blender_showcase_artifacts/harsh_lighting_final.png)
- Octane hybrid baseline final: [`build/Release/reports/octane_showcase_artifacts/baseline_final.png`](build/Release/reports/octane_showcase_artifacts/baseline_final.png)
- Octane hybrid harsh-lighting final: [`build/Release/reports/octane_showcase_artifacts/harsh_lighting_final.png`](build/Release/reports/octane_showcase_artifacts/harsh_lighting_final.png)
- Octane native proxy baseline final: [`build/Release/reports/octane_showcase_artifacts/baseline_native_proxy_final.png`](build/Release/reports/octane_showcase_artifacts/baseline_native_proxy_final.png)
- Octane native proxy harsh-lighting final: [`build/Release/reports/octane_showcase_artifacts/harsh_lighting_native_proxy_final.png`](build/Release/reports/octane_showcase_artifacts/harsh_lighting_native_proxy_final.png)

Those prerequisites are now signature-tracked as well, so repeated policy
regenerations can reuse the existing lensing map and geometry when the relevant
scene inputs have not changed, and only rebuild them when they are stale.

The Octane benchmark now records two distinct final lanes:

- `render_engine_native_final`: the pure Octane proxy scene
- `render_engine_final`: the synthesized CUDA base plus Octane finishing pass

That split is intentional. The Blackhole CUDA renderer and Octane are separate
renderers, even on the same NVIDIA GPU, so the repo now treats the CUDA+Octane
path as an explicit hybrid handoff instead of pretending Octane is directly
executing Blackhole's CUDA kernel.

Recent native-Octane handoff hardening:

- the disk material now follows Octane's converter-friendly path
  (`ShaderNodeTexImage -> ShaderNodeEmission -> OctaneUniversalMaterial`)
  instead of the older bespoke diffuse/emission graph
- OctaneServer readiness now requires a real listener on `127.0.0.1:5130`,
  not just a stale PID
- the mixed CUDA+Octane benchmark now resets the bridge CUDA device before
  Octane takes over, which stops the earlier mixed-lane CUDA/OOM failures

Current honest state of the native proxy lane:

- it is no longer black; the latest native proxy benchmark mean luma is about
  `0.7449`
- the hybrid lane mean luma is about `0.7517`
- preview-vs-native and preview-vs-hybrid PSNR are still only about `2.64`
  and `2.60`, so the Octane proxy is now alive but not yet physically aligned
  with the Blackhole CUDA preview
- Octane's own log still reports `Tex: ( Rgb32: 0, Rgb64: 0, grey8: 0, grey16: 0 )`
  during these renders, so direct Octane texture ingestion remains the main
  unresolved native-render gap

Octane quality-tier sweep:

```bash
cmake --build --preset full-dev --target verify-octane-quality-sweep
ctest --preset full-dev -R "octane_quality_sweep_report" --output-on-failure
```

That sweep runs the same Octane lane across `interactive`, `balanced`, and
`cinematic` tiers and verifies that the tier policy actually changes samples and
adaptive thresholds in the expected direction.

Octane harsh-lighting benchmark:

```bash
cmake --build --preset full-dev --target verify-octane-harsh-scene
ctest --preset full-dev -R "octane_harsh_scene_report" --output-on-failure
```

That lane reuses the balanced Octane tier but switches the benchmark harness to
a stronger multi-light stress profile so preview/final agreement is tested under
more demanding lighting.

## Optional: curve overlay

Plot a 2-column TSV (for example CompactStar critical curves) in the ImGui
overlay:

```bash
./build/Release/Blackhole --curve-tsv /absolute/path/to/Crit_curve_smooth.tsv
```

## Documentation

Full project documentation lives in [`docs/index.md`](docs/index.md).
- Product matrix: [`docs/getting-started/product-matrix.md`](docs/getting-started/product-matrix.md)
- Repo truth: [`docs/developer-guide/repo-truth.md`](docs/developer-guide/repo-truth.md)
- Bibliography: [`docs/references/bibliography.md`](docs/references/bibliography.md)
- Module requirements: [`docs/requirements/index.md`](docs/requirements/index.md)

## OpenGL 4.6 scope

See [`docs/gpu/scope.md`](docs/gpu/scope.md) for validation and platform notes.

## Status and validation

- Roadmap + issue tracking: [`docs/developer-guide/status.md`](docs/developer-guide/status.md) and [`docs/developer-guide/backlog.md`](docs/developer-guide/backlog.md).
- Repo truth report:
  `cmake --build --preset release --target repo-truth`
- Blender bridge/addon evidence:
  `cmake --build --preset release --target verify-blender-bridge-abi verify-blender-addon-package stage-blender-addon`
- Blender/Octane smoke-report verification:
  `cmake --build --preset release --target verify-blender-smoke-report verify-octane-smoke-report`
- Blender interactive benchmark verification:
  `cmake --build --preset release --target verify-blender-interactive-benchmark`
- Dream Textures runtime verification:
  `cmake --build --preset release --target verify-dream-textures-blender verify-dream-textures-octane`
- Octane quality sweep verification:
  `cmake --build --preset release --target verify-octane-quality-sweep`
- GLSL validation (warnings treated as errors only when `ENABLE_WERROR=ON`):
  `cmake --build --preset release --target validate-shaders`
- Physics validation tables:
  `python3 scripts/generate_validation_tables.py`

## Acknowledgements

**Papers**

- Gravitational Lensing by Spinning Black Holes in Astrophysics, and in the Movie Interstellar
- Trajectory Around A Spherically Symmetric Non-Rotating Black Hole - Sumanta
- Approximating Light Rays In The Schwarzschild Field - O. Semerak
- Implementing a Rasterization Framework for a Black Hole Spacetime - Yoshiyuki Yamashita

<!-- https://arxiv.org/pdf/1502.03808.pdf -->
<!-- https://arxiv.org/pdf/1109.0676.pdf -->
<!-- https://arxiv.org/pdf/1412.5650.pdf -->
<!-- https://pdfs.semanticscholar.org/56ff/9c575c29ae8ed6042e23075ff0ca00031ccc.pdfhttps://pdfs.semanticscholar.org/56ff/9c575c29ae8ed6042e23075ff0ca00031ccc.pdf -->

**Articles**

- Physics of oseiskar.github.io/black-hole - https://oseiskar.github.io/black-hole/docs/physics.html
- Schwarzschild geodesics - https://en.wikipedia.org/wiki/Schwarzschild_geodesics
- Photons and black holes - https://flannelhead.github.io/posts/2016-03-06-photons-and-black-holes.html
- A real-time simulation of the visual appearance of a Schwarzschild Black Hole - http://spiro.fisica.unipd.it/~antonell/schwarzschild/
- Ray Tracing a Black Hole in C# by Mikolaj Barwicki - https://www.codeproject.com/Articles/994466/Ray-Tracing-a-Black-Hole-in-Csharp
- Ray Marching and Signed Distance Functions - http://jamie-wong.com/2016/07/15/ray-marching-signed-distance-functions/
- Einstein's Rings and the Fabric of Space - https://www.youtube.com/watch?v=Rl8H4XEs0hw)
- Opus 2, GLSL ray tracing tutorial - http://fhtr.blogspot.com/2013/12/opus-2-glsl-ray-tracing-tutorial.html
- Ray Tracing in One Weekend - https://raytracing.github.io/
- On ray casting, ray tracing, ray marching and the like - http://hugi.scene.org/online/hugi37/- hugi%2037%20-%20coding%20adok%20on%20ray%20casting,%20ray%20tracing,%20ray%20marching%20and%20the%20like.htm

**Other GitHub Projects**

- https://github.com/sirxemic/Interstellar
- https://github.com/ssloy/tinyraytracer
- https://github.com/RayTracing/raytracing.github.io
- https://awesomeopensource.com/projects/raytracing
- Ray-traced simulation of a black hole - https://github.com/oseiskar/black-hole
- Raytracing a blackhole - https://rantonels.github.io/starless/
- https://github.com/rantonels/schwarzschild
