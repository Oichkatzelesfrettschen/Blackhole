# Blender Bridge Requirements

## Scope

Use this lane for the shared library bridge and the Blender addon integration.

## Required

- Blender installation compatible with the addon
- Python-enabled Blender environment
- NumPy available in Blender's Python environment
- CUDA-capable environment if you want the bridge to dispatch CUDA code paths
- CMake 3.21+
- Conan 2.x

## Local integration points

- bridge source: `src/blender_bridge/`
- canonical addon tree: `blender/addon/blackhole_physics/`
- bridge-focused preset: `blender-bridge`
- full smoke-test preset: `full-dev`
- addon packaging target: `package-blender-addon`
- addon package verifier: `verify-blender-addon-package`
- bridge ABI verifier: `verify-blender-bridge-abi`
- local staging target: `stage-blender-addon`
- environment override for Blender installs: `BLACKHOLE_BRIDGE_LIB=/absolute/path/to/libblackhole_bridge.so`

## Configure/build

```bash
./scripts/conan_install.sh Release build/BlenderBridge/Release
cmake --preset blender-bridge
cmake --build --preset blender-bridge
cmake --build --preset blender-bridge --target package-blender-addon verify-blender-addon-package verify-blender-bridge-abi stage-blender-addon
```

## Headless smoke test

When `blender` is available on `PATH`, use `full-dev` for the `ctest`-registered
smoke lane:

```bash
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
cmake --preset full-dev
cmake --build --preset full-dev --target blender-addon-smoke verify-blender-smoke-report
ctest --preset full-dev -R "blender_bridge_abi|blender_addon_package|blender_addon_stage|blender_addon_smoke|blender_smoke_report" --output-on-failure
```

Generated reports land under:

- `build/<preset>/reports/dream_textures_blender_install.json`
- `build/<preset>/reports/dream_textures_blender_verified.json`
- `build/<preset>/reports/blender_addon_manifest.json`
- `build/<preset>/reports/blender_bridge_abi.json`
- `build/<preset>/reports/blender_addon_package.json`
- `build/<preset>/reports/blender_addon_stage.json`
- `build/<preset>/reports/blender_smoke.json`
- `build/<preset>/reports/blender_smoke_verified.json`
- `build/<preset>/reports/blender_interactive_benchmark.json`
- `build/<preset>/reports/blender_interactive_benchmark_verified.json`
- `build/<preset>/reports/octane_readiness.json`

## Dream Textures

The repo includes a Dream Textures runtime installer and verifier for stock
Blender 5.2. This lane stages the addon into the Blender 5.2 user addon tree,
points it at a Blackhole-managed Python 3.14 venv, and verifies a real CUDA
generation pass with `stabilityai/sdxl-turbo`.

The same runtime now plugs directly into the Blackhole addon's texture lane:

- accretion-disk emission -> `BlackholeDiskTexture`
- environment lookdev -> scene world environment texture

See [`../developer-guide/dream-textures-integration.md`](../developer-guide/dream-textures-integration.md)
for prompt topology, scientific prompt style, and the next-stage
image/depth-conditioned roadmap.

```bash
cmake --build --preset release --target verify-dream-textures-blender
ctest --test-dir build/Release -R dream_textures_blender --output-on-failure
```

Generated evidence:

- `build/<preset>/reports/dream_textures_blender_install.json`
- `build/<preset>/reports/dream_textures_blender_verified.json`
- `build/<preset>/reports/dream_textures_blender_verified.md`

The repo also verifies the direct addon codepath that generates Dream
Textures assets and binds them into both the Blackhole disk material lane and
the world-environment lane inside stock Blender and OctaneBlender:

```bash
cmake --build --preset release --target \
  verify-dream-textures-direct-blender \
  verify-dream-textures-direct-blender-background \
  verify-dream-textures-direct-octane \
  verify-dream-textures-direct-octane-background
ctest --test-dir build/Release -R 'dream_textures_.*direct' --output-on-failure
```

Direct-pipeline evidence:

- `build/<preset>/reports/dream_textures_blender_direct_verified.json`
- `build/<preset>/reports/dream_textures_blender_direct_verified.md`
- `build/<preset>/reports/dream_textures_blender_background_direct_verified.json`
- `build/<preset>/reports/dream_textures_blender_background_direct_verified.md`
- `build/<preset>/reports/dream_textures_octane_direct_verified.json`
- `build/<preset>/reports/dream_textures_octane_direct_verified.md`
- `build/<preset>/reports/dream_textures_octane_background_direct_verified.json`
- `build/<preset>/reports/dream_textures_octane_background_direct_verified.md`

Image-conditioned disk refinement is now also verified in both hosts. That lane
generates a real `BlackholeLensingMap` through the Blackhole bridge first, then
uses it as the Dream Textures `image_to_image` source for
`BlackholeDiskTexture`:

```bash
cmake --build --preset release --target \
  verify-dream-textures-direct-blender-conditioned \
  verify-dream-textures-direct-octane-conditioned
ctest --test-dir build/Release -R 'dream_textures_.*conditioned_direct' --output-on-failure
```

Conditioned-pipeline evidence:

- `build/<preset>/reports/dream_textures_blender_conditioned_direct_verified.json`
- `build/<preset>/reports/dream_textures_blender_conditioned_direct_verified.md`
- `build/<preset>/reports/dream_textures_octane_conditioned_direct_verified.json`
- `build/<preset>/reports/dream_textures_octane_conditioned_direct_verified.md`

Depth-conditioned disk refinement is also wired for both hosts. This lane uses
the public automation-compatible SD2 depth conversion
`carsonkatri/stable-diffusion-2-depth-diffusers` by default, while still
documenting `stabilityai/stable-diffusion-2-depth` as the canonical upstream
model when a Hugging Face login is available. The staged depth source comes
from real Blackhole geometry rendered through Dream Textures' scene-depth pass.

```bash
cmake --build --preset release --target \
  verify-dream-textures-direct-blender-depth \
  verify-dream-textures-direct-octane-depth
ctest --test-dir build/Release -R 'dream_textures_.*depth_direct' --output-on-failure
```

Depth-conditioned evidence:

- `build/<preset>/reports/dream_textures_blender_depth_direct_verified.json`
- `build/<preset>/reports/dream_textures_blender_depth_direct_verified.md`
- `build/<preset>/reports/dream_textures_octane_depth_direct_verified.json`
- `build/<preset>/reports/dream_textures_octane_depth_direct_verified.md`

Joint image+depth-conditioned disk refinement is also available for both hosts.
This lane combines the generated `BlackholeLensingMap` source image with the
staged scene-depth field from real Blackhole geometry, then feeds both into the
same depth-capable Dream Textures model:

```bash
cmake --build --preset release --target \
  verify-dream-textures-direct-blender-image-depth \
  verify-dream-textures-direct-octane-image-depth
ctest --test-dir build/Release -R 'dream_textures_.*image_depth_direct' --output-on-failure
```

Joint image+depth evidence:

- `build/<preset>/reports/dream_textures_blender_image_depth_direct_verified.json`
- `build/<preset>/reports/dream_textures_blender_image_depth_direct_verified.md`
- `build/<preset>/reports/dream_textures_octane_image_depth_direct_verified.json`
- `build/<preset>/reports/dream_textures_octane_image_depth_direct_verified.md`

The repo now also runs a four-mode conditioning sweep in both hosts. This keeps
the direct disk lane honest across:

- `none`
- `image`
- `depth`
- `image_depth`

The sweep uses a Dream Textures `conditioning_sweep` memory profile so it can
finish reliably on a partially occupied CUDA device without forcing the rest of
the machine to be idle. It persists mode artifacts plus diff heatmaps under the
build tree and records pairwise PSNR/luma metrics for the generated disk
textures.

```bash
cmake --build --preset release --target \
  verify-dream-textures-conditioning-sweep-blender \
  verify-dream-textures-conditioning-sweep-octane
ctest --test-dir build/Release -R 'dream_textures_.*conditioning_sweep' --output-on-failure
```

Conditioning-sweep evidence:

- `build/<preset>/reports/dream_textures_blender_conditioning_sweep_verified.json`
- `build/<preset>/reports/dream_textures_blender_conditioning_sweep_verified.md`
- `build/<preset>/reports/dream_textures_blender_conditioning_sweep_artifacts/`
- `build/<preset>/reports/dream_textures_octane_conditioning_sweep_verified.json`
- `build/<preset>/reports/dream_textures_octane_conditioning_sweep_verified.md`
- `build/<preset>/reports/dream_textures_octane_conditioning_sweep_artifacts/`

The repo also runs the same four-mode sweep under the `harsh_lighting` scene
profile in both hosts and verifies Blender-vs-Octane parity for both baseline
and harsh scenes:

- `build/<preset>/reports/dream_textures_blender_harsh_conditioning_sweep_verified.json`
- `build/<preset>/reports/dream_textures_octane_harsh_conditioning_sweep_verified.json`
- `build/<preset>/reports/dream_textures_conditioning_baseline_parity.json`
- `build/<preset>/reports/dream_textures_conditioning_harsh_parity.json`

The sweep verifier now enforces a real quality floor for the combined lane:

- `image_depth` vs `image` must stay above the configured PSNR RGB/luma floor
- the host-parity verifier requires Blender and Octane to stay within mean,
  PSNR, and luma-cosine tolerances for the same scene profile

On top of those raw gates, the repo now derives a scene policy for each host
and a cross-host trend summary:

- `build/<preset>/reports/dream_textures_blender_conditioning_policy.json`
- `build/<preset>/reports/dream_textures_blender_harsh_conditioning_policy.json`
- `build/<preset>/reports/dream_textures_octane_conditioning_policy.json`
- `build/<preset>/reports/dream_textures_octane_harsh_conditioning_policy.json`
- `build/<preset>/reports/dream_textures_conditioning_trends.json`

Current measured policy on this machine:

- interactive default: `image`
- production default: `image_depth`
- the recommendation is the same in both `baseline` and `harsh_lighting`
  scenes for both Blender 5.2 and OctaneBlender

Those recommendations are now wired back into the addon UI as:

- `Auto (interactive)`
- `Auto (production)`

The addon resolves those modes from
`build/<preset>/reports/dream_textures_conditioning_trends.json` when that
report is available in the checkout, and otherwise falls back to the same
measured defaults.

The panel also now exposes slot-aware quick actions:

- `Regenerate Disk (Interactive Policy)`
- `Regenerate Disk (Scene Policy)`
- `Regenerate Background (Scene Policy)`
- `Prepare Scene for Policy Generation`
- `Invalidate Disk Texture Artifacts`
- `Invalidate Background Texture Artifacts`
- `Invalidate Policy Prerequisites`

These avoid manual slot/mode juggling:

- disk interactive regeneration temporarily uses the measured fast policy
- disk regeneration temporarily uses the production policy
- background regeneration temporarily uses the robust text-to-image default

The disk quick action also performs scene preflight automatically when the
resolved policy requires it:

- ensures a `BlackholeLensingMap` source image exists for image conditioning
- ensures a scene camera exists for depth-based conditioning
- ensures `EventHorizon` and `AccretionDisk` objects exist for staged depth

Those prerequisites are now cache-aware. The addon stamps signatures onto the
generated lensing map, camera, horizon, and disk so policy-driven reruns can
reuse them when the governing scene parameters still match, instead of
rebuilding them every time.

That cache-aware preflight is now verified directly in both stock Blender and
OctaneBlender. The cold pass creates the lensing map, and the warm pass reuses
it:

- `build/Release/reports/dream_textures_blender_policy_generation_verified.json`
- `build/Release/reports/dream_textures_octane_policy_generation_verified.json`

There is now also a stale-refresh lane that mutates the governing scene
parameters after the warm pass and verifies that the next preparation run
refreshes stale inputs instead of silently reusing them:

- `build/Release/reports/dream_textures_blender_policy_stale_refresh_verified.json`
- `build/Release/reports/dream_textures_octane_policy_stale_refresh_verified.json`

The prepare-only coverage now also includes the unconditioned background lane
and the production `image_depth` lane:

- `build/Release/reports/dream_textures_blender_policy_background_prepare_verified.json`
- `build/Release/reports/dream_textures_blender_policy_production_prepare_verified.json`
- `build/Release/reports/dream_textures_octane_policy_background_prepare_verified.json`
- `build/Release/reports/dream_textures_octane_policy_production_prepare_verified.json`

Rendered black hole stills are now surfaced as stable showcase galleries:

- `build/Release/reports/blender_showcase_render.json`
- `build/Release/reports/octane_showcase_render.json`
- `build/Release/reports/blender_showcase_artifacts/baseline_final.png`
- `build/Release/reports/blender_showcase_artifacts/harsh_lighting_final.png`
- `build/Release/reports/octane_showcase_artifacts/baseline_final.png`
- `build/Release/reports/octane_showcase_artifacts/harsh_lighting_final.png`

The policy layer uses per-mode elapsed time plus the existing PSNR floors, so
the repo can answer "which conditioning mode should we actually use?" instead
of only storing raw sweep metrics.

The direct reports now include prompt-budget, prompt-provenance, seed-policy,
cache-state, backend-capability, asset-digest, and world-binding metadata. A
saved direct report can be replayed through:

```bash
python3 scripts/replay_dream_textures_report.py \
  --report build/Release/reports/dream_textures_blender_direct_verified.json \
  --print-only
```

## Interactive benchmark lane

The first repo-native Blender benchmark lane measures the addon inside Blender
and records effective frame-generation timing for three in-process paths:

- `bridge_lensing_preview`: CPU bridge lensing-map path
- `bridge_cuda_preview`: CUDA bridge preview path when CUDA is available
- `render_engine_final`: Blender `BLACKHOLE_RT` final-frame render path when the
  CUDA render engine is available

This is an addon-integrated benchmark, not yet a full viewport-FPS capture
lane. It is meant to establish reproducible frame-time evidence inside Blender
without overstating what is measured.

The benchmark now seeds its input `.blend` through the isolated BlenderMCP lane
before the timed run starts. That preflight scene builder:

- launches a nondefault-port isolated BlenderMCP session
- applies the M87* preset and studio-quality profile
- generates `EventHorizon`, `AccretionDisk`, and a lensing map
- saves a reproducible benchmark scene `.blend`
- shuts the MCP session down after the scene artifact is captured

The benchmark report embeds the MCP scene report, including the chosen port,
the saved `.blend` path, and the final scene object inventory.

For the Octane lane, the repo now runs a dedicated readiness probe before the
interactive benchmark. That probe classifies Octane as one of:

- `ready`: headless Octane produced a non-empty render artifact
- `setup_required`: Octane is installed, but first-run sign-in, activation, or
  adjacent setup still appears to be blocking automation
- `server_unavailable`: OctaneBlender could not connect to `OctaneServer`
- `not_ready` or `probe_failed`: the repo could not confirm safe automation yet

This keeps "Octane launches" separate from "Octane final render automation is
actually available."

```bash
cmake --build --preset full-dev --target benchmark-blender-interactive verify-blender-interactive-benchmark
ctest --preset full-dev -R "blender_interactive_benchmark|blender_interactive_benchmark_report" --output-on-failure
```

For Octane specifically:

```bash
cmake --build --preset full-dev --target probe-octane-readiness benchmark-octane-interactive verify-octane-interactive-benchmark
ctest --preset full-dev -R "octane_readiness|octane_interactive_benchmark|octane_interactive_benchmark_report" --output-on-failure
```

For the tiered Octane optimization sweep:

```bash
cmake --build --preset full-dev --target verify-octane-quality-sweep
ctest --preset full-dev -R "octane_quality_sweep_report" --output-on-failure
```

## Studio-grade quality bar

For this repo, "production studio-grade quality" means all of the following are
true at the same time:

- the color pipeline is correct: no double tonemapping, no arbitrary post-tonemap
  exposure boosts, and an explicit Blender view transform is recorded
- the render engine is configured deliberately: GPU path when available, high
  sample counts, denoising, and engine-aware bounce/kernel defaults
- the scene is camera- and compositor-ready: transparent film, black-space world,
  stable camera defaults, and a compositor policy that avoids double-applying
  cinematic effects to `BLACKHOLE_RT`
- the quality setup is reproducible: smoke and benchmark reports record the
  applied studio-quality summary instead of relying on undocumented manual clicks
- the final-quality lane is comparable to the fast lane: benchmark reports now
  capture pairwise diff artifacts and image-comparison metrics between the CUDA
  preview path and the final render path when both are available

## Interactive install

The smoke runner installs the packaged addon zip into a temporary isolated
Blender addon directory automatically. For interactive use, install the zip at
`build/<preset>/dist/blackhole_physics-addon.zip` through Blender Preferences,
or unzip it under a directory pointed to by `BLENDER_USER_SCRIPTS`.

If `libblackhole_bridge.so` is not on the system library path, set:

```bash
export BLACKHOLE_BRIDGE_LIB=/absolute/path/to/libblackhole_bridge.so
```

Then launch Blender and enable the addon, or run:

```bash
blender --python blender/addon/setup_blender5.py
```

For a repo-local staged addon tree without touching your real Blender config:

```bash
cmake --build --preset blender-bridge --target stage-blender-addon
export BLENDER_USER_SCRIPTS=$PWD/build/BlenderBridge/Release/staging/blender-user-scripts
blender --python blender/addon/setup_blender5.py
```

## Isolated BlenderMCP session

When another Blender process is already listening on the default BlenderMCP
port `9876`, use the repo launcher to create a second isolated session on the
next free port without touching your real Blender preferences:

```bash
python3 scripts/run_blender_mcp_isolated_session.py \
  --blender-executable /usr/bin/blender \
  --source-dir "$PWD" \
  --addon-zip "$PWD/build/Release/dist/blackhole_physics-addon.zip" \
  --bridge-lib "$PWD/build/Release/src/blender_bridge/libblackhole_bridge.so" \
  --port 19876 \
  --port-range 32 \
  --json-out "$PWD/build/Release/reports/blender_mcp_isolated_session.json"
```

The launcher stages an isolated `BLENDER_USER_CONFIG` and `BLENDER_USER_SCRIPTS`
tree under `/tmp`, enables both addons, applies the studio-quality profile, and
probes `get_scene_info` before it returns success.

The generated report records the chosen port, PID, temp-root, and first probe:

- `build/<preset>/reports/blender_mcp_isolated_session.json`

Use the companion probe helper to talk to the isolated session:

```bash
python3 scripts/blender_mcp_probe.py \
  --host 127.0.0.1 \
  --port 19876 \
  --type get_scene_info \
  --timeout-seconds 10
```

Example scene mutation through the same socket:

```bash
python3 scripts/blender_mcp_probe.py \
  --host 127.0.0.1 \
  --port 19876 \
  --type execute_code \
  --params-json '{"code":"import bpy\\nbpy.ops.blackhole.generate_horizon()"}'
```

For noninteractive automation the launcher defaults to a headless
BlenderMCP-compatible command loop that reuses the installed addon's command
handlers. Use `--mode gui` if you explicitly want a windowed Blender session.

## Current policy

- The desktop application remains the canonical control surface.
- Blender is treated as a downstream client/integration surface.
- The bridge-focused preset intentionally disables the desktop app, tools, and
  benchmark binaries so the addon lane can be built in isolation.
- The smoke lane validates the packaged addon artifact, not just the source tree.

## Octane optimization notes

For this repo, Octane optimization means:

- keep the kernel on path tracing for the final-quality lane
- use adaptive sampling with a real threshold and minimum-sample floor
- use AI Light for complex lighting unless a scene proves it harmful
- use higher coherent ratio only for interactive speed, not for the cinematic tier
- compare preview vs final with the repo's diff artifacts and PSNR metrics

The detailed tier policy and rationale live in:

- `docs/developer-guide/octane-optimization.md`
