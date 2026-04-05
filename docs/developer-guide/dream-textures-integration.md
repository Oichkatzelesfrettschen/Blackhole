# Dream Textures Integration

This document defines how Dream Textures feeds the Blackhole Blender and
Octane lookdev lanes.

## Current Integration

The Blackhole addon already had one texture insertion path:

- `BlackholeDiskTexture` for accretion-disk emission
- the scene world environment for background lookdev

Dream Textures is now wired into that same path through
`blender/addon/blackhole_physics/sd_textures.py`.

The backend split is:

- `sd_cpp`: local `.gguf` / `sd` binary path
- `dream_textures`: Blender-native Dream Textures generation
- `diffusers`: in-process Python diffusers fallback
- `auto`: prefer `sd_cpp` for `.gguf`, else prefer Dream Textures for HF models

This keeps all material assignment, image packing, and world-environment
application code unchanged.

## Asset Topology

Prompt language must target the actual texture topology we need.

### Disk Lane

Use Dream Textures to produce a square, seamless emissive texture atlas for
`BlackholeDiskTexture`.

Prompt anchors:

- `Kerr black hole accretion disk emissive texture atlas`
- `seamless tileable square texture`
- `synchrotron-dominated plasma`
- `Novikov-Thorne radial temperature falloff`
- `Doppler-bright approaching side`
- `photon ring halo`

The disk lane enables Dream Textures seamless padding on both axes.

### Environment Lane

Use Dream Textures to produce a world background plate.

Prompt anchors:

- `equirectangular deep-space environment map`
- `black hole lookdev sky plate`
- `deep extragalactic starfield`
- `high dynamic range`

The environment lane does not request seamless tiling.

## Prompt Style Policy

The addon exposes three prompt styles:

- `scientific`: parameter-rich scientific visualization phrasing
- `hybrid`: scientific framing with some cinematic lookdev language
- `cinematic`: more dramatic astrophotography language

All three styles still preserve the target topology terms above. The style
layer changes visual language, not the output class.

## Scientific Mathematical Prompting

The prompt style should be parameterized, but not equation-heavy.

Recommended form:

- use short symbolic tokens inline:
  - `a*=0.938`
  - `i=17.0 deg`
  - `mdot=0.100 Edd`
  - `M=6.500e+09 Msun`
- keep the math descriptive rather than algebraic
- describe observables and morphology, not derivations
- keep the total prompt compact enough to stay inside the CLIP token budget;
  prefer a few high-value morphology cues over a long adjective list

Good examples:

- `Kerr black hole accretion disk emissive texture atlas, a*=0.938, i=17.0 deg, mdot=0.100 Edd, synchrotron-dominated plasma, Doppler-bright approaching side, photon ring halo, seamless tileable square texture`
- `equirectangular deep-space environment map, astronomical survey mosaic, sparse nebular haze, point-like stars, no planets, no spacecraft`

Avoid:

- raw equations
- LaTeX
- long prose sentences
- vague `space art` language without target topology
- prompts that ask for foreground objects in the environment lane

## Model Policy

The default model policy is tuned for `stabilityai/sdxl-turbo`.

From the official model guidance:

- use one-step text-to-image generation
- disable CFG guidance with `guidance_scale=0.0`
- do not rely on a negative prompt for the turbo path

The addon enforces that automatically when the selected model name contains
`sdxl-turbo` or `sd-turbo`.

## Reproducibility Contract

The direct Dream Textures verifier now records more than pass/fail status.
Each generated asset carries:

- prompt-budget accounting
- prompt-provenance inputs
- seed policy
- backend capability flags
- model-cache resolution
- deterministic SHA256 asset digest
- image metadata including channel count, colorspace, and alpha policy
- world-environment binding evidence for the background lane

That metadata is emitted in the direct verification reports for both stock
Blender and OctaneBlender, and can be replayed with:

```bash
python3 scripts/replay_dream_textures_report.py \
  --report build/Release/reports/dream_textures_blender_background_direct_verified.json \
  --print-only
```

The planned image/depth staging contract is documented separately in
[`dream-textures-conditioning-contract.md`](dream-textures-conditioning-contract.md).

## Conditioned Refinement

Image-conditioned refinement is now live for the Dream Textures backend.

Current behavior:

- `sd_conditioning_mode = image` reuses a real Blackhole-generated source image
- disk lane source: `BlackholeLensingMap`
- background lane source: current world environment image or `BH_SD_Background`
- the conditioned reports record the effective task, source image name, and
  source provenance

The current default conditioned verifier uses `stabilityai/sdxl-turbo` with the
requested user step count preserved. The one-step turbo policy remains limited
to unconditioned text-to-image, because collapsing image-conditioned turbo runs
to one step can produce an empty timestep schedule in Diffusers.

Depth-conditioned refinement is now also live through the automation-compatible
SD2 depth model mirror, and the next combined lane is no longer just planned.

Current verified conditioning modes:

- `image`: `BlackholeLensingMap` drives `image_to_image`
- `depth`: staged Blackhole geometry drives `depth_to_image`
- `image_depth`: `BlackholeLensingMap` and the staged scene-depth field are
  supplied together to the same depth-capable model

That makes the disk lane progressively tighter:

1. text-only morphology prior
2. image-conditioned lensing guidance
3. depth-conditioned geometry guidance
4. joint image+depth guidance for both silhouette and brightness structure

The repo now measures those four modes side by side in both stock Blender 5.2
and OctaneBlender through dedicated conditioning sweeps. Each sweep:

- runs `none`, `image`, `depth`, and `image_depth`
- uses a Dream Textures `conditioning_sweep` memory profile
- persists the generated per-mode PNGs under the build report tree
- computes pairwise PSNR/MAE/luma-cosine comparisons plus diff heatmaps

Current measured behavior on this machine:

- `none` remains the brightest unconstrained morphology prior
- `depth` stays much closer to `none` than `image_depth` does by mean intensity
- `image_depth` clusters very tightly around `image` in PSNR while still
  incorporating the staged scene-depth field
- both hosts produce closely matched sweep statistics, which means the Dream
  Textures conditioning lane is effectively host-stable across Blender and
  OctaneBlender

The sweep lane is now scene-aware as well:

- `baseline`
- `harsh_lighting`

and the verifier promotes two concrete guarantees into build gates:

1. `image_depth` must remain close to `image` under a configured PSNR floor
2. Blender and OctaneBlender must remain within bounded host-parity tolerances
   for the same scene profile

The next policy layer is now live as well. It records per-mode elapsed time,
derives a recommended interactive mode and production mode per host/scene, and
then builds a single cross-host trend summary.

Current outcome on this machine:

- `baseline`: interactive `image`, production `image_depth`
- `harsh_lighting`: interactive `image`, production `image_depth`
- Blender and OctaneBlender agree on that recommendation in both scenes

That gives the repo a more honest default story:

- `image` is the fastest conditioned lane that still stays close to the joint
  lane
- `image_depth` is the production lane because it preserves the staged depth
  signal while still clearing the PSNR floor against `image`
- the addon now exposes those recommendations directly as `Auto (interactive)`
  and `Auto (production)` instead of forcing users to choose the raw mode names

## Near-Term Next Step

The next stage should build on the policy layer with scene-aware thresholding:

1. tighten or relax the interactive/production thresholds per scene class
2. add a third scene profile for more extreme emissivity or jet contamination
3. connect the policy summary to automated material refresh defaults in the UI

That path is preferable to adding more ad hoc prompt adjectives because it
brings the generated textures closer to the actual Blackhole geometry and
lensing state.

## Depth Model Policy

Dream Textures' own depth tooling points at the Stable Diffusion 2 depth family.

Blackhole keeps two distinct references here:

- canonical upstream recommendation: `stabilityai/stable-diffusion-2-depth`
- automation-compatible repo default:
  `carsonkatri/stable-diffusion-2-depth-diffusers`

The distinction matters because the official Stability repository is gated on
this machine unless a Hugging Face account is logged in, while the Carson Katri
diffusers conversion is publicly accessible and works with unattended runtime
installation and verification.

So the repo policy is:

- document the official Stability depth model as the upstream scientific
  reference point
- use the public diffusers conversion for automated Blender and Octane depth
  verification
- record the exact selected model ID in every depth-conditioned report

## Stronger Depth-Source Workflow

The depth lane now uses actual Blackhole scene geometry instead of a generic
placeholder scene.

For the disk verifier, the staged scene now includes:

- `AccretionDisk` mesh from the Blackhole bridge geometry path
- `EventHorizon` mesh from the same bridge path
- `BlackholeLensingMap` image for the image-conditioned lane

Then Dream Textures renders a normalized scene-depth pass from that staged
geometry through its own depth renderer before depth-conditioned generation.

The resulting reports now include:

- `source_depth_name`
- `source_depth_metadata.range`
- `source_depth_digest.sha256`
- `source_origin`

That makes the depth source measurable, reproducible, and comparable across
stock Blender and OctaneBlender instead of leaving depth provenance implicit.
