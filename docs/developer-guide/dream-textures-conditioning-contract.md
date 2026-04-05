# Dream Textures Conditioning Contract

This document scopes the next-stage interface between Blackhole render outputs
and Dream Textures conditioning workflows.

## Goal

Move from pure text-to-image lookdev toward controlled refinement that stays
anchored to Blackhole geometry, lensing, and scene state.

## Conditioning Modes

The addon now exposes these planned modes:

- `none`: current text-to-image path
- `image`: future image-to-image refinement from a Blackhole preview frame
- `depth`: future depth-to-image refinement from a staged Blackhole depth pass
- `image_depth`: future joint color+depth refinement

Current repo truth still reports these as unimplemented. The properties and
metadata are present so the eventual implementation can land without inventing
new state later.

## Staging Layout

Conditioning inputs should be staged under a deterministic directory such as:

```text
build/<preset>/staging/dream_textures_conditioning/<label>/
```

Expected payloads:

- `color.png` or `color.exr`: Blackhole preview frame
- `depth.npy` or `depth.exr`: Blackhole depth pass
- `manifest.json`: source paths, hashes, and semantic labels

The helper script:

```bash
python3 scripts/stage_dream_textures_conditioning_input.py \
  --label harsh_lighting_preview \
  --staging-dir build/Release/staging/dream_textures_conditioning/harsh_lighting_preview \
  --color /path/to/preview.png \
  --depth /path/to/depth.npy \
  --json-out build/Release/reports/dream_textures_conditioning_harsh_lighting.json
```

copies inputs into a stable location and records SHA256 hashes.

## Color Contract

Color inputs should be:

- top-to-bottom image orientation
- display-ready sRGB for preview-conditioned lookdev
- deterministic camera framing when used in benchmark or verifier lanes

## Depth Contract

Depth inputs should be:

- aligned pixel-for-pixel with the staged color frame
- normalized or accompanied by an explicit normalization policy
- monotonic with camera distance in the recorded manifest

The preferred future normalization is a reproducible [0, 1] mapping derived
from the exact render pass bounds recorded in the staging manifest, not an
implicit per-image auto-stretch.

## Prompting Policy

Conditioned generation should keep the same scientific prompt topology as the
current direct lane:

- retain Kerr/disk/environment semantic anchors
- keep symbolic parameters compact
- treat conditioning as a geometry/morphology guide, not as a replacement for
  the scientific prompt

## Next Implementation Targets

1. Export Blackhole preview color frames into the staging layout.
2. Export aligned depth passes into the staging layout.
3. Teach the Dream Textures backend wrapper to accept staged image inputs.
4. Teach the Dream Textures backend wrapper to accept staged depth inputs.
5. Add verifier coverage for image-conditioned disk and depth-conditioned
   environment generation.
