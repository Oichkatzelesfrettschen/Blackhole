# Raw CUDA/GLSL Parity Post-Mortem

This note distills what the raw `texBlackhole` parity work has actually taught us.
It focuses on `showcase-orbit` / `wide-right`, where the remaining CUDA-vs-GLSL gap
is easiest to measure before bloom and tonemap.

## What The Raw Probe Established

The repo-owned raw exporter and comparer changed the problem from subjective screenshot
debate into a measurable renderer-input problem.

Primary tools:

- `src/main.cpp --export-raw-frame`
- `scripts/compare_raw_texblackhole.py`

What the raw probe proved:

1. The remaining CUDA-vs-GLSL mismatch is already present in `texBlackhole`.
2. The shared bloom/tonemap path is not the primary source of the parity debt.
3. The dominant remaining gap lives in the escaped background near the hole, especially:
   - `bright_arc_adjacent_right`
   - `broad_right_background`

## Regions That Matter

The most useful raw masks have been:

- `bright_arc_adjacent_right`
  The spill band just outside the true bright arc. This is the hardest region.
- `broad_right_background`
  The darker escaped field farther from the arc.
- `negative_space`
  The dark field that should stay dark in the compute winner.

The center box and whole-image mean abs are useful context, but they do not identify the
actual visual failure mode as well as the two right-side masks above.

## What Failed And Why

### 1. Broad Global Suppression

Examples:

- stronger broad field suppression
- generic dimming outside the bright sector
- blanket desaturation

Why it failed:

- it often improved `broad_right_background`
- but it flattened legitimate structure or did not move `bright_arc_adjacent_right`
  enough to matter

Takeaway:

- the problem is not "CUDA is globally too bright"
- the problem is "too much energy survives in the wrong specific right-side bands"

### 2. Boundary / Sector Membership Tricks

Examples:

- tighter `adjacent_sector`
- arc-boundary terms
- sector-only suppression keyed to `aligned_flow`

Why it failed:

- sweep-time wins were often not stable on exact reruns
- region membership by itself is too brittle
- small shifts in the mask boundary did not produce robust parity wins

Takeaway:

- geometric membership alone is not a stable proxy for the real error

### 3. Tint Endpoint Pulls

Examples:

- moving `cool_tint` / `warm_tint` toward neutral
- narrowing the warm/cool palette in the adjacent band

Why it failed:

- improved some broad-field numbers
- but often regressed `bright_arc_adjacent_right`
- endpoint motion alone was too blunt and changed the wrong pixels with the same lever

Takeaway:

- changing the palette endpoints is closer than blanket desaturation, but still too global

### 4. Chroma-Gated Adjacent-Band Palette Pulls

Examples:

- gate endpoint pull by local chroma
- gate endpoint pull by local luma + chroma

Why it failed:

- promising in sweeps
- not robust enough on exact reruns
- still attacked the palette source rather than the final contribution path

Takeaway:

- local chroma is a better signal than sector membership alone
- but acting on palette endpoints is still not localized enough

## What Consistently Helped

### 1. Raw Measurement By Region

The single biggest quality improvement in this effort was not a shader change. It was
measuring the right regions:

- `bright_arc_adjacent_right`
- `broad_right_background`
- `negative_space`

Without these masks, sweep results were too easy to overread.

### 2. Preserving Dark Negative Space

Changes that reduced surviving energy outside the main bright sector were consistently
helpful, especially when they left the true bright arc intact.

### 3. Narrower, More Local Control

The closer a change got to the actual tint/lift contribution in the adjacent band,
the more promising it became.

This is why the next move should target the blend path after `rim_sector` interpolation,
not the global palette definition.

## Current Working Hypothesis

The remaining parity debt is not primarily "wrong hue endpoints" or "not enough dimming."
It is that the CUDA escaped-field path still lets too much colored tint contribution survive
after the warm/cool interpolation step in the adjacent band.

That suggests a better control surface:

1. Keep the warm/cool palette fixed.
2. Keep `rim_sector` interpolation fixed.
3. Modify only the final adjacent-band contribution of `arc_tint`, using local luma/chroma
   to soften its chroma without flattening the true bright arc.

## Practical Rule Going Forward

Do not promote a CUDA still into `openperception` unless the raw probe says the right-side
escaped field is genuinely closer to GLSL in both luma and chroma, not just in a sweep-time
score or a post-tonemap screenshot.
