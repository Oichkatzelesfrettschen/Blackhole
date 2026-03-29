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

## Stage Split: Before Redshift vs After Redshift

We now have two raw export checkpoints:

- `pre-redshift-background`
- `pre-shaping-background`

That split changed the RCA materially.

What it showed:

1. The main mismatch is already present before redshift.
2. Redshift only changes the CUDA-vs-GLSL gap slightly for these showcase stills.
3. The real debt is upstream background sampling/composition, not just near-hole shaping.

Representative evidence:

- `showcase-orbit_wide-right_preredshift_bg1`
- `showcase-orbit_wide-right_preshaping_bg2`
- `showcase-orbit_right-third_preredshift_bg1`
- `showcase-orbit_right-third_preshaping_bg2`

The redshift-stage delta was small compared with the pre-redshift gap:

- `wide-right`: mean abs `0.04506 -> 0.04510`
- `right-third`: mean abs `0.04508 -> 0.04509`

So redshift is not the primary offender.

## Upstream Background Parity Bugs We Confirmed

The stage split let us stop guessing and inspect the actual background path.

Confirmed parity bugs:

1. CUDA was not rotating the escaped background by `time` before sampling, while GLSL was.
2. CUDA's layered equirect path was using a different layer UV transform from GLSL.
3. CUDA's background pitch rotation path was not using the camera-right axis that GLSL uses.
4. CUDA's layered equirect path was always applying a small blur kernel even when
   `background_filter_radius == 0`, which is not what the desktop GLSL lane does.

The time-rotation fix was the clearest measurable win so far. After the upstream fixes,
the pre-redshift wide-right gap moved:

- overall mean abs: `0.04506 -> 0.04281`
- `broad_right_background` luma gap: `0.08123 -> 0.07335`
- `negative_space` luma gap: `0.04182 -> 0.03738`

And for `right-third`:

- overall mean abs: `0.04508 -> 0.04286`
- `broad_right_background` luma gap: `0.08111 -> 0.07395`
- `negative_space` luma gap: `0.04182 -> 0.03762`

That is real progress, and it happened before we touched the near-hole shaping block.

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

### 5. Near-Hole Shaping Fixes Applied Too Early

Examples:

- direct CUDA copies of the active GLSL shaping block
- adjacent spill suppression before background-path parity was established

Why it failed:

- the background entering the shaping block was already too different
- some direct "GLSL parity" shaping ports actually made arc-core chroma worse

Takeaway:

- shaping parity cannot be solved cleanly until the escaped background input is closer

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

This is why the next move should target the correct stage first. Right now that means
upstream background composition and chroma parity before more near-hole shaping work.

## Current Working Hypothesis

The remaining parity debt is now best described like this:

1. The largest luma mismatch was upstream escaped-background composition, not redshift.
2. The strongest fixed upstream bug so far was the missing time rotation in CUDA.
3. After those upstream fixes, the remaining debt is increasingly chroma-heavy:
   CUDA is still too colorful in the right-side escaped field even when luma improves.

That suggests the next control surface should not be another generic shaping tweak.
It should be a pre-redshift background-composition/chroma investigation:

1. verify the layered equirect sampling path against the desktop GLSL lane again
2. compare pre-redshift chroma by region, not just luma
3. only then return to near-hole shaping parity

## Practical Rule Going Forward

Do not promote a CUDA still into `openperception` unless the raw probe says the right-side
escaped field is genuinely closer to GLSL in both luma and chroma, not just in a sweep-time
score or a post-tonemap screenshot.
