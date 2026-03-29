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
- `post-shaping-background`
- `shaper-inputs` packed as:
  - `R = clamp(minRadiusReached / (5 * rs), 0, 1)`
  - `G = alignedFlow`
  - `B = nearHoleWeight`

That split changed the RCA materially.

What it showed:

1. The main mismatch is already present before redshift.
2. Redshift only changes the CUDA-vs-GLSL gap slightly for these showcase stills.
3. The real debt is upstream background sampling/composition, not just near-hole shaping.
4. Once the upstream background path was fixed, `post-shaping-background` showed the
   remaining bright-arc debt is already present before the later photon-ring add.

Representative evidence:

- `showcase-orbit_wide-right_preredshift_bg1`
- `showcase-orbit_wide-right_preshaping_bg2`
- `showcase-orbit_right-third_preredshift_bg1`
- `showcase-orbit_right-third_preshaping_bg2`

The redshift-stage delta was small compared with the pre-redshift gap:

- `wide-right`: mean abs `0.04506 -> 0.04510`
- `right-third`: mean abs `0.04508 -> 0.04509`

So redshift is not the primary offender.

The later stage split mattered too. After the time-rotation and sRGB fixes were in place,
`post-shaping-background` still showed the CUDA arc core far below GLSL:

- `wide-right` bright arc core luma: about `0.08948` (GLSL) vs `0.00928` (CUDA)
- `right-third` bright arc core luma: about `0.07579` (GLSL) vs `0.01049` (CUDA)

That means the remaining gap is not mainly the later photon-ring term. It is already baked
into the shaped escaped background.

The `shaper-inputs` stage sharpened that further. For pixels that GLSL classifies as the
bright arc core, CUDA often reports the neutral fallback input:

- `minRadiusNorm = 1.0`
- `alignedFlow = 0.5`
- `nearHoleWeight = 0.0`

That is not just a weighting mismatch. It means many CUDA rays that GLSL treats as
near-hole arc-core rays are not entering the near-hole shaping regime at all on the CUDA side.

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

## The Big Color-Space RCA

The next decisive fix was more fundamental than another shaping tweak.

The desktop backgrounds are loaded as `GL_SRGB` / `GL_SRGB_ALPHA`, so the GLSL lane
samples them in linear space after automatic sRGB decode. CUDA was sampling those
same registered textures as normalized float values with no explicit decode.

That matched the observed failure mode exactly:

- pre-redshift CUDA background too bright
- pre-redshift CUDA background too colorful
- right-side escaped field heavily biased even before shaping

Once CUDA background samplers were switched to explicit sRGB-to-linear decode, the
pre-redshift parity improved dramatically.

For `wide-right`:

- mean abs: `0.04281 -> 0.00637`
- `bright_arc_adjacent_right` luma gap: `0.08660 -> 0.00405`
- `bright_arc_adjacent_right` chroma gap: `0.01295 -> 0.00051`
- `broad_right_background` luma gap: `0.07335 -> 0.00855`
- `broad_right_background` chroma gap: `0.01062 -> 0.00156`
- `negative_space` luma gap: `0.03738 -> 0.00495`
- `negative_space` chroma gap: `0.00537 -> 0.00093`

For `right-third`:

- mean abs: `0.04286 -> 0.00626`
- `bright_arc_adjacent_right` luma gap: `0.08602 -> 0.00389`
- `bright_arc_adjacent_right` chroma gap: `0.01187 -> 0.00052`
- `broad_right_background` luma gap: `0.07395 -> 0.00823`
- `broad_right_background` chroma gap: `0.01092 -> 0.00157`
- `negative_space` luma gap: `0.03762 -> 0.00485`
- `negative_space` chroma gap: `0.00558 -> 0.00096`

This is the first upstream parity fix that clearly solved the right problem instead of
merely redistributing error.

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

### 7. Full Desktop-Shaper Ports After Upstream Fixes

Examples:

- copying the stronger desktop GLSL near-hole shaping constants directly into CUDA
- adding local core-only emphasis after the existing CUDA suppressions

Why it failed:

- the full desktop-style shaper reheated the broad right-side field without lifting the
  arc core enough
- the narrow core-only emphasis made the core worse on exact reruns
- the `post-shaping-background` stage proved these were real shaper failures, not
  later photon-ring artifacts

Takeaway:

- the remaining debt is inside the CUDA shaper, but it will not be solved by a broad
  copy of the desktop GLSL constants
- the next correction has to be more local than "use the desktop shaper"

### 8. Shaper-Input Instrumentation Changed The Target

Examples:

- exporting `minRadiusReached`, `alignedFlow`, and `nearHoleWeight` directly as a packed raw stage
- comparing those maps by channel in the same regional masks

Why it mattered:

- it showed the shaped-background mismatch is not only about the shaping coefficients
- in the GLSL bright arc core, CUDA often arrives with neutral shaper inputs instead of
  near-hole inputs

Representative evidence:

- `showcase-orbit_wide-right_shaperinputs1`
- `showcase-orbit_right-third_shaperinputs1`

For `wide-right bright_arc_core`:

- GLSL mean RGB: about `[0.7104, 0.9694, 0.0529]`
- CUDA mean RGB: about `[1.0, 0.5, 0.0]`

For `right-third bright_arc_core`:

- GLSL mean RGB: about `[0.7086, 0.9686, 0.0549]`
- CUDA mean RGB: about `[1.0, 0.5, 0.0]`

Takeaway:

- the next correction should target geodesic / closest-approach / escaped-ray geometry parity
  before more shaper-coefficient tuning

### 6. Color-Space Blindness

Examples:

- treating CUDA background texture samples as if they were already linear-light values

Why it failed:

- OpenGL was sampling `GL_SRGB` textures with automatic decode
- CUDA was reading the same texture data as normalized float without decode
- this made the escaped background too bright and too saturated before redshift

Takeaway:

- color-space parity is part of mathematical correctness here
- raw image parity is not trustworthy if one lane is still in encoded sRGB while the other
  is in linear space

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
2. The strongest early upstream bug was the missing time rotation in CUDA.
3. The biggest chroma mismatch was also upstream: CUDA was not decoding sRGB backgrounds.
4. After those fixes, the escaped-field parity is much closer in both luma and chroma.
5. The `post-shaping-background` stage shows the main remaining debt has shifted to the
   true bright arc core, which is now relatively under-hot in CUDA compared with GLSL.
6. The `shaper-inputs` stage shows that some of that debt is upstream of the shaper
   coefficients themselves: CUDA often reaches the bright-arc masks with neutral
   shaper inputs.
7. The later photon-ring add is not the main offender anymore.

That means the next control surface should move forward from the now-cleaner upstream baseline:

1. preserve the fixed upstream background parity
2. use `shaper-inputs` and `post-shaping-background` together to keep geometry and shaping honest
3. only then return to near-hole or arc-core parity work

## Practical Rule Going Forward

Do not promote a CUDA still into `openperception` unless the raw probe says the right-side
escaped field is genuinely closer to GLSL in both luma and chroma, not just in a sweep-time
score or a post-tonemap screenshot.
