# Tesseract scene: replacing the wireframe with an Interstellar-inspired look

Status: design research, no code changed. The owner viewed the live scene and rejected it: a
thin wireframe hypercube plus labeled "library of time" feature points (books, window corners,
desk corners) read as a math diagram, not as the film's tesseract. This document maps the
current implementation, pins down what the film actually shows, and proposes a concrete,
real-time, asset-free rendering design plus a delete/keep/build breakdown.

## 1. Current implementation map

### Geometry and math (`src/render/tesseract/`)

- `tesseract_geometry.h`/`.cpp`: the 4-cube complex (`TesseractMesh`, `buildTesseract()`,
  geometry.cpp:90-132) and the two 4D->3D projections, `projectPerspective`
  (geometry.cpp:134-137) and `projectStereographic` (geometry.cpp:139-147), each mirrored
  vertex-for-vertex in `shader/tesseract.vert:86-98`.
- The rejected content lives in the same file: `FeatureKind` (geometry.h:119, `Shelf`/`Window`/
  `Desk`), `LibraryFeature` with a `name` field (geometry.h:122-126), `bedroomFeatures()`
  (geometry.cpp:149-188, hardcoded book/window/desk coordinates and English names such as
  `"Window upper front corner"`), `bedroomOutline()`/`outlinePolylines()` (geometry.cpp:206-235,
  the room-outline wireframe), `extrudeWorldTube()` (geometry.cpp:237-247, one straight polyline
  per feature point along w) and `selectedTubeMarker`/`selectedTubeSegments`
  (geometry.cpp:190-204).
- `buildSceneSegments()` (geometry.cpp:307-344) assembles three kinds of camera-facing ribbon
  segment (`SegmentKind::TesseractEdge/WorldTube/LitSlice`, geometry.h:226) into one instanced
  vertex buffer: subdivided cube edges, one world-tube per bedroom feature, and one lit-moment
  room-outline polyline per `outlinePolylines()` run.
- `so4.h`: the reusable SO(4) rotation math, `v -> qL v conj(qR)` on unit-quaternion pairs
  (so4.h:1-40 and following), templated on scalar type; `advanceOrientation`/
  `tesseractMotionAt` (geometry.cpp:269-290) step or closed-form-evaluate it. This is real
  physics-adjacent linear algebra, unconnected to the labeled-feature content, and is the
  mechanism the new design keeps.

### Renderer (`src/render/tesseract/tesseract_renderer.{h,cpp}`)

- `TesseractRenderer::render()` (renderer.cpp:205-255) draws the instanced ribbons with
  `GL_TRIANGLES`/6 vertices per instance, additive blending (`GL_ONE, GL_ONE`,
  renderer.cpp:224-226), directly into `rs.targets.texBlackhole` -- the same HDR target the
  black-hole fragment pass writes, so bloom and ACES tonemap treat it identically (see below).
  This FBO/VAO/program lifecycle, the saved/restored GL state (`SavedGlState`, renderer.cpp:66-
  118), and the hot-reload path (`reloadShaders()`, renderer.cpp:147-166) are reusable
  infrastructure independent of the visual content.
- Camera and framing math is reusable: `tesseractView`/`tesseractViewProjection`
  (renderer.cpp:377-399), `tesseractFraming` (renderer.cpp:344-366, sizes the record camera so
  the scene fills frame), `tesseractZoom`/`tesseractViewDistanceAfterInput`
  (renderer.cpp:368-375).
- `layoutSpeculativeLabel()` (renderer.cpp:257-333) and `TESSERACT_SPECULATIVE_LABEL`
  (renderer.h:41-42, `"SPECULATIVE (Thorne, The Science of Interstellar ch. 29-31): not
  physics"`) burn a persistent on-screen disclaimer into every frame, including recordings. The
  owner's instruction keeps this label; it is unrelated to the rejected geometry and needs no
  change.
- `TesseractFrameInputs` (renderer.h:90-112) is the uniform contract between `RenderState` and
  the GL pass: `selectedStrand`, `markerTime`, `pulseStrand`, `pulseTime` are the rejected
  "selected feature" concept threaded through; `edgeIntensity`/`strandIntensity`/
  `sliceIntensity`/`lineWidthPx` are generic ribbon-appearance knobs that a redesign can keep or
  repurpose.

### Shaders (`shader/tesseract.vert`, `shader/tesseract.frag`)

- `tesseract.vert` is a camera-facing ribbon expander for instanced line segments: 4D rotate and
  project each endpoint (`project4`, vert:100-108), near-plane clip in clip space
  (`nearClipStart`/`nearClipEnd`, vert:110-120), then build a screen-space quad with mitered
  joints at shared polyline corners (vert:130-238). This whole ribbon/miter/clip apparatus is
  the "thin wireframe line ribbons" the owner rejected; none of it survives a non-wireframe
  redesign, though the 4D-rotate-then-project block (`project4`) is reusable as a per-point
  transform inside a new fragment approach.
- `tesseract.frag` colors by `vKind`: `KIND_EDGE` cool blue, `KIND_WORLD_TUBE` dim amber
  brightened by a Gaussian at the lit moment plus a brighter Gaussian pulse
  (frag:53-76). The blue/amber duality and the Gaussian-in-time emission profile
  (`gaussian()`, frag:48-51, mirroring `litMomentEmission` in geometry.cpp:253-256) are ideas
  worth keeping (amber is closer to the film's palette than blue is); the ribbon-shaped
  geometry they paint is not.

### `RenderState::TesseractGroup` (`src/render/render_state.h:191-227`)

Holds the SO(4) rate/phase/orientation state (reusable), the `FeatureSelection selection`
(render_state.h:211, rejected), the pulse fields `pulseStrand`/`pulseNow`/`pulsePast`/
`pulseTravel`/`pulseSpeed`/`pulseWidth` (render_state.h:213-218, the concept -- a traveling
signal along a time strand -- is worth keeping structurally; the concrete "world-tube strand"
substrate is not), and the appearance/projection/camera knobs the panel exposes.

### UI (`src/ui/panels.cpp`)

- `renderTesseractRotationControls()` (panels.cpp:952-984): SO(4) rate sliders and three
  presets (`Simple xw`, `Left isoclinic`, `SO(3) qL = qR`). Reusable as-is; these are the only
  controls that touch the actual 4D structure.
- `renderTesseractProjectionControls()` (panels.cpp:986-1002): projection mode combo, eye
  distance, scene scale, view distance, FOV. Reusable.
- `renderTesseractLibraryControls()` (panels.cpp:1004-1037): the rejected UI surface --
  `"Selected feature"` combo listing book/window/desk names (panels.cpp:1009-1024), `"Cyan
  tube: selected feature; white mark: lit moment"` help text (panels.cpp:1025), the pulse-strand
  slider tied to the same feature list (panels.cpp:1031).
- `renderTesseractAppearanceControls()` (panels.cpp:1039-1045): line width and three intensity
  sliders, keepable as generic "how bright is X" controls under new names.
- `renderTesseractPanel()` (panels.cpp:1049-1073) assembles the window and draws the
  speculative-label text (panels.cpp:1059-1065, `PushStyleColor`+`TextWrapped`), which stays.

### `src/main.cpp` dispatch

- Scene dispatch: `SceneMode::Tesseract` branch (main.cpp:1314-1337) builds an optional
  `TesseractRecordFrame` from the output clock and camera focus tangent, then calls
  `renderTesseractScene()`; it neither runs the geodesic integrator nor reports GRMHD/compute
  activity, matching the observer-sky branch's shape (main.cpp:1300-1313). Zoom is redirected to
  the tesseract's own view distance while the scene is active (main.cpp:559-566,
  `tesseractActive`). Shader hot-reload calls `rs.tesseract.renderer.reloadShaders()`
  (main.cpp:1205-1206) outside the normal `shaderProgramMap` path. Shutdown releases the
  renderer and the speculative-label overlay (main.cpp:2138-2139). None of this dispatch
  plumbing needs to change for a new visual; it is scene-content-agnostic.

### Post pipeline (`src/render/post_pipeline.cpp`)

The tesseract pass writes straight into `texBlackhole`, so it automatically goes through Bloom
Composite (post_pipeline.cpp:100-116, `bloomStrength`/`bloomTone` uniforms) and the ACES
tonemap pass (post_pipeline.cpp:118-127, `shader/tonemapping.frag`, Narkowicz 2015 curve). Depth
cues are explicitly skipped for this scene mode because the pass writes alpha 1 everywhere
(post_pipeline.cpp:128-134, `depthCuesApply = rs.scene.mode == RenderState::SceneMode::
Blackhole`). This means: **the bloom/ACES pipeline is free and reusable for the new design
with no changes**, and a raymarched replacement pass has the same obligation the ribbon pass
already meets -- write HDR radiance to `texBlackhole` with alpha 1 -- and nothing else needs to
change downstream.

### Exposure (`tesseract_renderer.h:168-186`)

`TESSERACT_RECORD_EXPOSURE = 0.375f` is calibrated against the ribbons' 99th-percentile
brightness (`tesseract_exposure_gl_test.cpp`). A new emissive palette (different peak radiance,
different color distribution) invalidates this constant; it must be recalibrated against the
new pass's own measured brightness, the same way the current comment documents it was derived.

### Tests that pin the rejected visual

- `tests/tesseract_geometry_test.cpp`: `LibraryOfTime.*` tests (`FeatureNamesAreUniqueAndNonEmpty`
  at line 195, `FeatureSelectionTracksWholeTubeAndLitMoment` at 229, `LibraryTimeMapsOntoTesseractW`
  at 240, `LitMomentIsUnitGaussianInLibraryTime` at 247, `GravityPulseRunsFromNowToPast` at 257,
  `PulseSpeedChangeAffectsOnlyLaterMotion` at 282) and `SceneSegments.LayoutCountsAndTags` (400)
  all assert on `bedroomFeatures()`/world-tube/outline content and must be replaced or rewritten
  against the new geometry.
- `TesseractGeometry.*`/`TesseractProjection.*` (lines 53-181) test the 4-cube complex and the
  two projections directly; these keep working unchanged since the math is reused.
- `TesseractAnimation.*` (304-400) test SO(4) stepping and closed-form motion; unchanged.
- `tests/tesseract_ribbon_gl_test.cpp` (8 tests, lines 260-430): entirely about ribbon
  rasterization correctness (joint miters, near-plane clipping, subdivision independence). These
  test code that a raymarched replacement deletes outright; they cannot be adapted, only
  retired.
- `tests/tesseract_gl_state_test.cpp` (5 tests, 105-222): GL state save/restore and the render-
  to-texture/reload contract. Reusable in spirit (a raymarch pass has the same GL-state and
  hot-reload obligations) but the concrete assertions reference the ribbon program/VAO and need
  rewriting against the new pass's objects.
- `tests/tesseract_exposure_gl_test.cpp` (1 test, 142): measures ribbon-pixel 99th-percentile
  brightness against `TESSERACT_RECORD_EXPOSURE`; must be rebuilt against the new pass's
  radiance statistics.
- `tests/tesseract_framing_test.cpp` (12 tests): pure camera/framing math, unrelated to ribbon
  content; unchanged.
- `tests/tesseract_motion_test.cpp` (9 tests): SO(4) motion, zoom, pause; unchanged.
- `tests/tesseract_label_test.cpp` (8 tests): the speculative-label layout; unchanged (label
  stays).

## 2. What the film actually shows

Primary and reputable secondary sources, with inference flagged where the sources do not state
a detail directly.

- Kip Thorne's *The Science of Interstellar* devotes chapters to "Bulk beings" and "The
  Tesseract": Cooper, inside Gargantua, finds himself in a structure that is, physically, the
  back side of Murph's childhood bookcase, extended by future "bulk beings" into a hyper-cubic
  space that lets him act on the past. Thorne is explicit that this is speculative physics
  built on unproven bulk/brane and quantum-gravity ideas, not a prediction
  ([Goodreads summary](https://www.goodreads.com/en/book/show/23261448-the-science-of-interstellar);
  [W. W. Norton explainer on bulk beings](https://wwnorton.medium.com/an-interstellar-explainer-what-are-bulk-beings-1f0d0d99f847)).
  The repository's own label already cites this chapter range correctly
  (`tesseract_renderer.h:41-42`).
- VFX supervisor Paul Franklin (Double Negative), on the record: "A tesseract is a
  three-dimensional shadow of a four-dimensional hyper cube. It has this beautiful lattice-like
  structure," and the team built a physical set piece "containing four rooms" and digitally
  extended it, explicitly avoiding greenscreen for the sequence ("We didn't use a single bit of
  green screen in that entire sequence") ([Screen Daily VFX feature](https://www.screendaily.com/awards/the-vfx-of-interstellar/5082127.article);
  [Art of VFX interview](https://www.artofvfx.com/interstellar-paul-franklin-vfx-supervisor-double-negative/);
  fxguide retrospective, https://www.fxguide.com/fxfeatured/interstellar-inside-the-black-art/).
  This is the source for "open lattice, not a closed room" and "practically-lit, physically
  extended set," not a pure CG void.
- The slit-scan technique is the explicit inspiration for the time-strand look. Franklin: "Those
  photos record one point in space across many moments in time, where a typical photo is a
  moment in time across many points in space... I thought this was a way we could build all the
  timeline extrusions of all the objects in Murph's bedroom" (same interview set as above; also
  summarized at [IndieWire](https://www.indiewire.com/features/general/inside-the-making-of-the-spectacular-tesseract-in-interstellar-189771/),
  paywalled at fetch time but corroborated by the Screen Daily and Art of VFX pieces). This
  grounds the repository's own approach (`extrudeWorldTube`, a straight line through time per
  point) as structurally correct -- the error is not the time-strand *concept*, it is drawing
  only a handful of named, labeled points instead of a dense field of threads over the whole
  extended structure, and rendering each thread as a thin flat-shaded ribbon instead of a woven,
  lit fiber.
- Structural summary repeated across secondary sources and consistent with the released film:
  Cooper floats through what reads as an infinite corridor of repeated bedroom instances, each
  a different moment in time, and can act on a moment by disturbing dust or a book at its
  location; the sequence is famous for building this from a slit-scan-inspired asset rather
  than a literal repeated room (multiple secondary summaries agree on "infinite" repetition and
  "floating through a corridor," e.g. general audience explainers such as
  [Medium: The Tesseract in Interstellar](https://medium.com/@srivassekhar/the-tesseract-in-interstellar-explained-simply-75d073fb3862)).
  **Inference**: the exact geometric arrangement of the infinite repetition (whether it reads
  as a rectilinear grid, a radial fan, or a corridor with side branches) is not pinned down by
  any source fetched here at load-bearing precision; the film's own visual (not independently
  re-verified frame-by-frame in this pass) is the final authority, and the design below treats
  "regular lattice with domain repetition" as the closest cheap match, flagged as inference
  from the "lattice-like structure" quote plus the "infinite corridor" secondary consensus.
- Color and lighting: the tesseract interior reads warm (amber/gold interior light against a
  dark exterior void) in the released film. **Inference**: no fetched source states an explicit
  hex/Kelvin value or grading rationale; this is drawn from general recollection of the film's
  color grade, not a citation, and is the weakest-sourced trait in this section. The
  Interstellar production is, however, well documented as favoring warm, high-contrast,
  practical lighting throughout (consistent with Hoyte van Hoytema's cinematography choices
  generally), which supports but does not prove the specific warm-interior/dark-void tesseract
  palette. Treat this trait as a design choice justified by "matches secondary consensus and
  differentiates from the existing cool-blue palette," not as a directly sourced fact.
- The "gravity message" (Morse-code dust disturbance, and separately the wristwatch second
  hand) is documented film content (plot-level, not VFX-technical, so not separately cited
  here); the repository's pulse-along-a-strand concept (`pulseNow`/`pulsePast`/`pulseTravel`)
  is a reasonable render-only abstraction of "a signal travels backward along one time-thread
  to a specific past moment," and is worth keeping as a mechanism while changing its visual
  carrier from a labeled ribbon to a traveling pulse on a generic lattice fiber.

## 3. Proposed rendering design

### Technique: fragment-shader raymarch, signed-distance domain repetition, no new geometry

Replace the ribbon/miter vertex pipeline with a full-screen fragment shader that raymarches a
signed-distance field built from:

1. **The lattice.** A repeating unit cell (`opRepLim`/modulo-domain-repetition pattern: `p -
   cellSize * round(p / cellSize)`), each cell an SDF for a thin rectangular room shell (an
   `sdBoxFrame`-style hollow box, not a closed box -- the "beautiful lattice-like structure"
   Franklin describes) unioned with a few interior struts standing in for shelf/desk/window
   silhouettes as *unlabeled* rectangular volumes, not named books. This gives a solid,
   material lattice -- walls with thickness and shading, not wire edges -- at the cost of one
   `mod`/`round` and a handful of box-frame SDF evaluations per march step, independent of how
   many repeats are visible (true domain repetition, not instancing).
2. **The 4D mechanism, kept.** Before evaluating the SDF, transform the marched point through
   the existing `so4FromPair`-derived 4x4 rotation and one of the two existing projections
   (perspective-along-w or stereographic), exactly as `project4` does today
   (`shader/tesseract.vert:100-108`), but now applied per raymarch sample instead of per vertex.
   Practically: pick a `w` coordinate per lattice cell from its position along the repeat axis
   (the "depth into time" axis), run it through `rotation4`, and use the resulting 3D offset to
   *shear/slide* the lattice cell relative to its neighbors as the rotation animates -- this is
   what makes the SO(4) spin visibly warp the corridor instead of spinning a hard cube outline.
   This reuses 100% of `so4.h` and the projection math; nothing about the mechanism changes,
   only its output target (an SDF domain warp instead of a vertex position).
3. **Strands as volumetric fibers.** Represent the "world line" threads as thin capsule/cylinder
   SDFs (`sdCapsule`) running along the repeat axis through each cell, displaced by a low-
   frequency curl-noise field so they read as woven rather than perfectly straight (matching
   "fine threads of light that wove through the scene" -- Franklin, cited above). Light them with
   a simple two-term shading model: a Beckmann-style anisotropic highlight aligned along the
   fiber tangent (cheap: `pow(max(dot(V, T), 0), n)` term, not a full microfacet BRDF) plus a
   diffuse-ish base, so they read as fabric/light-fiber rather than flat-shaded lines. Color
   warm amber/gold (`vec3(1.0, 0.72, 0.35)`-ish), replacing both the current cool-blue edge
   color and the amber-but-flat strand color.
4. **The "message" pulse.** Keep the existing scalar state (`pulseNow`, `pulsePast`,
   `pulseTravel`, `pulseSpeed`) unchanged in `RenderState::TesseractGroup`; feed `pulseTravel`
   into the fragment shader as a traveling bright segment along one strand's arc-length
   parameter (a Gaussian window in arc-length, same shape as today's `litMomentEmission`, just
   evaluated as a raymarch-time emissive boost on the strand SDF's nearest point instead of on a
   vertex attribute).
5. **Depth/void treatment.** Aerial-perspective fog: `radiance = mix(deepVoidColor, cellRadiance,
   exp(-marchDistance * density))`, `deepVoidColor` near-black with a faint warm tint, giving the
   "dark void, warm light source" read and naturally hiding the repeat pattern's far tiling seam
   (cheap, no extra geometry).
6. **Camera drift.** Reuse `tesseractView`/`tesseractViewProjection` unchanged; add a slow
   forward-drift term to `viewDistance` (or a dedicated `corridorDrift` state field) gated by
   `tg.animate`, so the default view *moves through* the corridor rather than orbiting a static
   object -- matching "Cooper floats through" rather than "camera orbits a hypercube."
7. **Bloom/ACES.** No changes needed; write the raymarch result as HDR radiance into
   `texBlackhole` with alpha 1, exactly as the ribbon pass does today
   (`tesseract_renderer.cpp:214-226`), and let the existing bloom/tonemap passes carry the
   "glowing light" look. Re-tune `bloomStrength`/`bloomTone` defaults for this scene only if
   measurement shows the new palette needs it (same mechanism `TESSERACT_RECORD_EXPOSURE`
   already uses for exposure).

Why raymarch over instanced solid geometry: a solid lattice as *geometry* (extruded box meshes)
would need either a bounded number of visible repeats (breaks the "infinite" read at the
horizon, and requires CPU-side visibility culling logic that does not exist today) or GPU
instancing with indirect draws sized to camera position (more code, more state, a new instance
buffer management path). A raymarched SDF gets unbounded, seamless repetition for free via
`mod`, needs no visibility culling (march distance IS the culling), and reuses the existing
"one fullscreen-ish draw into an FBO" shape of `TesseractRenderer::render()` -- only the
vertex/fragment shader pair and the VAO's vertex layout change (a single fullscreen triangle
instead of six vertices per line-segment instance); `ensureResources()`
(`tesseract_renderer.cpp:168-203`) shrinks since there is no longer a large instance buffer
rebuilt on `timeSpan` changes.

### GPU cost estimate

- **RTX 4070 Ti class, 1920x1080:** A box-frame + capsule SDF scene with domain repetition,
  8-16 primitives per cell evaluated at up to ~80-120 raymarch steps (typical for a lattice with
  soft shadows/AO skipped and only a few octaves of curl noise on the strands), is comparable in
  cost to a mid-complexity Shadertoy raymarch (many public examples of infinite architectural
  lattices run at 1080p60 on far weaker GPUs than a 4070 Ti). Budget: 1-3 ms/frame for the
  raymarch itself, well inside the existing frame budget the black-hole fragment integrator
  already uses on this project's hardware baseline (`GPU Fragment` timer in the existing HUD,
  `panels.cpp:917-919`). No new compute dispatch, no new textures beyond what curl-noise (a
  small tileable 3D or 2D texture, generated once) needs.
- **Mesa llvmpipe (CI layout lane):** llvmpipe executes fragment shaders on the CPU via LLVM
  JIT; cost scales with instruction count and step count, not with dedicated hardware texture
  units. The existing CI lane (`scripts/ci/render_output_probe.sh:13`,
  `MESA_LOADER_DRIVER_OVERRIDE=llvmpipe`; `docs/validation/workspace-screenshot-lane.md`) already
  renders the black-hole fragment integrator -- a per-pixel iterative ray integrator, the same
  cost *class* as a raymarch -- at low resolution for its captures, and the tesseract-scene
  workspace capture added in commit `4ce2e67` exercises this scene under llvmpipe today
  (docking/layout check only, not a pixel oracle). A raymarch of similar step count is not a new
  cost regime for that lane; it is the same shape of workload the black-hole shader already
  proves runs there. To keep CI robust, gate step count and noise octaves behind a
  `#ifdef`/uniform "quality tier" the way other passes already do (grep for the project's
  existing quality-tier uniforms in the black-hole fragment shader for the established pattern),
  and drop to a coarser step count (e.g. 40-50 steps, no curl noise, box-only SDF) whenever
  `renderScale` or an explicit quality flag says so -- mirroring `rs.display.renderScale`
  (`render_state.h:245`) already used for the main integrator. Concretely: keep march step count
  and noise octave count as uniforms, not compile-time constants, so the CI capture can run a
  cheap tier without a shader variant.

### Falsifiable, measurable "no longer a wireframe" criteria

See task 4 for the acceptance checks; they are chosen so a capture-based CI test can enforce them
without a human eyeballing every PR.

## 4. Delete / keep / build, and PR breakdown

### Delete

- `FeatureKind`, `LibraryFeature`, `bedroomFeatures()`, `bedroomOutline()`,
  `outlinePolylines()`, `OutlinePolyline`, `selectedTubeMarker()`, `selectedTubeSegments()`,
  `FeatureSelection` (geometry.h:118-147, 190-204, 260-263; geometry.cpp:149-235).
- `extrudeWorldTube()` as a *named-feature* extrusion (geometry.cpp:237-247) -- the underlying
  "extrude a point along w" idea is kept, but reimplemented as a procedural strand field, not a
  per-named-feature polyline list.
- `SegmentInstance`, `SegmentKind`, `packSegmentTag`/`segmentKind`/`segmentCapped`,
  `buildSceneSegments`, `SceneSegmentOptions`, `appendPolyline`/`appendSubdivided*` helpers
  (geometry.h:225-289; geometry.cpp entire instanced-ribbon assembly) -- replaced by the SDF
  raymarch; no instance buffer needed.
- `shader/tesseract.vert`'s entire ribbon-expansion/miter/clip machinery; `shader/tesseract.frag`'s
  per-`vKind` ribbon coloring.
- `TesseractRenderer`'s VAO/VBO instance-buffer setup in `ensureResources()`
  (renderer.cpp:176-202) -- replaced with a single fullscreen-triangle VAO (or none, using
  `gl_VertexID` tricks) the way the project's existing fullscreen post passes already do (see
  `renderToTexture`/`RenderToTextureInfo` used throughout `post_pipeline.cpp`; prefer reusing
  that existing fullscreen-pass helper instead of `TesseractRenderer` hand-rolling its own VAO).
- UI: `"Selected feature"` combo and its help text, `renderTesseractLibraryControls`'s feature-
  index-driven pulse-strand slider (panels.cpp:1004-1037, the parts naming books/windows/desks).
- `RenderState::TesseractGroup::selection` (render_state.h:211); `TesseractFrameInputs::
  selectedStrand`/`markerTime` (renderer.h:101-102).
- Tests: `LibraryOfTime.FeatureNamesAreUniqueAndNonEmpty`,
  `LibraryOfTime.FeatureSelectionTracksWholeTubeAndLitMoment`, `SceneSegments.*`, and all of
  `tests/tesseract_ribbon_gl_test.cpp` (ribbon-specific rasterization tests have no equivalent
  in a raymarch pass).

### Keep unchanged

- `so4.h` in full; `TesseractMesh`/`buildTesseract`/`tesseractVertex` (the 4-cube complex, useful
  as a conceptual/debug reference even if the raymarch does not build a literal mesh from it);
  `projectPerspective`/`projectStereographic`/`StereographicPoint` (reused per-sample in the new
  fragment shader); `advanceOrientation`/`tesseractMotionAt`/`advancePulseTravel`;
  `litMomentEmission`'s Gaussian shape (reused for the pulse window).
- `tesseractView`/`tesseractViewProjection`/`tesseractFraming`/`tesseractZoom`/
  `tesseractViewDistanceAfterInput`/`tesseractFocusTangent`/`tesseractBoundingRadius`.
- `TESSERACT_SPECULATIVE_LABEL`, `layoutSpeculativeLabel()`, and the panel's label rendering --
  explicit owner instruction to keep it.
- The scene dispatch in `main.cpp` (1314-1337), zoom redirect (559-566), shutdown calls
  (2138-2139), GPU timer plumbing (`gpuTimers.tesseract`).
- `renderTesseractRotationControls` and `renderTesseractProjectionControls` in full.
- `tests/tesseract_geometry_test.cpp`'s `TesseractGeometry.*`/`TesseractProjection.*`/
  `TesseractAnimation.*` groups; `tests/tesseract_framing_test.cpp`;
  `tests/tesseract_motion_test.cpp`; `tests/tesseract_label_test.cpp`.

### New, player-facing UI (few controls, no jargon)

Replace `renderTesseractLibraryControls` and `renderTesseractAppearanceControls` with a small
set under a renamed section, e.g. "Corridor and light":

- `"Corridor density"` (lattice cell size / repeat frequency) -- replaces "Time span T" in
  spirit (still controls how much of the time-axis structure is visible per screen).
- `"Drift speed"` -- forward camera drift through the corridor (new, replaces nothing).
- `"Strand glow"` -- replaces `edgeIntensity`/`strandIntensity`/`sliceIntensity` (three sliders
  collapse to one or two: fiber emissive intensity, fog/void darkness).
- `"Message pulse"` checkbox + `"Pulse speed"` -- keep, unchanged semantics, renamed away from
  "strand"/feature language if the strand a pulse rides is now anonymous.
- Keep rotation and projection sections as-is.

### Acceptance checks (falsifiable, capture-based)

1. **Non-wireframe coverage.** In a fixed-camera capture, the fraction of pixels with radiance
   above a low floor (e.g. > 0.02 in linear HDR before tonemap) must exceed a threshold (e.g.
   35-50% of the frame) -- a thin-line wireframe cannot reach this; a lit lattice with fog can.
   Falsifier: coverage stays under, say, 15% (the old ribbon pass's rough ballpark, to be
   measured against current captures as the "before" baseline) -- indicates it is still
   line-dominated.
2. **Warm hue histogram.** Over the same capture, the circular mean hue of pixels above the
   coverage floor should fall in the amber/gold band (roughly hue 25-50 degrees on a 0-360 HSV
   wheel) for a majority of qualifying pixels, replacing the current cool-blue-dominant edge
   color. Falsifier: hue histogram peak sits in blue/cyan (180-240 degrees), meaning the old
   palette leaked through.
3. **Lattice periodicity.** 1D or 2D autocorrelation of the luminance capture along the
   corridor/depth axis should show a clear secondary peak at a lag matching the configured cell
   size (in screen-space, accounting for perspective -- check near the horizon/vanishing region
   where the repeat is most nearly periodic in log-depth). Falsifier: no discernible peak (flat
   autocorrelation) means the repetition is not reading as a lattice at all.
4. **Pulse travel.** Over N captured frames with `pulseEnabled = true`, the screen-space (or
   parametric arc-length) position of the brightest short-lived hotspot must move monotonically
   at a rate consistent with `pulseSpeed`, matching how `tesseract_motion_test.cpp` already
   checks `advancePulseTravel` at the state level -- this is a rendering-level companion check,
   not a replacement.
5. **llvmpipe survival.** The existing workspace-screenshot lane capture of the Tesseract scene
   (added in commit `4ce2e67`, `scripts/ci/workspace_screenshot_probe.sh`) must keep passing at
   its cheap quality tier with no crash, no shader compile failure, and no timeout increase
   beyond the lane's existing budget.
6. **Exposure recalibration.** A `tesseract_exposure_gl_test.cpp`-equivalent test must measure
   the new pass's actual 99th-percentile radiance distribution (as the current test's docstring
   already documents doing for ribbons) and pin a new `TESSERACT_RECORD_EXPOSURE`-equivalent
   constant to it, not carry the old ribbon-derived value forward unchecked.

### PR breakdown (2-3 PRs)

**PR 1 -- Raymarch core, lattice + strands, no UI rename yet.**
Replace `shader/tesseract.vert`/`shader/tesseract.frag` with a fullscreen-triangle vertex shader
and an SDF raymarch fragment shader implementing the lattice + strand + fog + SO(4) domain warp
(items 1-3, 5 above). Rewrite `TesseractRenderer::ensureResources()`/`render()` to drop the
instance-buffer path in favor of the project's existing fullscreen-pass convention. Delete the
rejected geometry functions and their tests (`FeatureKind` through `buildSceneSegments`, and
`tests/tesseract_ribbon_gl_test.cpp`, `SceneSegments.*`, `LibraryOfTime.FeatureNames*`,
`LibraryOfTime.FeatureSelection*`). Add acceptance checks 1-3 as a new
`tests/tesseract_raymarch_gl_test.cpp`. Recalibrate exposure (check 6). Keep the old UI wired to
whatever uniforms still exist even if some sliders are temporarily no-ops, to keep the PR buildable
and bisectable; do not rename UI yet.

**PR 2 -- Message pulse, camera drift, and UI cleanup.**
Wire `pulseNow`/`pulsePast`/`pulseTravel` into the raymarch as a traveling emissive window on a
strand's arc-length coordinate (item 4); add the drift-speed camera term (item 6). Replace
`renderTesseractLibraryControls`/`renderTesseractAppearanceControls` with the new "Corridor and
light" panel section, delete `FeatureSelection`/`selectedStrand`/`markerTime` from
`RenderState`/`TesseractFrameInputs`. Add acceptance check 4.

**PR 3 (optional, split out if PR 1/2 run long) -- Tuning pass and CI quality tier.**
Add the explicit quality-tier uniform (step count, noise octaves) gated for llvmpipe (check 5),
tune bloom/ACES interaction for the new warm palette (check 2 threshold satisfied), and record
before/after captures in `docs/validation/` the way other rendering-lane docs already do.

## Open decisions for the owner

1. **Lattice arrangement.** The plan assumes a regular rectilinear repeat (cheapest, matches
   "lattice-like structure" literally). If the owner wants a more literal "corridor with rooms
   receding to a vanishing point" read (closer to some fan descriptions of "floating down a
   hallway"), the domain-repetition axis should be biased along the camera's forward/drift axis
   rather than isotropic; this is a shader-parameter choice, not an architecture change, but it
   changes which SDF pattern (grid vs. radial/tunnel) is primary.
2. **Warm palette specifics.** No source fetched here pins an exact color; recommend picking
   values during PR 1 by eye against a reference capture and letting acceptance check 2's hue
   band (25-50 degrees) be the durable, checkable constraint rather than a specific hex value in
   the plan.
3. **Strand density vs. performance headroom.** Whether strands render as a sparse set of
   "featured" fibers (a few dozen, cheap) or a dense dust-like field (hundreds, matching "every
   object left a trail") is a cost/richness tradeoff; recommend starting sparse in PR 1 (bounds
   the GPU-cost estimate above) and letting the llvmpipe check (5) gate any increase.
