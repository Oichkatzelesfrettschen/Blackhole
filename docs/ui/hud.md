# HUD Overlay (Blackhole)

This document describes the lightweight HUD overlay used by Blackhole for
performance and debug information.

## Overview

- The default overlay uses `stb_easy_font` (ASCII-only) and renders directly
  as geometry (cheap, no font atlas required).
- A richer TrueType/SDF backend may be added later for UTF-8 and typographic
  control.

## API

- `HudOverlay` (RAII): `init()` / `shutdown()`; `setOptions()`, `setLines()`,
  `render(width, height)`.
- Options are described in `HudOverlayOptions` (scale, margin, lineSpacing,
  align, origin, drawBackground, fontFile).
- Per-line color/background via `HudOverlayLine`.

## Environment

- Enable the performance HUD using `BLACKHOLE_PERF_HUD` (env var); default
  scale can be set via `BLACKHOLE_PERF_HUD_SCALE`.

## Performance

- Keep lines short and avoid per-frame reallocation when possible. Use
  `setLines()` on a persistent overlay instance to avoid reallocating vectors
  frequently in hot paths.

## Integration Notes

- The overlay is integrated in `main.cpp` to show controls and perf lines.
- Shaders used: `shader/overlay_text.vert` and `shader/overlay_text.frag`.

## Future Work

- Add SDF/TrueType backend with glyph atlas and GPU caching.
- Add batching across multiple overlays, hit-testing, and alignment helpers.
