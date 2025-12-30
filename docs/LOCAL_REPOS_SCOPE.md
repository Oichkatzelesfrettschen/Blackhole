# Local Repos Scope (~/Github)

This document captures a first-pass inventory of local repos outside
Blackhole and OpenUniverse. It is a lightweight triage list; deeper
audits will be added per project priority.

## Notable repos (initial triage)
- MangoHud: HUD/overlay reference (cleanroom HUD port).
- graphics-programming, ancient_compute: rendering/math reference patterns.
- microwindows64: low-level windowing/UI patterns.
- openuniverse, openuniverse-common, compact-common: physics references.
- cern-analysis-common: data/IO patterns.

## Focus targets (next audit pass)
- graphics-programming:
  - portable-gl, sgi-software-renderer, tinygl: software rasterization + fixed pipeline ideas.
  - ogl-sample: OpenGL samples (shader patterns, FBO layouts).
  - renderers-comparison: perf/feature comparison notes (baseline expectations).
- MangoHud: FPS/frametime aggregation and overlay layout choices.
- microwindows64: minimal UI/event loop patterns (potential fallback HUD/input).
- Xinim: low-level C/C++ graphics experiments (renderer/text loop patterns).

## Recent notes
- graphics-programming/GRAPHICS_HARMONIZATION_ARCHITECTURE.md highlights duplicated matrix
  math, clipping, and viewport transforms across TinyGL/PortableGL/SGI renderer lines; useful
  for potential CPU fallback or validation reference.
- Xinim `commands/mined_unified.hpp` defines a Renderer concept with `clear/present/draw_text`,
  plus text buffer rendering in `mined.hpp`; useful for HUD/text overlay ideas and UTF-8 layout.

## Expanded notes (audit pass 2)
- openuniverse: monorepo hub with submodules; relevant physics sources are compact-common,
  nubhlight (GRMHD), tardis (radiative transfer), grb-common/ASGARD/boxfit/JetFit (GRB fits).
- MangoHud: OpenGL/Vulkan overlay; reference for HUD layout, frametime aggregation, vsync notes,
  and configuration surface (env/preset files).
- graphics-programming: includes portable-gl, tinygl, SGI renderer, and OpenGL samples; use as
  cleanroom reference for CPU-side raster math and validation utilities.
- Xinim: C++23 OS; large scope, but text-render paths (mined renderer) are a candidate for HUD
  layout/metrics formatting ideas.
- microwindows64: small windowing/Nano-X stack with input notes (KMS/libinput); possible UI/HUD
  patterns, not a direct dependency.
- cern-analysis-common/openperception: data-analysis repositories; low immediate relevance but
  may supply validation or I/O patterns later.

## Domain tags (coarse)
- Physics: openuniverse, compact-common, nubhlight, tardis, grb-common/ASGARD/boxfit/JetFit.
- Rendering/HUD: MangoHud, graphics-programming, Xinim (text renderer), microwindows64.
- Data/Analysis: cern-analysis-common, openperception, MathScienceCompendium, PhysicsForge.
- System/tooling: classic71, posix-compliance, ryzen-boost-service, system-rice-audit.

## Inventory snapshot (file-type signal)
| Repo | Dominant types (top 5) | Preliminary domain notes |
|------|-------------------------|--------------------------|
| 4-bit | .rs, .bmp, .pdf, .toml, .txt | Rust tooling + assets; potential procedural/renderer snippets. |
| AGL | .py, noext, .json, .html, .h | Large mixed codebase; likely system tooling. |
| Blackhole | noext, .py, .h, .md, .c | Current project baseline. |
| KeenKenning | .o, .json, .txt, .bin, .cmake | Binary-heavy; treat as data/reference only. |
| MangoHud | .h, .cpp, .py, .c, .yml | HUD overlay reference. |
| Synthesis-Dark-Theme | .png, .svg, noext, .scss, .svgz | Visual assets; not core physics. |
| Xinim | .c, .s, .cpp, .h, .hpp | Systems/renderer experiments; possible math snippets. |
| ancient_compute | .md, .py, .ts, .tex, .csv | Notes + experiments; possible equations. |
| apex-tux | .rs, .toml, .png, .bmp, .md | Rust + assets; minor relevance. |
| archpower | noext, .asc, .txt, .patch, .toml | OS/system tooling; likely low relevance. |
| cern-analysis-common | .py, noext, .toml, .md | Data/IO + analysis; possible calibration patterns. |
| classic71 | .h, .c, .asm, .md, noext | Low-level C/ASM patterns. |
| feuerbird_exokernel | .html, .make, .cmake, .ts, .d | Tooling/build-heavy; minimal direct physics. |
| graphics-programming | .h, .out, .c, .cpp, .html | Rendering samples; likely useful. |
| heirloom-project | .c, noext, .mk, .h, .1 | C tooling; low relevance. |
| microwindows64 | .c, .ttf, .o, .d, .h | Windowing/UI patterns; potential HUD ref. |
| openmarco | .c, .h, .po, .png, .gmo | C + localization assets. |
| openperception | .png, .jpg, .pdf, .md, .py | Papers/assets; possible reference material. |
| openrival-tools | .md, .txt, .py, noext, .pcapng | Tooling; minor relevance. |
| openuniverse | .h, .py, .md, .json, .cxx | Primary physics reference base. |
| openuniverse-common | .py, .md, .toml, .typed | Spine/adapter patterns. |
| posix-compliance | .c, .txt, .xml, .sh, noext | OS compliance tests; low relevance. |
| puzzles | .png, .make, .cmake, .h, noext | Assets + build; low relevance. |
| ryzen-boost-service | noext, .sh, .py, .rules, .service | System tuning; low relevance. |
| silksurf | .h, .c, noext, .png, .html | Rendering assets + C; potential UI refs. |
| sys71src | .a, .h, .p, .c, .txt | Binary-heavy; data/reference. |
| system-rice-audit | .conf, .md, .py, .sh | System config audit; low relevance. |
| xv6-projects | .c, noext, .h, .s, .1 | OS kernel projects; low relevance. |

## Next Steps
1. Validate/expand domain tags with file-level audits for priority repos.
2. Select cleanroom-port candidates with explicit equations or algorithms.
3. Document any licensing constraints before porting.
