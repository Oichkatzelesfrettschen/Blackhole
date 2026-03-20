# OpenGL 4.5 vs 4.6 Shader Pipeline Report

This report distills the OpenGL 4.5 to 4.6 standardization trajectory and
summarizes the programmable shader stages with engine-facing implications.
It is intended as a reference for Blackhole's rendering backend, shader
asset pipeline, and cleanroom parity work.

## Executive summary
- OpenGL 4.5 focused on Direct State Access (DSA) to reduce bind churn and
  driver validation overhead.
- OpenGL 4.6 standardized several key extensions, enabling a modern,
  GPU-driven pipeline without vendor-specific fallbacks.
- The most impactful 4.6 additions for engine architecture are SPIR-V
  ingestion, shader draw parameters (gl_DrawID), and indirect draw count
  commands that allow the GPU to drive visibility.
- Blackhole now supports a multi-draw main pass with per-draw SSBO data
  and optional indirect-count dispatch, plus SPIR-V runtime loading.

## Programmable stages: roles and critical built-ins

### Vertex Shader (VS)
- Role: per-vertex transform and attribute routing into the pipeline.
- Key built-ins:
  - gl_VertexID: vertex index (from element buffer or draw loop).
  - gl_InstanceID: instance index (starts at 0, does not include base).
  - gl_BaseInstance: base instance (core in 4.6, extension in 4.5).
  - gl_DrawID: draw index inside multi-draw batch (core in 4.6).
- Notes: for multi-draw indirect, gl_DrawID is essential for indexing
  per-draw data without per-draw uniform updates.
  gl_InstanceID always starts at 0, so gl_BaseInstance must be added to
  reach the true instance index when using base-instance draws.

### Tessellation Control Shader (TCS)
- Role: per-patch processing and tessellation level selection.
- Key built-ins:
  - gl_in: array of input control points from VS.
  - gl_TessLevelOuter / gl_TessLevelInner: drive the fixed-function
    tessellation primitive generator.
- Notes: use barrier() when reading/writing shared patch outputs.
  Cull patches early by driving tess levels to zero.

### Tessellation Evaluation Shader (TES)
- Role: evaluate generated vertices from tessellation coordinates.
- Key built-ins:
  - gl_TessCoord: barycentric or UV coordinates, based on domain type.
- Notes: distance-based LOD is mandatory to avoid micro-tessellation.

### Geometry Shader (GS)
- Role: per-primitive amplification or culling.
- Key built-ins:
  - gl_Layer: layered rendering to array/cubemap faces.
  - gl_ViewportIndex: per-primitive viewport selection.
- Notes: GS is often a performance bottleneck. Prefer compute culling or
  instancing unless layered rendering is required.

### Fragment Shader (FS)
- Role: per-fragment shading and output to render targets.
- Key built-ins:
  - gl_FragCoord: window-space position and depth.
  - gl_FrontFacing: front/back face flag.
  - gl_HelperInvocation: identifies helper fragments (4.5+ core).
- Notes: guard side effects (imageStore, atomics) to avoid helper writes.

### Compute Shader (CS)
- Role: general-purpose GPU compute, independent of rasterization.
- Key built-ins:
  - gl_GlobalInvocationID, gl_LocalInvocationID, gl_WorkGroupID.
- Notes: ideal for GPU-driven culling, prefix sums, and draw command
  compaction. 4.6 standardizes subgroup operations via core integration
  of group-vote and ballot behavior.

## Stage-specific deep dive notes
### Vertex + draw parameters
- gl_DrawID enables a single multi-draw call to index per-draw SSBO data.
- gl_BaseInstance is required to recover true instance IDs; gl_InstanceID
  alone ignores baseInstance offsets.

### Tessellation risks
- Micro-tessellation (sub-pixel triangles) can explode raster cost; drive
  tess levels by screen-space error in the TCS.

### Geometry shader constraints
- GS amplification forces buffering between stages; it is typically slower
  than compute-driven culling or instancing for large batches.

### Fragment helper invocations
- Helper fragments execute to support derivatives; guard side effects with
  `if (!gl_HelperInvocation)` to avoid corrupting buffers or images.

### Compute subgroup ops
- 4.6 core includes group vote/ballot behavior. These intrinsics enable
  lane-level compaction and work reduction without shared memory.

## Standardization changes: 4.5 to 4.6

| Capability | 4.5 status | 4.6 status | Why it matters |
| --- | --- | --- | --- |
| SPIR-V ingestion (GL_ARB_gl_spirv) | Extension | Core | Offline compilation, consistent shader validation, Vulkan parity. |
| Draw parameters (GL_ARB_shader_draw_parameters) | Extension | Core | gl_DrawID and gl_BaseInstance enable MDI without per-draw uniforms. |
| Indirect count draw (GL_ARB_indirect_parameters) | Extension | Core | GPU can write draw count and drive visibility without CPU readback. |
| Anisotropic filtering (GL_EXT_texture_filter_anisotropic) | Extension | Core | Baseline visual quality for oblique textures. |
| Polygon offset clamp (GL_EXT_polygon_offset_clamp) | Extension | Core | Stable shadow biasing, reduces peter-panning. |
| Parallel shader compile (GL_KHR_parallel_shader_compile) | Extension | Extension (common in 4.6 drivers) | Async shader linking to avoid main-thread stalls. |
| No-error context (GL_KHR_no_error) | Extension | Extension (often shipped with 4.6) | Shipping-only mode to reduce CPU validation overhead. |

### SPIR-V ingestion (GL_ARB_gl_spirv)
- Offline compilation removes driver-front-end variability and reduces
  first-run stutter. OpenGL 4.6 consumes SPIR-V via glShaderBinary and
  glSpecializeShader, matching the Vulkan pipeline structure.

### Blackhole SPIR-V toolchain
- Shader compilation uses shaderc to produce SPIR-V binaries at build/load time.
- SPIRV-Tools runs performance passes to strip dead code and normalize math.
- SPIRV-Cross is used for reflection to precompute bindings, reducing runtime
  `glGetUniformLocation` calls.

### Indirect parameters (GL_ARB_indirect_parameters)
- glMultiDraw*IndirectCount allows the GPU to write the draw count, enabling
  fully GPU-driven visibility without CPU readback.

### Shader draw parameters (GL_ARB_shader_draw_parameters)
- gl_DrawID and gl_BaseInstance are core, enabling draw/instance indexing
  inside MDI batches without per-draw uniform updates.

### Anisotropic filtering & polygon offset clamp
- 4.6 guarantees baseline texture fidelity and stable shadow biasing without
  vendor checks.

## Engine-facing implications for Blackhole

1. Shader asset pipeline
   - Prefer offline shader compilation to SPIR-V and load via
     glShaderBinary + glSpecializeShader when GL 4.6 is available.
   - Keep GLSL source fallback for 4.5 drivers.
   - Runtime toggle: set `BLACKHOLE_USE_SPIRV=1` to load `*.spv` files
     alongside the GLSL sources.
   - Script: `scripts/compile_shaders_spirv.sh` generates `*.spv` artifacts.
   - Tool: `tools/spirv_bake.cpp` (CMake target `spirv_bake`) compiles GLSL
     to SPIR-V with optional optimization + reflection (shaderc/spirv-tools).
   - If SPIR-V link fails, the runtime falls back to GLSL compilation.
   - Explicit varying locations are recommended to ensure link compatibility
     across separately compiled SPIR-V stages.

2. GPU-driven rendering
   - Use gl_DrawID to index per-draw data in SSBOs for multi-draw batches.
   - Use glMultiDraw*IndirectCount when available to avoid CPU readback.
   - Runtime toggles: `BLACKHOLE_MULTIDRAW_MAIN=1`,
     `BLACKHOLE_MULTIDRAW_INDIRECT_COUNT=1`, `BLACKHOLE_MULTIDRAW_OVERLAY=0`.

3. Fragment safety
   - Guard imageStore and atomic operations with !gl_HelperInvocation.

4. Tessellation LOD
   - Always drive tessellation levels based on screen-space metrics to
     prevent micro-triangles.

5. Portability
   - If GL_VERSION >= 4.6, features above are guaranteed.
   - For 4.5, check extensions individually and fall back gracefully.
   - macOS is capped at 4.1 and does not support 4.5/4.6 features.

## Suggested API checks (pseudo)
```cpp
const char *version = reinterpret_cast<const char *>(glGetString(GL_VERSION));
bool is46 = version && std::string(version).find("4.6") != std::string::npos;
bool hasDrawParams = is46 || hasExtension("GL_ARB_shader_draw_parameters");
bool hasIndirectCount = is46 || hasExtension("GL_ARB_indirect_parameters");
bool hasSpirv = is46 || hasExtension("GL_ARB_gl_spirv");
```

## Recommended adoption roadmap
1. Add SPIR-V offline build step and runtime loader (keep GLSL fallback).
2. Migrate multi-draw paths to gl_DrawID driven SSBO indexing.
3. Add indirect draw count pipeline for GPU culling (compute writes count).
4. Enable anisotropic filtering baseline and optional polygon offset clamp.
5. Consider no-error context option for release builds after validation.

## Current Blackhole status (2025-12-31)
| Feature | Status |
| --- | --- |
| SPIR-V runtime load | Optional via `BLACKHOLE_USE_SPIRV=1` |
| SPIR-V build step | `scripts/compile_shaders_spirv.sh` |
| SPIR-V link hardening | Explicit varying locations for key stages |
| SPIR-V tooling | `spirv_bake` target (shaderc + spirv-tools + spirv-cross) |
| gl_DrawID usage | Multi-draw main path + probe via `BLACKHOLE_DRAWID_PROBE=1` |
| Indirect draw count | Implemented via `BLACKHOLE_MULTIDRAW_INDIRECT_COUNT=1` |
| Anisotropic filtering | Enabled by default (clamped to 8x) |
| Polygon offset clamp | Not used (no shadow map path yet) |
| Parallel shader compile | Optional via `BLACKHOLE_PARALLEL_SHADER_COMPILE=1` |
| No-error context | Optional via `BLACKHOLE_NO_ERROR_CONTEXT=1` |
