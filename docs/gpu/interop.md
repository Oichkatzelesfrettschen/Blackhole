# Compute/Fragment Interop Checklist

Scope: align compute and fragment shader outputs for the ray integrator and
support parity comparisons with minimal drift.

## References
- OpenGL Wiki: Compute Shader
  https://www.khronos.org/opengl/wiki/Compute_Shader
- OpenGL Wiki: GLSL Type Qualifier (precision + invariant qualifiers)
  https://www.khronos.org/opengl/wiki/GLSL_Type_Qualifier

## Project Checklist
- Shared math:
  - Keep raygen/trace/shading in shared includes and avoid stage-specific built-ins.
  - Ensure `#version 460` stays first line; include shared files after uniforms when required.
- Inputs and mapping:
  - Use pixel centers (`gl_FragCoord.xy` vs `gl_GlobalInvocationID + 0.5`).
  - Keep UV aspect correction identical across stages.
  - Lock a single frame time for parity captures.
- Uniform parity:
  - Align names/types across compute + fragment: `cameraPos`, `cameraBasis`, `fovScale`,
    `depthFar`, `kerrSpin`, `iscoRadius`, `interopMaxSteps`, `interopStepSize`.
  - Clamp step counts/size once before setting uniforms on both paths.
- Resource binding:
  - Bind matching LUTs and cubemaps; use identical fallbacks.
  - After compute dispatch, apply `glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT)`
    before sampling outputs.
- Precision and determinism:
  - Avoid derivatives (`dFdx/dFdy`) or other fragment-only built-ins in shared code.
  - Consider `invariant` on outputs for strict parity if needed.
  - Precision qualifiers in desktop GLSL do not change results; avoid relying on them.
- Debug and comparison:
  - Force parity mode during compare sweeps.
  - Compare pre-postprocess linear output and capture diffs for outliers.

## SPIR-V pipeline alignment
- Compile once, specialize often:
  - Use SPIR-V binaries (`glShaderBinary` + `glSpecializeShader`) to avoid runtime GLSL
    compile variance across vendors.
  - Prefer explicit `layout(location = ...)` on varyings and `layout(binding = ...)`
    for resources to keep compute/fragment bindings in lockstep.
- Reflection:
  - Use SPIRV-Cross to build a binding map; avoid `glGetUniformLocation` on hot paths.
- Optimization:
  - Run `spv::Optimizer` performance passes to canonicalize math before driver ingestion.

## Overdraw control (fragment cost)
- Use meshoptimizer to reorder triangle submission for early-Z wins:
  - `meshopt_optimizeOverdraw` for opaque/alpha-tested geometry.
- Favor tighter bounds or explicit depth pre-pass for dense accretion disk geometry.
