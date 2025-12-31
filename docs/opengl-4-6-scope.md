# OpenGL 4.6 Scope and Effort

This project targets OpenGL 4.6 (GLSL 460). The items below capture the migration scope,
validation needed, and known platform implications.

## Applied changes
- GLFW requests a 4.6 core context and validates the created context at runtime.
- glbinding is initialized via `glbinding::initialize(glfwGetProcAddress)` for core 4.6 entry points.
- ImGui OpenGL backend uses `#version 460`.
- All shaders now declare `#version 460 core` (compute shader updated as well).

## Validation checklist
- Verify the app boots on at least one NVIDIA and one AMD/Intel stack.
- Confirm `glGetIntegerv(GL_MAJOR_VERSION/MINOR_VERSION)` reports 4.6.
- Run `validate-shaders` target (glslangValidator in OpenGL mode).
- Check that ImGui renders with the 460 shader version.
- Exercise compute shader path if/when it is wired into runtime.

## Platform implications
- macOS does not support OpenGL 4.6; the app will fail to create a context.
- Linux/Windows require updated GPU drivers that expose OpenGL 4.6.
- Headless CI cannot validate runtime GL 4.6; CI remains build-only.

## Follow-up work if issues appear
- Bump or pin Conan packages (GLFW/glbinding/ImGui) if 4.6 symbols are missing.
- Add a startup log banner with GL_VENDOR/GL_RENDERER/GL_VERSION for debugging.
- Gate optional features behind extensions if some drivers report 4.6 but miss behavior.

## Compute geodesic path plan
- Keep fragment and compute paths feature-parity (camera basis, step size, disk params).
- Dispatch in tiles (`tileOffset`, `tileSize`) for deterministic perf sweeps.
- Add compare mode: render fragment + compute, diff in CPU/SSBO, and emit CSV metrics.
- Capture PPMs for threshold sweeps; fail on error budget regressions.

## References inside repo
- Context setup: `src/main.cpp`
- Shader versions: `shader/*.frag`, `shader/*.vert`, `shader/*.comp`
- Shader validation: `CMakeLists.txt` target `validate-shaders`
