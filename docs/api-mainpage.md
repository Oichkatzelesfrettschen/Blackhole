# Blackhole API Documentation

This is the Doxygen entry point for the generated API documentation.

## Scope

The generated API docs focus on the native implementation surfaces that the
build produces today:

- `src/` runtime, physics, and renderer code
- `src/cuda/` CUDA backend code when enabled
- `src/blender_bridge/` C ABI used by the Blender addon
- `shader/` authored GLSL programs and includes
- `tools/` and `bench/` helper executables

## Product surfaces

- `Blackhole`: shared desktop application
- `BlackholeGLSL`: desktop executable with the GLSL/OpenGL lane only
- `BlackholeCUDA`: desktop executable with the CUDA lane forced on
- `libblackhole_bridge.so`: Blender bridge shared library

## Verification companions

API documentation is paired with:

- the measured repo inventory in `build/*/reports/repo_truth.md`
- the claims verifier report in `build/*/reports/physics_claims.md`

Those reports are the source of truth for build/test presence. This Doxygen
surface describes the implementation interfaces themselves.
