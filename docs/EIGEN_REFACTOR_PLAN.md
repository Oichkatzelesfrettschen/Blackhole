# Eigen Refactor Plan

## Goals
- Define a clean CPU math boundary while keeping GLM on the render path.
- Preserve C++23 and deterministic numeric behavior across platforms.
- Align data layout for FlatBuffers + HighFive IO.

## Scope
- CPU physics: `src/physics/*`, LUT generation, `bench/physics_bench.cpp`
- Render path: keep GLM for shader uniforms and camera matrices
- IO: pack math arrays in row-major and document conversions

## Phases
1. Boundary types
   - Add math types header (`math::Vec3/Mat3/Mat4`) with GLM default.
   - Introduce conversion helpers for GLM <-> Eigen.
2. Physics migration
   - Move geodesics/Kerr/Schwarzschild kernels to Eigen types.
   - Keep shader-facing data in GLM; convert at upload boundaries.
3. Data IO alignment
   - Use `Eigen::Map` for FlatBuffers/HighFive buffers (row-major).
   - Add schema notes for matrix storage and endian expectations.
4. SIMD + parallel
   - Evaluate Eigen vectorization flags vs xsimd in benchmarks.
   - Use Taskflow to batch CPU ray steps / LUT generation.
5. Validation
   - Add parity checks in `physics_test` and extend bench results.
   - Track tolerances for each kernel migration.

## Interop Guidelines
- Avoid implicit conversions; keep helper functions explicit.
- Use `Eigen::Map` to avoid copies when moving to/from IO buffers.
- Convert to GLM right before uniform upload.

## Risks / Constraints
- Eigen 5 API changes remain deferred; stick to 3.4.0 until stable.
- Keep shader data in GLM to avoid layout mismatches.

## Deliverables
- `src/physics/math_types.h`
- `src/physics/math_interop.h`
- `bench/physics_bench.cpp` updates for GLM vs Eigen
