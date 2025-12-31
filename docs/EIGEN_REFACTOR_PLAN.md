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
   - Add math types header (`math::Vec2/Vec3/Vec4/Mat2/Mat3/Mat4/Quat`) with GLM default and convenience helpers such as `dataPtr()` for raw access.
   - Add a small `math_interop.h` containing explicit GLM <-> Eigen conversion helpers for Vec2/Vec3/Vec4/Mat3/Mat4/Quat.
   - Opt-in to Eigen by defining `BLACKHOLE_USE_EIGEN` at build time (Eigen headers must be present via Conan).
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
- Eigen 5 API changes remain deferred; 5.0.1 exists on conancenter but needs
  an API audit before adoption (matrix/tensor changes).
- Keep shader data in GLM to avoid layout mismatches.

## Version alignment (2025-12-30)
- GLM: 1.0.1 (shader parity; keep for render path).
- Eigen: evaluate 5.0.1 vs 3.4.0 stability before migration.

## Deliverables
- `src/physics/math_types.h`
- `src/physics/math_interop.h`
- `bench/physics_bench.cpp` updates for GLM vs Eigen
