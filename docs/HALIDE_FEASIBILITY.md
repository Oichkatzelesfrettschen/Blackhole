# Halide Feasibility (Cleanroom)

This document scopes a minimal Halide pilot for CPU-side kernels. The goal is
to verify that Halide can provide reproducible scheduling wins without adding
runtime coupling to the OpenGL path.

## Key notes
- Halide is not on conancenter; treat it as optional tooling (FetchContent or
  prebuilt SDK) gated behind `-DENABLE_HALIDE=ON`.
- Requires a compatible LLVM/Clang toolchain; pin the version to avoid ABI
  churn across machines.
- Best fit: offline LUT generation and CPU validation kernels (not the real-time
  render loop).

## Pilot kernel (proposed)
1. Implement emissivity LUT generation in Halide (1D kernel).
2. Compare output against current C++ LUT path (max abs error).
3. Benchmark throughput and export CSV (Halide vs baseline).

## Integration sketch
- Add `cmake/FindHalide.cmake` or use FetchContent for Halide source/SDK.
- Provide `src/halide/halide_kernels.*` with explicit schedule functions.
- Keep outputs identical to existing CSV/HDF5 formats (no runtime dependency).

## Risks
- Toolchain setup friction (LLVM mismatch).
- Increased build times if Halide is compiled from source.
- Potential divergence between Halide outputs and SIMD baseline if schedules
  are misconfigured.
