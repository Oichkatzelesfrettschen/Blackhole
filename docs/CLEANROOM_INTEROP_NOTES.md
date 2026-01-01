# Cleanroom Interop Notes

Scope: shader parity and shared integration logic for compute/fragment paths.

## Shared shader modules
- `shader/include/interop_raygen.glsl`: pixel mapping + ray direction.
- `shader/include/interop_trace.glsl`: geodesic integration + shading.

Both compute (`shader/geodesic_trace.comp`) and fragment
(`shader/blackhole_main.frag` in parity mode) include the same
raygen/trace code to reduce divergence.

## Parity mode

Fragment parity path (compare sweeps):
- `interopParityMode` gates the parity branch in `blackhole_main.frag`.
- Uses `bhTraceGeodesic` + `bhShadeHit` from `interop_trace.glsl`.

Compute path:
- Always uses `bhTraceGeodesic` + `bhShadeHit` from `interop_trace.glsl`.

## Debug flags

`bhDebugFlags` is a bitmask used inside `interop_trace.glsl`:
- `1`: flag NaN/Inf and paint magenta.
- `2`: flag out-of-range radii and paint yellow.
- `3`: both.

Enable via:
```bash
BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=3 ./build/Riced/Debug/Blackhole
```

## Parity sweep findings

Baseline compare sweeps showed sensitivity to integration step size:
- Default steps (300/0.1): 2/12 preset failures (post background LOD bias defaults).
- 600 steps + 0.05 step: 2/12 preset failures.
- 1000 steps + 0.02 step: 0/12 preset failures.

Conclusion: divergence is dominated by integration error near high curvature
rather than NaN/Inf or range issues.

## OpenGL 4.6 standardization impact
- `docs/OPENGL_45_46_SHADER_REPORT.md` summarizes 4.5 to 4.6 changes that affect
  cleanroom parity, notably SPIR-V ingestion and gl_DrawID availability.
