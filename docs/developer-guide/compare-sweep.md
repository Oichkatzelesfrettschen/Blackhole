# Compare Sweep Guide

Purpose: run deterministic compute vs fragment parity sweeps and capture diffs.

Outputs:
- `logs/compare/compare_summary.csv` (diff stats + thresholds)
- `logs/compare/compare_uniforms.csv` (interop inputs per preset)
- `logs/compare/compare_<idx>_{compute,fragment,diff}.ppm` (optional)

## Quick start

Baseline sweep (no extras, CSV only):
```bash
BLACKHOLE_COMPARE_SWEEP=1 \
BLACKHOLE_COMPARE_BASELINE=1 \
BLACKHOLE_COMPARE_WRITE_OUTPUTS=0 \
BLACKHOLE_COMPARE_WRITE_DIFF=0 \
./build/Riced/Debug/Blackhole
```

Capture PPMs + diff images:
```bash
BLACKHOLE_COMPARE_SWEEP=1 \
BLACKHOLE_COMPARE_BASELINE=1 \
BLACKHOLE_COMPARE_WRITE_OUTPUTS=1 \
BLACKHOLE_COMPARE_WRITE_DIFF=1 \
./build/Riced/Debug/Blackhole
```
## Environment flags

Core:
- `BLACKHOLE_COMPARE_SWEEP=1`: enable preset sweep capture.
- `BLACKHOLE_COMPARE_BASELINE=1`: disable extras (disk/noise/GRMHD/background).
- `BLACKHOLE_COMPARE_WRITE_OUTPUTS=1`: write compute/fragment PPMs.
- `BLACKHOLE_COMPARE_WRITE_DIFF=1`: write diff PPMs.
- `BLACKHOLE_COMPARE_WRITE_SUMMARY=0`: disable CSV output.

Overrides:
- `BLACKHOLE_COMPARE_MAX_STEPS=<int>`
- `BLACKHOLE_COMPARE_STEP_SIZE=<float>`
- `BLACKHOLE_COMPARE_OUTLIER_COUNT=<int>`
- `BLACKHOLE_COMPARE_OUTLIER_FRAC=<float>`

Integrator debug flags:
- `BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=1`: NaN/Inf (magenta overlay)
- `BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=2`: range guard (yellow overlay)
- `BLACKHOLE_INTEGRATOR_DEBUG_FLAGS=3`: both

## Recommended parity settings

Empirical results (baseline sweeps):
- Default steps (300/0.1): 3/12 preset failures.
- 600 steps + 0.05 step: 2/12 preset failures.
- 1000 steps + 0.02 step: 0/12 preset failures.

Latest full-feature sweep (post background LOD bias defaults):
- Default steps (300/0.1): 2/12 preset failures (idx 0/4).
- Strict steps (1000/0.02): 0/12 preset failures.

For strict parity, set:
```bash
BLACKHOLE_COMPARE_MAX_STEPS=1000 \
BLACKHOLE_COMPARE_STEP_SIZE=0.02
```

## FP Precision Testing (Compute Shader Optimization)

To test the impact of SPIR-V optimization on floating-point precision in compute shaders,
use the `SPIRV_SKIP_OPT_COMPUTE` environment variable during shader compilation.

### Shader Size Impact

| Shader | Unoptimized | Optimized | Reduction |
|--------|-------------|-----------|-----------|
| geodesic_trace.comp | 52k | 27k | 48% |
| drawid_cull.comp | 2.4k | 1.7k | 29% |

### Testing Procedure

1. Compile shaders without compute optimization:
   ```bash
   rm -rf build/shader_cache/*
   SPIRV_SKIP_OPT_COMPUTE=1 scripts/compile_shaders_spirv.sh
   ```

2. Run the application and capture a reference frame:
   ```bash
   BLACKHOLE_COMPARE_SWEEP=1 \
   BLACKHOLE_COMPARE_BASELINE=1 \
   BLACKHOLE_COMPARE_WRITE_OUTPUTS=1 \
   ./build/Release/Blackhole
   cp logs/compare/compare_0_compute.ppm /tmp/unopt_compute.ppm
   ```

3. Recompile with optimization (default):
   ```bash
   rm -rf build/shader_cache/*
   scripts/compile_shaders_spirv.sh
   ```

4. Run again and compare:
   ```bash
   BLACKHOLE_COMPARE_SWEEP=1 \
   BLACKHOLE_COMPARE_BASELINE=1 \
   BLACKHOLE_COMPARE_WRITE_OUTPUTS=1 \
   ./build/Release/Blackhole
   compare -metric RMSE /tmp/unopt_compute.ppm logs/compare/compare_0_compute.ppm /tmp/diff.png
   ```

The RMSE value indicates the precision difference caused by FP contraction optimizations.
Values under 0.001 typically indicate acceptable precision for visualization purposes.
