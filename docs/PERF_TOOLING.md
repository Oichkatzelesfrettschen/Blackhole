# Performance Tooling

This project supports GPU timing CSV logs and CPU flamegraphs via `perf`.
It also ships SPIR-V tooling for shader optimization and reflection.

## GPU timing CSV

Enable CSV logging via environment variables:
```bash
BLACKHOLE_GPU_TIMING_LOG=1 \
BLACKHOLE_GPU_TIMING_LOG_STRIDE=1 \
./build/Release/Blackhole
```

Output:
- `logs/perf/gpu_timing.csv`

Notes:
- `BLACKHOLE_GPU_TIMING_LOG_STRIDE` controls sample cadence in frames.
- Logging auto-enables GPU timers when set.

## GPU timing analysis

Analyze timing logs with statistical outlier detection:
```bash
# Text report (default)
python scripts/analyze_gpu_timing.py logs/perf/gpu_timing.csv

# JSON output for CI/automation
python scripts/analyze_gpu_timing.py --json

# Custom IQR threshold (default: 1.5)
python scripts/analyze_gpu_timing.py --threshold 2.0

# Write to file
python scripts/analyze_gpu_timing.py -o logs/perf/timing_report.txt
```

Features:
- Computes mean, median, std, min, max, P25/P75/P95/P99 for each metric
- Detects outliers using IQR method (Q1 - 1.5*IQR to Q3 + 1.5*IQR)
- Reports outlier indices for investigation
- Returns exit code 1 when outliers detected (CI-friendly)
- JSON output for machine processing

## Performance pack (CMake targets)

Collect GPU timing + flamegraph + analysis in one command:
```bash
# Full performance pack (5s run, generates timing + flamegraph + reports)
cmake --build build/Release --target perf-pack

# Analyze existing GPU timing data only
cmake --build build/Release --target analyze-gpu-timing
```

Manual collection with custom duration:
```bash
./scripts/collect_perf_pack.sh 10  # 10-second collection
```

Output directory: `logs/perf/perf_pack_<timestamp>/`
- `gpu_timing.csv` - Raw timing samples
- `timing_report.txt` - Human-readable analysis
- `timing_report.json` - Machine-readable analysis
- `flamegraph.svg` - CPU flamegraph (if perf available)

## Perf sysctl settings

High sample rates require permissive perf settings:
```bash
sysctl kernel.perf_event_paranoid kernel.perf_event_max_sample_rate
```
Expected values:
- `kernel.perf_event_paranoid = -1`
- `kernel.perf_event_max_sample_rate = 100000`

## Flamegraphs

Scripted flamegraph capture (timestamped output):
```bash
PERF_FREQ=2000 ./scripts/run_flamegraph.sh build/Riced/Debug/physics_bench
```

Outputs:
- `logs/perf/flamegraph/flamegraph_<timestamp>.svg`
- `logs/perf/flamegraph/flamegraph_latest.svg` (symlink)

If `flamegraph` is not installed, set `FLAMEGRAPH_DIR` to the FlameGraph repo.

## SPIR-V bake + optimization

Compile GLSL to SPIR-V and run performance passes before runtime load:
```bash
./build/Release/spirv_bake shader/blackhole_main.frag \
  shader/blackhole_main.frag.spv \
  --stage frag --opt --strip --reflect
```

Notes:
- `--opt` runs `spv::Optimizer` performance passes.
- `--reflect` dumps bindings for quick verification.

## Overdraw reduction (meshoptimizer)

For heavy fragment shaders, reduce overdraw by reordering triangles:
- Use `meshopt_optimizeOverdraw` on opaque/alpha-tested geometry.
- Prefer depth pre-pass for dense disk geometry if overdraw remains high.
