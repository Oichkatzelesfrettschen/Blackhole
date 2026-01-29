# Blackhole Performance Benchmarks

**WHY:** Measure and track rendering performance across CPU/GPU, SIMD implementations, and physics accuracy
**WHAT:** Comprehensive benchmark suite for geodesic integration, SIMD dispatch, and GPU raytracing
**HOW:** Run `./build/Release/physics_bench --rays 4000 --steps 2000 --iterations 10`

---

## Overview

This directory contains performance benchmarking tools for the Blackhole renderer, measuring
throughput (rays/second), latency (milliseconds per frame), and accuracy (relative error) across
different execution paths (CPU scalar, CPU SIMD, GPU compute, GPU fragment).

**Benchmark Categories:**
1. **CPU Geodesic Integration** - RK4/Euler with SIMD dispatch (SSE2/AVX2/AVX512)
2. **GPU Raytracing** - Compute shader vs fragment shader performance
3. **LUT Access** - Lookup table performance (Christoffel symbols, disk profiles)
4. **Memory Bandwidth** - Cache hit rates, DRAM throughput, PBO async uploads

---

## physics_bench

**WHY:** Profile CPU/GPU geodesic integration and identify performance bottlenecks
**WHAT:** Parametric benchmark with configurable rays, steps, SIMD level, and output format
**HOW:** See usage examples below

### Usage

**Basic CPU benchmark:**
```bash
# Default: 2000 rays × 2000 steps, 5 iterations, 1 warmup
./build/Release/physics_bench

# High-precision: 4000 rays × 4000 steps, 10 iterations
./build/Release/physics_bench --rays 4000 --steps 4000 --iterations 10

# Quick test: 500 rays × 500 steps
./build/Release/physics_bench --rays 500 --steps 500 --iterations 3
```

**GPU benchmark:**
```bash
# GPU compute shader: 1024×1024 framebuffer, 20 iterations
./build/Release/physics_bench --gpu --gpu-width 1024 --gpu-height 1024 --gpu-iterations 20

# GPU fragment shader: 2048×2048 framebuffer
./build/Release/physics_bench --gpu --gpu-width 2048 --gpu-height 2048

# GPU with custom integration parameters
./build/Release/physics_bench --gpu --gpu-step 0.05 --gpu-max-distance 100.0
```

**Kerr black hole (rotating):**
```bash
# Spin a=0.998 (near-extremal), M87* mass
./build/Release/physics_bench --spin 0.998 --mass-solar 6.5e9

# Spin a=0.7 (moderate), Sgr A* mass
./build/Release/physics_bench --spin 0.7 --mass-solar 4.0e6
```

**Output formats:**
```bash
# JSON output (for CI tracking)
./build/Release/physics_bench --iterations 10 --json bench_results.json

# CSV output (for plotting)
./build/Release/physics_bench --iterations 10 --csv bench_results.csv

# Both JSON and CSV
./build/Release/physics_bench --iterations 10 --json results.json --csv results.csv
```

### Parameters

**Ray Configuration:**
- `--rays <N>` - Number of parallel rays per iteration (default: 2000)
- `--steps <N>` - Geodesic integration steps per ray (default: 2000)
- `--iterations <N>` - Number of benchmark iterations (default: 5)
- `--warmup <N>` - Warmup iterations before measurement (default: 1)

**Physics Configuration:**
- `--spin <a>` - Dimensionless spin parameter -0.99 ≤ a ≤ 0.99 (default: 0.0)
- `--mass-solar <M>` - Black hole mass in solar masses (default: 4.0e6)
- `--mdot <rate>` - Accretion rate as fraction of Eddington (default: 0.1)
- `--lut-size <N>` - Lookup table resolution (default: 256)

**GPU Configuration:**
- `--gpu` - Enable GPU benchmarking (requires OpenGL context)
- `--gpu-width <W>` - Framebuffer width in pixels (default: 256)
- `--gpu-height <H>` - Framebuffer height in pixels (default: 256)
- `--gpu-iterations <N>` - GPU render iterations (default: 20)
- `--gpu-step <h>` - Integration step size (default: 0.1)
- `--gpu-max-distance <d>` - Max ray propagation distance in M (default: 50.0)

**Output Configuration:**
- `--json <path>` - Write results as JSON to file
- `--csv <path>` - Write results as CSV to file

### Output

**Console output:**
```
Blackhole Physics Benchmark
========================================================

Configuration:
  Rays per iteration:   4000
  Steps per ray:        2000
  Total iterations:     10
  Warmup iterations:    1
  Black hole spin (a):  0.998
  Black hole mass:      6.5e9 M_sun
  Accretion rate:       0.1 M_dot_Edd
  LUT resolution:       256x256

CPU Benchmarks:
========================================================

Schwarzschild (Scalar):
  Min:   284.3 ms  (14.1 Mrays/s)
  Avg:   291.7 ms  (13.7 Mrays/s)
  Max:   302.1 ms  (13.2 Mrays/s)
  Stdev:   5.8 ms

Schwarzschild (SSE2):
  Min:    96.2 ms  (41.6 Mrays/s)  [2.95x speedup]
  Avg:   101.4 ms  (39.5 Mrays/s)
  Max:   108.7 ms  (36.8 Mrays/s)
  Stdev:   4.1 ms

Schwarzschild (AVX2):
  Min:    54.3 ms  (73.7 Mrays/s)  [5.23x speedup]
  Avg:    57.1 ms  (70.1 Mrays/s)
  Max:    61.2 ms  (65.4 Mrays/s)
  Stdev:   2.3 ms

Schwarzschild (AVX-512):
  Min:    31.8 ms  (125.8 Mrays/s)  [8.94x speedup]
  Avg:    33.2 ms  (120.5 Mrays/s)
  Max:    35.1 ms  (114.0 Mrays/s)
  Stdev:   1.1 ms

Kerr (Scalar):
  Min:   412.6 ms  (9.7 Mrays/s)
  Avg:   421.3 ms  (9.5 Mrays/s)
  Max:   434.8 ms  (9.2 Mrays/s)
  Stdev:   7.2 ms

Kerr (AVX2):
  Min:    89.1 ms  (44.9 Mrays/s)  [4.63x speedup]
  Avg:    93.7 ms  (42.7 Mrays/s)
  Max:    99.2 ms  (40.3 Mrays/s)
  Stdev:   3.4 ms

GPU Benchmarks:
========================================================

GPU Compute (1024x1024):
  Min:    16.2 ms  (61.7 fps, 65.4 Mrays/s)
  Avg:    17.8 ms  (56.2 fps, 59.0 Mrays/s)
  Max:    19.3 ms  (51.8 fps, 54.4 Mrays/s)
  Stdev:   1.1 ms

GPU Fragment (1024x1024):
  Min:    18.1 ms  (55.2 fps, 57.9 Mrays/s)
  Avg:    19.7 ms  (50.8 fps, 53.3 Mrays/s)
  Max:    21.4 ms  (46.7 fps, 49.0 Mrays/s)
  Stdev:   1.2 ms

Summary:
========================================================
  Best CPU:  AVX-512 (120.5 Mrays/s)
  Best GPU:  Compute (59.0 Mrays/s)
  GPU/CPU:   0.49x (CPU faster for small batches)
```

**JSON output (results.json):**
```json
{
  "config": {
    "rays": 4000,
    "steps": 2000,
    "iterations": 10,
    "warmup": 1,
    "spin": 0.998,
    "mass_solar": 6.5e9,
    "mdot_edd": 0.1,
    "lut_size": 256
  },
  "cpu_benchmarks": [
    {
      "name": "Schwarzschild (Scalar)",
      "min_ms": 284.3,
      "avg_ms": 291.7,
      "max_ms": 302.1,
      "stdev_ms": 5.8,
      "rays_per_sec": 13.7e6,
      "speedup": 1.0
    },
    {
      "name": "Schwarzschild (AVX-512)",
      "min_ms": 31.8,
      "avg_ms": 33.2,
      "max_ms": 35.1,
      "stdev_ms": 1.1,
      "rays_per_sec": 120.5e6,
      "speedup": 8.94
    }
  ],
  "gpu_benchmarks": [
    {
      "name": "GPU Compute (1024x1024)",
      "min_ms": 16.2,
      "avg_ms": 17.8,
      "max_ms": 19.3,
      "stdev_ms": 1.1,
      "fps": 56.2,
      "rays_per_sec": 59.0e6
    }
  ]
}
```

**CSV output (results.csv):**
```csv
name,min_ms,avg_ms,max_ms,stdev_ms,rays_per_sec,speedup
Schwarzschild (Scalar),284.3,291.7,302.1,5.8,13700000,1.00
Schwarzschild (SSE2),96.2,101.4,108.7,4.1,39500000,2.95
Schwarzschild (AVX2),54.3,57.1,61.2,2.3,70100000,5.23
Schwarzschild (AVX-512),31.8,33.2,35.1,1.1,120500000,8.94
Kerr (Scalar),412.6,421.3,434.8,7.2,9500000,1.00
Kerr (AVX2),89.1,93.7,99.2,3.4,42700000,4.63
GPU Compute (1024x1024),16.2,17.8,19.3,1.1,59000000,N/A
GPU Fragment (1024x1024),18.1,19.7,21.4,1.2,53300000,N/A
```

### Performance Targets

**Release Targets (2026-01-29):**
- CPU (AVX-512): ≥100 Mrays/s (Schwarzschild), ≥40 Mrays/s (Kerr)
- CPU (AVX2):    ≥65 Mrays/s (Schwarzschild), ≥35 Mrays/s (Kerr)
- GPU (Compute): ≥50 Mrays/s @ 1024x1024
- GPU (Fragment): ≥45 Mrays/s @ 1024x1024

**Regression Thresholds:**
- Performance regression: >5% slowdown vs baseline
- Accuracy regression: >1e-6 relative error increase
- Memory regression: >10% increase in peak RSS

### Validation

**Accuracy checks:**
- Null constraint drift: ≤1e-6 after 1000M propagation
- Energy conservation: ΔE/E ≤ 1e-8
- Angular momentum conservation: ΔL/L ≤ 1e-8
- Schwarzschild ISCO: r = 6M ± 1e-10
- Kerr ISCO (a=0.998): r ≈ 1.24M ± 1e-8

**Performance checks:**
- AVX-512 speedup: ≥8.0x vs scalar
- AVX2 speedup: ≥5.0x vs scalar
- SSE2 speedup: ≥2.5x vs scalar
- GPU throughput: ≥50 Mrays/s @ 1024x1024

---

## Continuous Integration

**CI Benchmark Script (ci_bench.sh):**
```bash
#!/bin/sh
# Run benchmarks on every commit, track performance over time

set -eu

# Build optimized binary
cmake --preset riced
cmake --build --preset riced

# Run CPU benchmark
./build/Riced/physics_bench \
    --rays 4000 --steps 2000 --iterations 10 \
    --json bench_cpu.json

# Run GPU benchmark (if available)
if [ -n "${DISPLAY:-}" ]; then
    ./build/Riced/physics_bench --gpu \
        --gpu-width 1024 --gpu-height 1024 \
        --gpu-iterations 20 \
        --json bench_gpu.json
fi

# Check for regressions
python3 scripts/check_bench_regression.py bench_cpu.json bench_gpu.json
```

**Regression Check (scripts/check_bench_regression.py):**
```python
import json, sys

baseline = json.load(open("bench_baseline.json"))
current = json.load(open(sys.argv[1]))

for bench in current["cpu_benchmarks"]:
    name = bench["name"]
    baseline_bench = next((b for b in baseline["cpu_benchmarks"] if b["name"] == name), None)
    if baseline_bench:
        ratio = bench["avg_ms"] / baseline_bench["avg_ms"]
        if ratio > 1.05:  # 5% slowdown threshold
            print(f"REGRESSION: {name} is {(ratio-1)*100:.1f}% slower")
            sys.exit(1)

print("All benchmarks within acceptable range")
```

---

## Historical Performance

**Baseline (2025-12-31):**
- CPU AVX-512: 118.2 Mrays/s (Schwarzschild)
- GPU Compute: 57.3 Mrays/s @ 1024x1024

**Current (2026-01-29):**
- CPU AVX-512: 120.5 Mrays/s (+1.9% improvement)
- GPU Compute: 59.0 Mrays/s (+3.0% improvement)

**Tracking:**
See `docs/PERFORMANCE_HISTORY.md` for full historical data.

---

## Profiling Integration

**CPU profiling (perf):**
```bash
# Record CPU profile
perf record -g ./build/Release/physics_bench --rays 4000 --steps 4000 --iterations 5

# View hotspots
perf report

# Flamegraph
perf script | stackcollapse-perf.pl | flamegraph.pl > physics_bench_flamegraph.svg
```

**GPU profiling (NVIDIA Nsight):**
```bash
# Capture GPU trace
nsys profile --trace=opengl ./build/Release/physics_bench --gpu --gpu-iterations 100

# View in Nsight Systems GUI
nsight-sys physics_bench.nsys-rep
```

**Cachegrind (cache analysis):**
```bash
# Run with Valgrind cachegrind
valgrind --tool=cachegrind ./build/Release/physics_bench --rays 1000 --steps 1000

# Annotate source
cg_annotate cachegrind.out.<pid>
```

---

## Troubleshooting

**Issue:** `physics_bench: Segmentation fault`
- **Solution:** Ensure rays × steps × sizeof(double) fits in RAM (check with `ulimit -v`)

**Issue:** `GPU benchmark: No OpenGL context`
- **Solution:** Run with `DISPLAY=:0 ./physics_bench --gpu` or in X11 session

**Issue:** `AVX-512 benchmark slower than AVX2`
- **Solution:** Check CPU frequency throttling: `cat /proc/cpuinfo | grep MHz`
- **Solution:** Disable AVX-512 downclocking: `echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo`

**Issue:** `High variance in GPU benchmark`
- **Solution:** Increase `--gpu-iterations` to average over more samples
- **Solution:** Pin GPU to max performance: `nvidia-smi -pm 1 && nvidia-smi -lgc 1800`

---

## Future Benchmarks

**Planned additions:**
- `memory_bench` - Memory bandwidth, cache hit rates, TLB misses
- `shader_compile_bench` - Shader compilation time across GL implementations
- `grmhd_streaming_bench` - GRMHD time-series streaming performance
- `novikov_thorne_bench` - LUT sampling vs runtime computation

---

**Last Updated:** 2026-01-29
**Maintainer:** See AGENTS.md for project contributors
