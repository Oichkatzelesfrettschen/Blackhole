# Performance Tooling

This project supports GPU timing CSV logs and CPU flamegraphs via `perf`.
It also ships SPIR-V tooling for shader optimization and reflection.

## GPU timing CSV

Enable CSV logging via environment variables:
```bash
BLACKHOLE_GPU_TIMING_LOG=1 \
BLACKHOLE_GPU_TIMING_LOG_STRIDE=1 \
./build/Riced/Debug/Blackhole
```

Output:
- `logs/perf/gpu_timing.csv`

Notes:
- `BLACKHOLE_GPU_TIMING_LOG_STRIDE` controls sample cadence in frames.
- Logging auto-enables GPU timers when set.

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
