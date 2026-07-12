#!/bin/sh
# Build the riced preset, run physics_bench, and gate on the recorded
# baseline via scripts/check_bench_regression.py. GPU benchmarks run
# only when a display is present; the CPU gate always runs.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

cmake --preset riced
cmake --build --preset riced

bench_bin="./build/Riced/physics_bench"
[ -x "$bench_bin" ] || bench_bin="./build/riced/physics_bench"

"$bench_bin" \
    --rays 4000 --steps 2000 --iterations 10 \
    --json bench_cpu.json

if [ -n "${DISPLAY:-}" ]; then
    "$bench_bin" --gpu \
        --gpu-width 1024 --gpu-height 1024 \
        --gpu-iterations 20 \
        --json bench_gpu.json
    set -- bench_cpu.json bench_gpu.json
else
    echo "NOTICE: no DISPLAY; skipping GPU benchmark run"
    set -- bench_cpu.json
fi

# --allow-missing keeps the first-ever run green while printing the
# record instruction; once a baseline is committed the gate is real.
python3 scripts/check_bench_regression.py --allow-missing "$@"
