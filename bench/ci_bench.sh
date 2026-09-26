#!/bin/sh
# Build physics_bench for one CMake preset, run the CPU benchmark (and the GPU
# benchmark when a display is present), and compare each result file against
# its own recorded baseline through scripts/check_bench_regression.py.
#
# usage: bench/ci_bench.sh
#
#   BENCH_PRESET=ci|riced   preset to build (default ci)
#   BENCH_BASELINE=PATH     CPU baseline (default bench/baseline-$BENCH_PRESET.json)
#   BENCH_GPU_BASELINE=PATH GPU baseline (default bench/baseline-$BENCH_PRESET-gpu.json)
#   BENCH_OUT_DIR=DIR       result JSON directory (default build/bench)
#   BENCH_ALLOW_MISSING=1   exit 0 with a notice when the CPU baseline is absent
#   BENCH_RUN_ONLY=1        stop after writing the JSON, skipping the comparison
#   PYTHON                  interpreter for the checker (default python3)
#
# `ci` is the locked GCC 14 Release graph the hosted lanes install into
# build/CI-deps; bench/baseline-ci.json is its committed CPU baseline, and the
# scheduled bench workflow runs it. `riced` is opt-in: a Debug build with Tracy
# instrumentation whose dependency graph needs tracy/0.13.1, which conan.lock
# does not pin, so its Conan install runs unlocked, the script only names that
# command, and no riced baseline is committed.
#
# The GPU run (DISPLAY set) repeats the CPU benchmarks with the same arguments
# and adds the GPU geodesic benchmark, so bench_gpu.json is compared only
# against a GPU baseline, never the CPU one. No GPU baseline is committed: until
# one is recorded on a GPU host, the GPU comparison prints a notice and does
# not affect the exit status.
#
# A failed build or benchmark run, or a missing or unparsable result file,
# exits nonzero before any comparison. After that the exit status is the CPU
# checker's (1 on a regression, a missing or invalid entry; 2 on a missing
# baseline), or the GPU checker's when the CPU comparison passes.
set -eu

root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
PYTHON=${PYTHON:-python3}
preset=${BENCH_PRESET:-ci}

case $preset in
  riced)
    bin_dir=build/Riced/Debug
    toolchain=build/Riced/Debug/generators/conan_toolchain.cmake
    install_cmd="CONAN_INSTALL_NO_LOCKFILE=1 ./scripts/conan_install.sh Debug build/Riced -o 'blackhole/*:enable_tracy=True' --lockfile="
    ;;
  ci)
    bin_dir=build/CI
    toolchain=build/CI-deps/Release/generators/conan_toolchain.cmake
    install_cmd="conan install . --output-folder=build/CI-deps --lockfile=conan.lock --build=missing -pr:a conan/profiles/ci"
    ;;
  *)
    echo "ci_bench: BENCH_PRESET must be riced or ci, not '$preset'" >&2
    exit 2
    ;;
esac
[ -r "$toolchain" ] || {
  echo "ci_bench: missing $toolchain; install the $preset dependencies first:" >&2
  echo "  $install_cmd" >&2
  exit 2
}

cmake --preset "$preset"
cmake --build --preset "$preset" --target physics_bench

out=${BENCH_OUT_DIR:-build/bench}
mkdir -p "$out"
# A result left by an earlier run must never stand in for this one: remove it
# first and stop if it survives. physics_bench exits 4 when it cannot write
# its JSON and 3 when a requested GPU run fails.
fresh_output() {
  rm -f "$1" || true
  if [ -e "$1" ]; then
    echo "ci_bench: cannot remove stale $1" >&2
    exit 1
  fi
}
fresh_output "$out/bench_cpu.json"
fresh_output "$out/bench_gpu.json"
set -- --rays 4000 --steps 2000 --iterations 10
"$bin_dir/physics_bench" "$@" --json "$out/bench_cpu.json" || {
  rc=$?
  echo "ci_bench: CPU benchmark failed (exit $rc)" >&2
  exit "$rc"
}
require_json() {
  test -s "$1" || { echo "ci_bench: physics_bench wrote no $1" >&2; exit 1; }
  "$PYTHON" -c 'import json, sys; json.load(open(sys.argv[1]))' "$1" ||
    { echo "ci_bench: $1 is not valid JSON" >&2; exit 1; }
}
require_json "$out/bench_cpu.json"
gpu=0
if [ -n "${DISPLAY:-}" ]; then
  # physics_bench exits 3 when the GL context or compute shader fails.
  "$bin_dir/physics_bench" "$@" --gpu --gpu-width 1024 --gpu-height 1024 \
    --gpu-iterations 20 --json "$out/bench_gpu.json" || {
    rc=$?
    echo "ci_bench: GPU benchmark failed (exit $rc) with DISPLAY=$DISPLAY" >&2
    exit "$rc"
  }
  require_json "$out/bench_gpu.json"
  gpu=1
else
  echo "NOTICE: no DISPLAY; skipping GPU benchmark run"
fi

[ "${BENCH_RUN_ONLY:-0}" = 1 ] && exit 0

baseline=${BENCH_BASELINE:-bench/baseline-$preset.json}
allow=
[ "${BENCH_ALLOW_MISSING:-0}" = 1 ] && allow=--allow-missing
cpu_rc=0
"$PYTHON" scripts/check_bench_regression.py --baseline "$baseline" ${allow:+"$allow"} \
  "$out/bench_cpu.json" || cpu_rc=$?
gpu_rc=0
if [ "$gpu" = 1 ]; then
  gpu_baseline=${BENCH_GPU_BASELINE:-bench/baseline-$preset-gpu.json}
  echo "GPU results against $gpu_baseline:"
  # --allow-missing: without a GPU baseline the GPU run is reported, not gated.
  "$PYTHON" scripts/check_bench_regression.py --baseline "$gpu_baseline" --allow-missing \
    "$out/bench_gpu.json" || gpu_rc=$?
fi
[ "$cpu_rc" != 0 ] && exit "$cpu_rc"
exit "$gpu_rc"
