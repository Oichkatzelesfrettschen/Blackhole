#!/bin/sh
# Build physics_bench for one CMake preset, run the CPU benchmark (and the GPU
# benchmark when a display is present), and compare the JSON against the
# preset's recorded baseline through scripts/check_bench_regression.py.
#
# usage: bench/ci_bench.sh
#
#   BENCH_PRESET=riced|ci   preset to build (default riced)
#   BENCH_BASELINE=PATH     baseline JSON (default bench/baseline-$BENCH_PRESET.json)
#   BENCH_OUT_DIR=DIR       result JSON directory (default build/bench)
#   BENCH_ALLOW_MISSING=1   exit 0 with a notice when the baseline is absent
#   PYTHON                  interpreter for the checker (default python3)
#
# `riced` is a Debug build with Tracy instrumentation; its dependency graph
# needs tracy/0.13.1, which conan.lock does not pin, so its Conan install runs
# unlocked and the script only names that command. `ci` is the locked GCC 14
# Release graph the hosted lanes install into build/CI-deps, and is the preset
# the scheduled bench workflow runs. The exit status is the checker's: 1 on a
# regression beyond its threshold, 2 on a missing baseline.
set -eu

root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
PYTHON=${PYTHON:-python3}
preset=${BENCH_PRESET:-riced}

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
"$bin_dir/physics_bench" --rays 4000 --steps 2000 --iterations 10 \
  --json "$out/bench_cpu.json"
set -- "$out/bench_cpu.json"
if [ -n "${DISPLAY:-}" ]; then
  "$bin_dir/physics_bench" --gpu --gpu-width 1024 --gpu-height 1024 \
    --gpu-iterations 20 --json "$out/bench_gpu.json"
  set -- "$@" "$out/bench_gpu.json"
else
  echo "NOTICE: no DISPLAY; skipping GPU benchmark run"
fi

baseline=${BENCH_BASELINE:-bench/baseline-$preset.json}
if [ "${BENCH_ALLOW_MISSING:-0}" = 1 ]; then
  set -- --allow-missing "$@"
fi
exec "$PYTHON" scripts/check_bench_regression.py --baseline "$baseline" "$@"
