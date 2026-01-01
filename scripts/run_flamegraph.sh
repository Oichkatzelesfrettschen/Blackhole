#!/bin/bash
# Generate a perf flamegraph for Blackhole.
#
# Usage: ./scripts/run_flamegraph.sh [command...]
# Example: ./scripts/run_flamegraph.sh ./build/Profile/RelWithDebInfo/physics_bench

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
OUT_DIR="${PROJECT_ROOT}/logs/perf/flamegraph"
PERF_FREQ="${PERF_FREQ:-999}"
TIMESTAMP="$(date +%Y%m%d_%H%M%S)"
OUT_SVG="${OUT_DIR}/flamegraph_${TIMESTAMP}.svg"
LATEST_SVG="${OUT_DIR}/flamegraph_latest.svg"

if ! command -v perf >/dev/null 2>&1; then
  echo "Error: perf not found in PATH"
  exit 1
fi

STACKCOLLAPSE=""
FLAMEGRAPH=""
FLAMEGRAPH_BIN="$(command -v flamegraph || true)"

if [ -n "$FLAMEGRAPH_BIN" ]; then
  mkdir -p "$OUT_DIR"
  COMMAND=("$@")
  if [ ${#COMMAND[@]} -eq 0 ]; then
    COMMAND=("${PROJECT_ROOT}/build/Profile/RelWithDebInfo/physics_bench")
  fi

  echo "Recording perf data and generating flamegraph..."
  "$FLAMEGRAPH_BIN" -F "$PERF_FREQ" -o "$OUT_SVG" -- "${COMMAND[@]}"
  ln -sfn "$OUT_SVG" "$LATEST_SVG"
  echo "Flamegraph: $OUT_SVG"
  exit 0
fi

if [ -n "${FLAMEGRAPH_DIR:-}" ]; then
  STACKCOLLAPSE="${FLAMEGRAPH_DIR}/stackcollapse-perf.pl"
  FLAMEGRAPH="${FLAMEGRAPH_DIR}/flamegraph.pl"
else
  STACKCOLLAPSE="$(command -v stackcollapse-perf.pl || true)"
  FLAMEGRAPH="$(command -v flamegraph.pl || true)"
fi

if [ ! -x "$STACKCOLLAPSE" ] || [ ! -x "$FLAMEGRAPH" ]; then
  echo "Error: FlameGraph scripts not found."
  echo "Set FLAMEGRAPH_DIR to the FlameGraph repo or put stackcollapse-perf.pl + flamegraph.pl in PATH."
  exit 1
fi

mkdir -p "$OUT_DIR"
PERF_DATA="${OUT_DIR}/perf_${TIMESTAMP}.data"

COMMAND=("$@")
if [ ${#COMMAND[@]} -eq 0 ]; then
  COMMAND=("${PROJECT_ROOT}/build/Profile/RelWithDebInfo/physics_bench")
fi

echo "Recording perf data..."
perf record -F "$PERF_FREQ" -g --output "$PERF_DATA" -- "${COMMAND[@]}"

echo "Generating flamegraph..."
perf script -i "$PERF_DATA" | "$STACKCOLLAPSE" | "$FLAMEGRAPH" > "$OUT_SVG"
ln -sfn "$OUT_SVG" "$LATEST_SVG"

echo "Flamegraph: $OUT_SVG"
