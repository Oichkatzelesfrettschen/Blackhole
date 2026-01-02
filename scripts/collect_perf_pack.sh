#!/bin/bash
# Collect performance metrics pack: GPU timing + flamegraph + analysis report.
#
# Usage: ./scripts/collect_perf_pack.sh [duration_sec]
# Example: ./scripts/collect_perf_pack.sh 10
#
# Output: logs/perf/perf_pack_<timestamp>/
#   - gpu_timing.csv
#   - timing_report.txt
#   - timing_report.json
#   - flamegraph.svg (if perf available)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
DURATION="${1:-5}"
TIMESTAMP="$(date +%Y%m%d_%H%M%S)"
OUT_DIR="${PROJECT_ROOT}/logs/perf/perf_pack_${TIMESTAMP}"
BINARY="${PROJECT_ROOT}/build/Release/Blackhole"

if [ ! -x "$BINARY" ]; then
  echo "Error: Blackhole binary not found at $BINARY"
  echo "Build with: cmake --build build/Release --target Blackhole"
  exit 1
fi

mkdir -p "$OUT_DIR"
echo "=== Performance Pack Collection ==="
echo "Duration: ${DURATION}s"
echo "Output:   $OUT_DIR"
echo ""

# Clean previous timing data
rm -f "${PROJECT_ROOT}/logs/perf/gpu_timing.csv"

# Run with GPU timing enabled
echo "Collecting GPU timing data..."
BLACKHOLE_GPU_TIMING_LOG=1 \
BLACKHOLE_GPU_TIMING_LOG_STRIDE=1 \
timeout "${DURATION}" "$BINARY" 2>/dev/null || true

# Copy timing data
if [ -f "${PROJECT_ROOT}/logs/perf/gpu_timing.csv" ]; then
  cp "${PROJECT_ROOT}/logs/perf/gpu_timing.csv" "$OUT_DIR/"
  TIMING_SAMPLES=$(wc -l < "$OUT_DIR/gpu_timing.csv")
  echo "GPU timing: $TIMING_SAMPLES samples"
else
  echo "Warning: No GPU timing data generated"
fi

# Generate analysis reports
if [ -f "$OUT_DIR/gpu_timing.csv" ]; then
  echo "Generating analysis reports..."
  python3 "${SCRIPT_DIR}/analyze_gpu_timing.py" "$OUT_DIR/gpu_timing.csv" \
    -o "$OUT_DIR/timing_report.txt" 2>/dev/null || true
  python3 "${SCRIPT_DIR}/analyze_gpu_timing.py" "$OUT_DIR/gpu_timing.csv" \
    --json -o "$OUT_DIR/timing_report.json" 2>/dev/null || true
  echo "Reports generated"
fi

# Generate flamegraph (optional, requires perf)
if command -v perf >/dev/null 2>&1; then
  echo "Generating CPU flamegraph..."
  PERF_FREQ="${PERF_FREQ:-999}"
  PERF_DATA="$OUT_DIR/perf.data"

  # Check if we can record (requires perf_event_paranoid <= 1 or CAP_SYS_ADMIN)
  PARANOID=$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo "3")
  if [ "$PARANOID" -le 1 ] || [ "$(id -u)" -eq 0 ]; then
    timeout "${DURATION}" perf record -F "$PERF_FREQ" -g --output "$PERF_DATA" -- "$BINARY" 2>/dev/null || true

    if [ -f "$PERF_DATA" ]; then
      FLAMEGRAPH_BIN="$(command -v flamegraph || true)"
      if [ -n "$FLAMEGRAPH_BIN" ]; then
        perf script -i "$PERF_DATA" | "$FLAMEGRAPH_BIN" --flamechart > "$OUT_DIR/flamegraph.svg" 2>/dev/null || true
      elif command -v stackcollapse-perf.pl >/dev/null 2>&1 && command -v flamegraph.pl >/dev/null 2>&1; then
        perf script -i "$PERF_DATA" | stackcollapse-perf.pl | flamegraph.pl > "$OUT_DIR/flamegraph.svg" 2>/dev/null || true
      else
        perf script -i "$PERF_DATA" > "$OUT_DIR/perf_script.txt"
        echo "Flamegraph tools not found; raw perf script saved"
      fi
      rm -f "$PERF_DATA"
    fi
  else
    echo "Flamegraph skipped: perf_event_paranoid=$PARANOID (need <=1 or root)"
  fi
else
  echo "Flamegraph skipped: perf not available"
fi

# Summary
echo ""
echo "=== Performance Pack Complete ==="
echo "Output directory: $OUT_DIR"
ls -la "$OUT_DIR"

# Return 0 if we got some data
if [ -f "$OUT_DIR/gpu_timing.csv" ]; then
  exit 0
else
  echo "Warning: No performance data collected"
  exit 1
fi
