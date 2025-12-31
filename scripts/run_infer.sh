#!/bin/bash
# Infer workflow for Blackhole
#
# Usage: ./scripts/run_infer.sh [preset] [target]
#   preset defaults to riced
#   target defaults to all (cmake --build preset)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

PRESET="${1:-riced}"
TARGET="${2:-}"
OUT_DIR="${PROJECT_ROOT}/infer-out/${PRESET}"

if ! command -v infer >/dev/null 2>&1; then
  echo "Error: infer not found in PATH"
  exit 1
fi

mkdir -p "$OUT_DIR"

BUILD_CMD=(cmake --build --preset "$PRESET")
if [ -n "$TARGET" ]; then
  BUILD_CMD+=(--target "$TARGET")
fi

echo "Running Infer for preset: $PRESET"
echo "Output: $OUT_DIR"

infer run --results-dir "$OUT_DIR" ${INFER_ARGS:-} -- "${BUILD_CMD[@]}"

echo "Infer report: $OUT_DIR/report.html"
