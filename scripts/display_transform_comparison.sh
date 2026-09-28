#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 BUILD OUT" >&2
  exit 2
fi
: "${PYTHON:?Set PYTHON to the configured Python interpreter}"
build_dir=$(CDPATH= cd -- "$1" && pwd -P)
binary="$build_dir/Blackhole"
[ -x "$binary" ] || { echo "Missing executable: $binary" >&2; exit 1; }
[ ! -e "$2" ] || { echo "Output already exists: $2" >&2; exit 1; }
mkdir -p -- "$2"
output_dir=$(CDPATH= cd -- "$2" && pwd -P)
repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)

capture_tile() {
  name=$1
  exposure=$2
  bloom=$3
  tone=$4
  (
    cd "$output_dir"
    BLACKHOLE_WINDOW_HIDDEN=1 \
      "$binary" --export-frame "$output_dir/$name.png" \
      --export-raw-frame "$output_dir/$name.pfm" --export-frames 10 \
      --export-size 960 720 --export-exposure "$exposure" \
      --export-bloom "$bloom" --export-tone-mapping "$tone" \
      > "$output_dir/$name.stdout.log" 2> "$output_dir/$name.stderr.log"
  )
}

capture_tile bloom_off 1 0 on
capture_tile bloom_on 1 0.1 on
capture_tile exposure_0p5 0.5 0 on
capture_tile exposure_1 1 0 on
capture_tile exposure_2 2 0 on
capture_tile tone_mapping_off 1 0 off
capture_tile tone_mapping_on 1 0 on
"$PYTHON" "$repo_dir/scripts/capture_comparison_index.py" display "$output_dir"
echo "Comparison written to $output_dir/index.md"
