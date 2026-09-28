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

# The magnified patch is nearly uniform at raw luminance about 3, which the
# default exposure maps to display white; exposure 0.25 keeps both tiles below
# clipping so resolution stays the only controlled variable.
capture_tile() {
  name=$1
  width=$2
  height=$3
  (
    cd "$output_dir"
    BLACKHOLE_WINDOW_HIDDEN=1 BLACKHOLE_SCENE=observer-sky \
      BLACKHOLE_OBSERVER_LOOK=patch BLACKHOLE_OBSERVER_FOV=0.1 \
      "$binary" --export-frame "$output_dir/$name.png" \
      --export-raw-frame "$output_dir/$name.pfm" --export-frames 10 \
      --export-size "$width" "$height" --export-exposure 0.25 \
      > "$output_dir/$name.stdout.log" 2> "$output_dir/$name.stderr.log"
  )
}

capture_tile resolution_640x480 640 480
capture_tile resolution_1280x960 1280 960
"$PYTHON" "$repo_dir/scripts/capture_comparison_index.py" observer "$output_dir"
echo "Comparison written to $output_dir/index.md"
