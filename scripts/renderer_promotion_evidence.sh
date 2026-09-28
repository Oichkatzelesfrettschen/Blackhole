#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <build-dir> <output-dir>" >&2
  exit 2
fi

PYTHON=${PYTHON:-python3}
command -v "$PYTHON" >/dev/null 2>&1 || { echo "Python is required" >&2; exit 1; }
command -v glxinfo >/dev/null 2>&1 || { echo "glxinfo is required" >&2; exit 1; }

repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
build_dir=$(CDPATH= cd -- "$1" && pwd -P)
binary="$build_dir/Blackhole"
[ -x "$binary" ] || { echo "Missing executable: $binary" >&2; exit 1; }
mkdir -p -- "$2"
output_dir=$(CDPATH= cd -- "$2" && pwd -P)
for path in legacy.png legacy.png.json legacy_gpu_timing.csv default.png default.png.json default_gpu_timing.csv summary.md glxinfo.txt legacy.stdout.log legacy.stderr.log default.stdout.log default.stderr.log; do
  [ ! -e "$output_dir/$path" ] || { echo "Output exists: $output_dir/$path" >&2; exit 1; }
done

glxinfo -B > "$output_dir/glxinfo.txt"
commit=$(git -C "$repo_dir" rev-parse HEAD)
frame_count=180

(
  cd "$repo_dir"
  BLACKHOLE_WINDOW_HIDDEN=1 BLACKHOLE_GPU_TIMING_LOG=1 \
    BLACKHOLE_GPU_TIMING_LOG_STRIDE=1 \
    BLACKHOLE_GPU_TIMING_LOG_PATH="$output_dir/legacy_gpu_timing.csv" \
    "$binary" --renderer-backend fragment --renderer-geodesic legacy-beauty \
    --export-frame "$output_dir/legacy.png" --export-frames "$frame_count" \
    > "$output_dir/legacy.stdout.log" 2> "$output_dir/legacy.stderr.log"
  BLACKHOLE_WINDOW_HIDDEN=1 BLACKHOLE_GPU_TIMING_LOG=1 \
    BLACKHOLE_GPU_TIMING_LOG_STRIDE=1 \
    BLACKHOLE_GPU_TIMING_LOG_PATH="$output_dir/default_gpu_timing.csv" \
    "$binary" --renderer-backend fragment --renderer-geodesic kerr-reference \
    --export-frame "$output_dir/default.png" --export-frames "$frame_count" \
    > "$output_dir/default.stdout.log" 2> "$output_dir/default.stderr.log"
)

"$PYTHON" - "$output_dir" "$commit" "$frame_count" <<'PY'
import csv
import json
import math
import pathlib
import statistics
import sys

output = pathlib.Path(sys.argv[1])
commit = sys.argv[2]
frame_count = int(sys.argv[3])
gl_info = (output / "glxinfo.txt").read_text(encoding="utf-8")


def gl_field(label):
    for line in gl_info.splitlines():
        if line.startswith(label):
            return line.partition(":")[2].strip()
    raise ValueError(f"glxinfo lacks {label}")


gpu = gl_field("OpenGL renderer string:")
driver = gl_field("OpenGL version string:")
stages = (
    "gpu_fragment_ms", "gpu_compute_ms", "gpu_bloom_ms", "gpu_tonemap_ms",
    "gpu_depth_ms", "gpu_grmhd_slice_ms", "gpu_tesseract_ms",
)
metrics = {}
resolution = None
camera = None
for name, geodesic in (("legacy", "legacy-beauty"), ("default", "kerr-reference")):
    metadata = json.loads((output / f"{name}.png.json").read_text(encoding="utf-8"))
    if (metadata["backend"] != "fragment" or metadata["geodesic_model"] != geodesic
            or metadata["radiative_model"] != "thin-surface"
            or metadata["quality_tier"] != "balanced"):
        raise ValueError(f"{name} capture has the wrong renderer contract")
    camera_fields = ("camera_distance", "camera_yaw_degrees", "camera_pitch_degrees", "camera_fov_degrees",
                     "camera_aim_target_world", "kerr_spin", "scene")
    camera_values = tuple(json.dumps(metadata[field], sort_keys=True) for field in camera_fields)
    if camera is not None and camera_values != camera:
        raise ValueError("capture camera, spin, or scene differs")
    camera = camera_values
    dimensions = (metadata["width"], metadata["height"])
    if resolution is not None and dimensions != resolution:
        raise ValueError("capture resolutions differ")
    resolution = dimensions
    with (output / f"{name}_gpu_timing.csv").open(newline="", encoding="utf-8") as source:
        rows = list(csv.DictReader(source))
    if len(rows) < frame_count:
        raise ValueError(f"{name} has only {len(rows)} GPU timing rows")
    rows = rows[-(frame_count - 10):]
    if any((int(row["width"]), int(row["height"])) != resolution for row in rows):
        raise ValueError(f"{name} GPU timing resolution differs from capture")
    if any(row["compute_active"] != "0" for row in rows):
        raise ValueError(f"{name} unexpectedly used compute dispatch")
    metrics[name] = {stage: [] for stage in (*stages, "total_gpu_ms")}
    for row in rows:
        values = {}
        for stage in stages:
            if row[stage]:
                value = float(row[stage])
                if not math.isfinite(value) or value < 0:
                    raise ValueError(f"invalid {stage} sample for {name}")
                values[stage] = value
                metrics[name][stage].append(value)
        if "gpu_fragment_ms" not in values or "gpu_tonemap_ms" not in values:
            raise ValueError(f"{name} lacks required fragment or tone map timing")
        metrics[name]["total_gpu_ms"].append(sum(values.values()))


def describe(values):
    if not values:
        return "n/a"
    ordered = sorted(values)
    median = statistics.median(ordered)
    p95 = ordered[math.ceil(0.95 * len(ordered)) - 1]
    return f"{median:.3f} / {p95:.3f}"


lines = [
    "# Default renderer promotion timing",
    "",
    f"GPU: {gpu}  ",
    f"Driver (OpenGL version string): {driver}  ",
    f"Resolution: {resolution[0]} x {resolution[1]}  ",
    f"Commit: `{commit}`  ",
    f"Frames: {frame_count} settled per path; final {frame_count - 10} samples analyzed",
    "",
    "| Pass (ms) | Legacy median / p95 | Default median / p95 |",
    "| --- | ---: | ---: |",
]
for stage in (*stages, "total_gpu_ms"):
    lines.append(f"| {stage} | {describe(metrics['legacy'][stage])} | "
                 f"{describe(metrics['default'][stage])} |")
lines.extend(("", "Total sums available GPU pass durations in each sampled row. "
              "p95 uses nearest rank. Empty pass columns are n/a.", ""))
(output / "summary.md").write_text("\n".join(lines), encoding="utf-8")
PY

echo "Evidence written to $output_dir"
