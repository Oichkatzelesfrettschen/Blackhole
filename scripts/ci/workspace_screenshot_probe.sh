#!/bin/sh
set -eu

: "${PYTHON:?Set PYTHON to the configured interpreter}"
build_dir=${1:-build/CI}
artifact_dir=${BLACKHOLE_WORKSPACE_ARTIFACTS:-$build_dir/workspace-screenshot-artifacts}
mkdir -p "$artifact_dir"
artifact_dir=$(cd "$artifact_dir" && pwd)
export LIBGL_ALWAYS_SOFTWARE=1
export MESA_LOADER_DRIVER_OVERRIDE=llvmpipe
export MESA_GL_VERSION_OVERRIDE=4.6
export MESA_GLSL_VERSION_OVERRIDE=460

if [ "${BLACKHOLE_WORKSPACE_DISPLAY:-xvfb}" = xvfb ] && [ "${BH_WORKSPACE_XVFB_ACTIVE:-0}" != 1 ]; then
  command -v xvfb-run >/dev/null 2>&1 || {
    echo "xvfb-run is required for workspace screenshots" >&2
    exit 2
  }
  BH_WORKSPACE_XVFB_ACTIVE=1
  export BH_WORKSPACE_XVFB_ACTIVE
  exec xvfb-run -a -s '-screen 0 2560x1440x24' "$0" "$build_dir"
fi

command -v glxinfo >/dev/null 2>&1 || {
  echo "glxinfo is required for workspace screenshots" >&2
  exit 2
}
glxinfo -B > "$artifact_dir/glxinfo.txt"
if ! grep -qi llvmpipe "$artifact_dir/glxinfo.txt"; then
  echo "The selected display does not use Mesa llvmpipe" >&2
  exit 2
fi
if ! awk '/OpenGL core profile version string:/ { sub(/^.*string: /, ""); split($0, parts, " "); if (parts[1] ~ /^4\.[6-9]/ || parts[1] ~ /^[5-9]\./) found=1 } END { exit !found }' "$artifact_dir/glxinfo.txt"; then
  echo "Mesa did not expose OpenGL 4.6" >&2
  exit 2
fi

result=0
for configuration in 1280x720:1 1920x1080:1 2560x1440:2; do
  size=${configuration%:*}
  scale=${configuration#*:}
  for workspace in simulator gororoba diagnostics; do
    prefix=$artifact_dir/$workspace-$size-scale$scale
    if ! "$build_dir/Blackhole" --workspace-screenshot "$prefix" \
      --workspace "$workspace" --window-size "$size" --ui-scale "$scale" \
      > "$prefix.log" 2>&1; then
      echo "Workspace capture failed: $prefix (see $prefix.log)" >&2
      result=1
      continue
    fi
    if ! "$PYTHON" scripts/ci/check_workspace_layout.py "$prefix.json" "$prefix.first.json"; then
      result=1
    fi
  done
done
exit "$result"
