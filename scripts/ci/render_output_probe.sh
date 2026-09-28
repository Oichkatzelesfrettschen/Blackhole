#!/bin/sh
set -eu

build_dir=${1:-build/CI}
artifact_dir=${BLACKHOLE_RENDER_ARTIFACTS:-$build_dir/render-output-artifacts}
mkdir -p "$artifact_dir"
# CTest runs the test from the build directory, so the test and the verifier
# agree on the receipt only through an absolute path.
artifact_dir=$(cd "$artifact_dir" && pwd)
rm -f "$artifact_dir/rendered_output_validation.pass"
export BLACKHOLE_RENDER_ARTIFACTS=$artifact_dir
export LIBGL_ALWAYS_SOFTWARE=1
export MESA_LOADER_DRIVER_OVERRIDE=llvmpipe
export MESA_GL_VERSION_OVERRIDE=4.6
export MESA_GLSL_VERSION_OVERRIDE=460

if [ "${BLACKHOLE_RENDER_DISPLAY:-xvfb}" = xvfb ] && [ "${BH_RENDER_XVFB_ACTIVE:-0}" != 1 ]; then
  command -v xvfb-run >/dev/null 2>&1 || {
    echo "xvfb-run is required for the rendered-output lane" >&2
    exit 2
  }
  BH_RENDER_XVFB_ACTIVE=1
  export BH_RENDER_XVFB_ACTIVE
  exec xvfb-run -a -s '-screen 0 1024x768x24' "$0" "$build_dir"
fi

command -v glxinfo >/dev/null 2>&1 || {
  echo "glxinfo is required to verify the GL context" >&2
  exit 2
}
glxinfo -B > "$artifact_dir/glxinfo.txt"
if ! grep -qi llvmpipe "$artifact_dir/glxinfo.txt"; then
  echo "The selected display does not use Mesa llvmpipe" >&2
  exit 2
fi
if ! awk '/OpenGL core profile version string:/ { sub(/^.*string: /, ""); split($0, parts, " "); if (parts[1] ~ /^4\.[6-9]/ || parts[1] ~ /^[5-9]\./) found=1 } END { exit !found }' "$artifact_dir/glxinfo.txt"; then
  echo "Mesa did not expose OpenGL 4.6 in the selected display" >&2
  exit 2
fi
ctest --test-dir "$build_dir" -L render-output --output-on-failure --no-tests=error
: "${PYTHON:?Set PYTHON to the configured interpreter}"
"$PYTHON" scripts/verify_claims_matrix.py \
  --source-dir . --build-dir "$build_dir" \
  --manifest docs/physics/claims_evidence.json \
  --md-out "$artifact_dir/claims.md" --json-out "$artifact_dir/claims.json" \
  --require-render-passing
