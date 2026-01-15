#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

# Parse arguments
FORCE_REINSTALL=0
BUILD_TYPE="${1:-Release}"

# Check for --force-reinstall flag
for arg in "$@"; do
  if [[ "$arg" == "--force-reinstall" ]]; then
    FORCE_REINSTALL=1
  fi
done

OUTPUT_DIR_REL="${2:-build}"
OUTPUT_DIR="${ROOT}/${OUTPUT_DIR_REL}"
shift $(( $# > 1 ? 2 : $# )) || true

# Filter out --force-reinstall from extra args
EXTRA_ARGS=()
for arg in "$@"; do
  if [[ "$arg" != "--force-reinstall" ]]; then
    EXTRA_ARGS+=("$arg")
  fi
done

# Ensure output folder is inside the repo so cache/config stays repo-local
case "$OUTPUT_DIR" in
  ${ROOT}/*) ;; # ok
  *) echo "" >&2; echo "ERROR: conan install output folder must live under ${ROOT}" >&2; echo "Requested: ${OUTPUT_DIR}" >&2; exit 2 ;;
esac

# Ensure directories exist
mkdir -p "${OUTPUT_DIR}"

# Ensure conan uses repo-local home (set in conan_env.sh)
"${ROOT}/scripts/conan_init.sh"
"${ROOT}/scripts/conan_export_local_recipes.sh"

# Detect conan major version and adapt flags if necessary
CONAN_VER_STR="$(conan --version 2>/dev/null || true)"
# Fallback to 'conan --version' empty check
if [[ -z "${CONAN_VER_STR}" ]]; then
  echo "ERROR: 'conan' not found in PATH. Install Conan (recommended: 2.x) and retry." >&2
  exit 2
fi

# Extract major version number if possible (format: 'Conan version X.Y.Z')
if [[ "${CONAN_VER_STR}" =~ ([0-9]+)\. ]]; then
  CONAN_MAJOR=${BASH_REMATCH[1]}
else
  CONAN_MAJOR=1
fi

# Determine build policy
BUILD_POLICY="missing"
if (( FORCE_REINSTALL == 1 )); then
  BUILD_POLICY="*"
  echo "Force reinstall requested: rebuilding all dependencies"
fi

if (( CONAN_MAJOR >= 2 )); then
  echo "Using Conan ${CONAN_VER_STR} (2.x+) -- installing in ${OUTPUT_DIR_REL}"
  conan install "${ROOT}" \
    --output-folder="${OUTPUT_DIR}" \
    --build="${BUILD_POLICY}" \
    -s build_type="${BUILD_TYPE}" \
    -s compiler.cppstd=23 \
    -s:b build_type="${BUILD_TYPE}" \
    -s:b compiler.cppstd=23 \
    "${EXTRA_ARGS[@]}"
else
  echo "WARNING: Detected Conan ${CONAN_VER_STR} (1.x). Consider upgrading to Conan 2.x -- continuing using compatibility options."
  conan install "${ROOT}" \
    --output-folder="${OUTPUT_DIR}" \
    --build="${BUILD_POLICY}" \
    -s build_type="${BUILD_TYPE}" \
    -s compiler.cppstd=23 \
    -s:b build_type="${BUILD_TYPE}" \
    -s:b compiler.cppstd=23 \
    "${EXTRA_ARGS[@]}"
fi

echo ""
echo "Conan install complete."
echo "  Dependencies cached in: .conan/"
echo "  CMake toolchain in: ${OUTPUT_DIR_REL}/"
echo ""
echo "Next steps:"
echo "  cmake --preset release   # or: cmake -B ${OUTPUT_DIR_REL} -DCMAKE_BUILD_TYPE=${BUILD_TYPE}"
echo "  cmake --build ${OUTPUT_DIR_REL}"
