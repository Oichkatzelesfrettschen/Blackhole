#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

# Parse arguments
FORCE_REINSTALL=0
CMAKE_PRESET=""
POSITIONAL_ARGS=()
PRESET_EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --force-reinstall)
      FORCE_REINSTALL=1
      shift
      ;;
    --cmake-preset|--preset)
      if [[ $# -lt 2 ]]; then
        echo "ERROR: $1 requires a preset name" >&2
        exit 2
      fi
      CMAKE_PRESET="$2"
      shift 2
      ;;
    *)
      POSITIONAL_ARGS+=("$1")
      shift
      ;;
  esac
done

PRESET_BUILD_TYPE=""
PRESET_OUTPUT_DIR_REL=""
if [[ -n "${CMAKE_PRESET}" ]]; then
  case "${CMAKE_PRESET}" in
    release)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build"
      ;;
    debug)
      PRESET_BUILD_TYPE="Debug"
      PRESET_OUTPUT_DIR_REL="build"
      ;;
    glsl-only)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/GLSL-Only"
      ;;
    cuda-only)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/CUDA-Only"
      ;;
    blender-bridge)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/BlenderBridge"
      ;;
    full-dev)
      PRESET_BUILD_TYPE="RelWithDebInfo"
      PRESET_OUTPUT_DIR_REL="build/FullDev"
      ;;
    docs)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/Docs"
      ;;
    microbench)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/Microbench"
      PRESET_EXTRA_ARGS+=(
        "-o" "blackhole/*:enable_google_benchmark=True"
        "-o" "blackhole/*:enable_highway=False"
        "-c:h" "tools.build:cxxflags=['-Wno-c2y-extensions']"
        "-c:b" "tools.build:cxxflags=['-Wno-c2y-extensions']"
      )
      ;;
    release-mimalloc)
      PRESET_BUILD_TYPE="Release"
      PRESET_OUTPUT_DIR_REL="build/ReleaseMimalloc"
      PRESET_EXTRA_ARGS+=("-o" "blackhole/*:enable_mimalloc=True")
      ;;
    *)
      echo "ERROR: Unsupported preset '${CMAKE_PRESET}' for Conan install." >&2
      exit 2
      ;;
  esac
fi

BUILD_TYPE="${POSITIONAL_ARGS[0]:-${PRESET_BUILD_TYPE:-Release}}"
OUTPUT_DIR_REL="${POSITIONAL_ARGS[1]:-${PRESET_OUTPUT_DIR_REL:-build}}"
OUTPUT_DIR="${ROOT}/${OUTPUT_DIR_REL}"
EXTRA_ARGS=("${PRESET_EXTRA_ARGS[@]}" "${POSITIONAL_ARGS[@]:2}")

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

ROOT_USER_PRESETS="${ROOT}/CMakeUserPresets.json"
if [[ -f "${ROOT_USER_PRESETS}" ]] && rg -q '"conan"' "${ROOT_USER_PRESETS}"; then
  GENERATED_USER_PRESETS_DEST="${OUTPUT_DIR}/conan-generated-CMakeUserPresets.json"
  mv "${ROOT_USER_PRESETS}" "${GENERATED_USER_PRESETS_DEST}"
  echo "Moved Conan-generated root CMakeUserPresets.json to ${OUTPUT_DIR_REL}/conan-generated-CMakeUserPresets.json to avoid preset-name collisions."
fi

echo ""
echo "Conan install complete."
echo "  Dependencies cached in: .conan/"
echo "  CMake toolchain in: ${OUTPUT_DIR_REL}/"
echo ""
echo "Next steps:"
if [[ -n "${CMAKE_PRESET}" ]]; then
  echo "  cmake --preset ${CMAKE_PRESET}"
else
  echo "  cmake --preset release   # or: cmake -B ${OUTPUT_DIR_REL} -DCMAKE_BUILD_TYPE=${BUILD_TYPE}"
fi
echo "  cmake --build ${OUTPUT_DIR_REL}"
