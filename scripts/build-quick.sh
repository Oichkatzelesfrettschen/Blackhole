#!/usr/bin/env bash
# Quick build script - standardized entry point
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_TYPE="${1:-Release}"
CLEAN=0

# Parse flags
for arg in "$@"; do
  case "$arg" in
    --clean)
      CLEAN=1
      ;;
    Debug|Release|RelWithDebInfo)
      BUILD_TYPE="$arg"
      ;;
  esac
done

echo "========================================="
echo "  Blackhole Quick Build"
echo "  Type: ${BUILD_TYPE}"
echo "========================================="
echo ""

# Clean if requested
if (( CLEAN == 1 )); then
  echo "🧹 Cleaning build artifacts..."
  rm -rf "${ROOT}/build" "${ROOT}/.conan"
  echo ""
fi

# Step 1: Conan install
echo "📦 Installing dependencies with Conan..."
"${ROOT}/scripts/conan_install.sh" "${BUILD_TYPE}" build
echo ""

# Step 2: CMake configure
echo "⚙️  Configuring CMake..."
cd "${ROOT}/build"
cmake .. \
  -G "Unix Makefiles" \
  -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
  -DCMAKE_TOOLCHAIN_FILE="${ROOT}/build/Release/generators/conan_toolchain.cmake"
echo ""

# Step 3: Build
echo "🔨 Building Blackhole..."
make -j$(nproc) Blackhole
echo ""

# Success
echo "========================================="
echo "✅ BUILD SUCCESS!"
echo "========================================="
echo ""
echo "Executable: ${ROOT}/build/Blackhole"
echo ""
echo "Run with:"
echo "  cd ${ROOT}/build && ./Blackhole"
echo ""
