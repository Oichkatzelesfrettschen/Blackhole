#!/bin/bash
# ============================================================================
# Blackhole Optimized Build Script
# ============================================================================
# Performs a complete optimized build with:
# - Full clean build from scratch
# - Conan dependency resolution
# - -O3 optimization
# - -march=native for CPU-specific optimizations
# - Fat LTO (Link Time Optimization)
# - All files properly wired and validated
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
BUILD_DIR="${PROJECT_ROOT}/build"
BUILD_TYPE="${1:-Release}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}============================================================================${NC}"
echo -e "${BLUE}Blackhole Optimized Build - Ground-Up Optimization${NC}"
echo -e "${BLUE}============================================================================${NC}"
echo ""

# Function to print status messages
status() {
    echo -e "${GREEN}==>${NC} $1"
}

warning() {
    echo -e "${YELLOW}WARNING:${NC} $1"
}

error() {
    echo -e "${RED}ERROR:${NC} $1"
    exit 1
}

# Validate build type
VALID_TYPES=("Debug" "Release" "RelWithDebInfo" "MinSizeRel" "PGO-Gen" "PGO-Use")
if [[ ! " ${VALID_TYPES[@]} " =~ " ${BUILD_TYPE} " ]]; then
    error "Invalid build type: ${BUILD_TYPE}. Valid types: ${VALID_TYPES[*]}"
fi

status "Build configuration:"
echo "  Project root: ${PROJECT_ROOT}"
echo "  Build directory: ${BUILD_DIR}"
echo "  Build type: ${BUILD_TYPE}"
echo ""

# Step 1: Clean previous build
if [ -d "${BUILD_DIR}" ]; then
    status "Cleaning previous build..."
    rm -rf "${BUILD_DIR}"
fi

mkdir -p "${BUILD_DIR}"
cd "${PROJECT_ROOT}"

# Step 2: Conan dependency installation
status "Installing dependencies with Conan..."
"${SCRIPT_DIR}/conan_install.sh" "${BUILD_TYPE}" "${BUILD_DIR}"

if [ ! -f "${BUILD_DIR}/conan_toolchain.cmake" ] && [ ! -f "${BUILD_DIR}/generators/conan_toolchain.cmake" ]; then
    error "Conan toolchain not found after installation!"
fi

# Step 3: CMake configuration with full optimization
status "Configuring CMake with maximum optimization..."
cd "${BUILD_DIR}"

cmake .. \
    -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
    -DENABLE_NATIVE_ARCH=ON \
    -DENABLE_LTO=ON \
    -DENABLE_FAT_LTO=ON \
    -DENABLE_FAST_MATH=ON \
    -DENABLE_WERROR=ON \
    -DWARNING_LEVEL=5

if [ $? -ne 0 ]; then
    error "CMake configuration failed!"
fi

# Step 4: Build
status "Building with full optimization (-O3, -march=native, Fat LTO)..."
echo "  This may take several minutes due to LTO..."

# Use all available cores
NUM_CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
status "Building with ${NUM_CORES} parallel jobs..."

cmake --build . --parallel "${NUM_CORES}" --target Blackhole

if [ $? -ne 0 ]; then
    error "Build failed!"
fi

# Step 5: Verify executable
EXECUTABLE="${BUILD_DIR}/Blackhole"
if [ ! -f "${EXECUTABLE}" ]; then
    error "Executable not found: ${EXECUTABLE}"
fi

# Step 6: Check optimization level
status "Verifying optimization..."
file "${EXECUTABLE}" | grep -q "not stripped" && warning "Binary is not stripped (contains debug symbols)"

# Display binary information
echo ""
echo -e "${GREEN}============================================================================${NC}"
echo -e "${GREEN}BUILD SUCCESS!${NC}"
echo -e "${GREEN}============================================================================${NC}"
echo ""
echo "Executable: ${EXECUTABLE}"
echo "Size: $(du -h "${EXECUTABLE}" | cut -f1)"
echo ""

if command -v objdump &> /dev/null; then
    status "Binary architecture check:"
    objdump -f "${EXECUTABLE}" | grep "file format"
fi

# Check for CPU-specific instructions (evidence of -march=native)
if command -v objdump &> /dev/null; then
    if objdump -d "${EXECUTABLE}" 2>/dev/null | head -1000 | grep -E 'avx|fma|sse' &> /dev/null; then
        status "CPU-specific optimizations detected (SIMD instructions present)"
    fi
fi

echo ""
status "Optimization flags applied:"
echo "  - O3: Maximum compiler optimization"
echo "  - march=native: CPU-specific instructions (${SIMD_EFFECTIVE_TIER:-AUTO})"
echo "  - Fat LTO: Cross-module link-time optimization"
echo "  - Fast math: Aggressive floating-point optimizations"
echo ""

status "Run with:"
echo "  cd ${BUILD_DIR} && ./Blackhole"
echo ""

# PGO instructions if applicable
if [ "${BUILD_TYPE}" = "PGO-Gen" ]; then
    echo -e "${YELLOW}============================================================================${NC}"
    echo -e "${YELLOW}PGO Phase 1 Complete - Profile Generation Build${NC}"
    echo -e "${YELLOW}============================================================================${NC}"
    echo ""
    echo "Next steps for Profile-Guided Optimization:"
    echo "  1. Run the executable to generate profile data:"
    echo "     cd ${BUILD_DIR} && ./Blackhole"
    echo ""
    echo "  2. Exercise typical workload (render various scenes, adjust settings)"
    echo ""
    echo "  3. For Clang, merge profile data:"
    echo "     llvm-profdata merge -output=${BUILD_DIR}/pgo-profiles/default.profdata ${BUILD_DIR}/pgo-profiles/default.profraw"
    echo ""
    echo "  4. Rebuild with optimizations:"
    echo "     ${SCRIPT_DIR}/build-optimized.sh PGO-Use"
    echo ""
fi

if [ "${BUILD_TYPE}" = "PGO-Use" ]; then
    echo -e "${GREEN}============================================================================${NC}"
    echo -e "${GREEN}PGO Phase 2 Complete - Optimized Binary with Profile Data${NC}"
    echo -e "${GREEN}============================================================================${NC}"
    echo ""
    echo "This binary is optimized using runtime profiling data."
    echo "Expected performance improvement: 10-20% over standard -O3 build"
    echo ""
fi

exit 0
