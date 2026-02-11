#!/bin/bash
# ============================================================================
# Blackhole Profiling Build Script
# ============================================================================
# Builds optimized binary suitable for profiling with:
# - perf (Linux performance profiler)
# - valgrind (memory/cache profiler)
# - flamegraph generation
# - Full optimization maintained for realistic profiling
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
BUILD_DIR="${PROJECT_ROOT}/build-profiling"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}============================================================================${NC}"
echo -e "${BLUE}Blackhole Profiling Build${NC}"
echo -e "${BLUE}============================================================================${NC}"
echo ""

status() {
    echo -e "${GREEN}==>${NC} $1"
}

# Clean previous profiling build
if [ -d "${BUILD_DIR}" ]; then
    status "Cleaning previous profiling build..."
    rm -rf "${BUILD_DIR}"
fi

mkdir -p "${BUILD_DIR}"
cd "${PROJECT_ROOT}"

# Conan setup
status "Installing dependencies..."
"${SCRIPT_DIR}/conan_install.sh" "RelWithDebInfo" "${BUILD_DIR}"

# CMake configuration for profiling
status "Configuring for profiling (RelWithDebInfo + perf/valgrind support)..."
cd "${BUILD_DIR}"

cmake .. \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DENABLE_NATIVE_ARCH=ON \
    -DENABLE_LTO=OFF \
    -DENABLE_FAST_MATH=OFF \
    -DENABLE_PERF_PROFILING=ON \
    -DENABLE_VALGRIND_FRIENDLY=ON \
    -DENABLE_PROFILING=ON \
    -DENABLE_WERROR=OFF

if [ $? -ne 0 ]; then
    echo "CMake configuration failed!"
    exit 1
fi

# Build
NUM_CORES=$(nproc 2>/dev/null || echo 4)
status "Building profiling binary (${NUM_CORES} cores)..."
cmake --build . --parallel "${NUM_CORES}" --target Blackhole

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

EXECUTABLE="${BUILD_DIR}/Blackhole"

echo ""
echo -e "${GREEN}============================================================================${NC}"
echo -e "${GREEN}PROFILING BUILD SUCCESS!${NC}"
echo -e "${GREEN}============================================================================${NC}"
echo ""
echo "Executable: ${EXECUTABLE}"
echo "Size: $(du -h "${EXECUTABLE}" | cut -f1)"
echo ""

# Check for debugging symbols
if file "${EXECUTABLE}" | grep -q "not stripped"; then
    status "Debug symbols: Present (required for profiling)"
else
    echo -e "${YELLOW}WARNING: Debug symbols not found!${NC}"
fi

echo ""
echo -e "${BLUE}=== Profiling Tool Usage ===${NC}"
echo ""

# perf instructions
if command -v perf &> /dev/null; then
    status "Linux perf (available):"
    echo "  Record CPU profile:"
    echo "    perf record -F 99 -g ${EXECUTABLE}"
    echo ""
    echo "  View report:"
    echo "    perf report"
    echo ""
    echo "  Generate flamegraph:"
    echo "    perf script | stackcollapse-perf.pl | flamegraph.pl > flame.svg"
    echo ""

    # Check for flamegraph tools
    if ! command -v stackcollapse-perf.pl &> /dev/null; then
        echo -e "${YELLOW}  NOTE: flamegraph tools not found. Install with:${NC}"
        echo "    git clone https://github.com/brendangregg/FlameGraph"
        echo "    sudo cp FlameGraph/*.pl /usr/local/bin/"
        echo ""
    fi
else
    echo -e "${YELLOW}perf: Not available (Linux only)${NC}"
    echo ""
fi

# valgrind instructions
if command -v valgrind &> /dev/null; then
    status "Valgrind (available):"
    echo "  Memory check:"
    echo "    valgrind --leak-check=full ${EXECUTABLE}"
    echo ""
    echo "  Cache profiling:"
    echo "    valgrind --tool=cachegrind ${EXECUTABLE}"
    echo "    cg_annotate cachegrind.out.*"
    echo ""
    echo "  Callgrind profiling:"
    echo "    valgrind --tool=callgrind ${EXECUTABLE}"
    echo "    kcachegrind callgrind.out.*  # (requires KCachegrind)"
    echo ""
else
    echo -e "${YELLOW}valgrind: Not installed${NC}"
    echo "  Install: sudo pacman -S valgrind  # or: sudo apt install valgrind"
    echo ""
fi

# gprof instructions (if enabled)
if grep -q "ENABLE_GPROF" "${PROJECT_ROOT}/CMakeLists.txt" 2>/dev/null; then
    echo "For gprof profiling, rebuild with:"
    echo "  cmake -DENABLE_GPROF=ON .. && cmake --build ."
    echo "  ${EXECUTABLE}  # generates gmon.out"
    echo "  gprof ${EXECUTABLE} gmon.out > analysis.txt"
    echo ""
fi

# heaptrack instructions
if command -v heaptrack &> /dev/null; then
    status "Heaptrack (available):"
    echo "  Memory allocation profiling:"
    echo "    heaptrack ${EXECUTABLE}"
    echo "    heaptrack_gui heaptrack.*.gz"
    echo ""
else
    echo "Heaptrack: Not installed (optional)"
    echo "  Install: sudo pacman -S heaptrack  # or: sudo apt install heaptrack"
    echo ""
fi

# hotspot instructions
if command -v hotspot &> /dev/null; then
    status "Hotspot GUI (available):"
    echo "  Visual performance analysis:"
    echo "    hotspot ${EXECUTABLE}"
    echo ""
else
    echo "Hotspot: Not installed (optional)"
    echo "  Install: sudo pacman -S hotspot  # or from https://github.com/KDAB/hotspot"
    echo ""
fi

echo -e "${GREEN}============================================================================${NC}"
echo ""
echo "Profiling build complete. Run with:"
echo "  cd ${BUILD_DIR} && ./Blackhole"
echo ""

exit 0
