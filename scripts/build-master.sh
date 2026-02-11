#!/bin/bash
# ============================================================================
# Blackhole Master Build Script
# ============================================================================
# Comprehensive build orchestration with multiple optimization profiles:
# - Release: Maximum optimization (-O3, -march=native, Fat LTO)
# - Profiling: Optimized with profiling support (perf, valgrind, flamegraph)
# - PGO: Profile-Guided Optimization (two-phase build)
# - Debug: Full debugging support
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

show_banner() {
    echo -e "${CYAN}"
    cat << 'EOF'
╔══════════════════════════════════════════════════════════════════════════╗
║                  Blackhole Build System Master Control                   ║
║                 Ground-Up Optimization & Profiling Suite                 ║
╚══════════════════════════════════════════════════════════════════════════╝
EOF
    echo -e "${NC}"
}

show_menu() {
    echo ""
    echo -e "${BLUE}Select Build Configuration:${NC}"
    echo ""
    echo "  ${GREEN}1)${NC} Release Build (Maximum Performance)"
    echo "     - O3 optimization"
    echo "     - march=native (CPU-specific)"
    echo "     - Fat LTO (Link Time Optimization)"
    echo "     - Fast math"
    echo ""
    echo "  ${GREEN}2)${NC} Profiling Build"
    echo "     - Optimized with debug symbols"
    echo "     - perf, valgrind, flamegraph support"
    echo "     - Frame pointers preserved"
    echo ""
    echo "  ${GREEN}3)${NC} PGO Build (Profile-Guided Optimization)"
    echo "     - Phase 1: Generate profile data"
    echo "     - Phase 2: Optimize using profiles"
    echo "     - 10-20% performance gain over -O3"
    echo ""
    echo "  ${GREEN}4)${NC} Debug Build"
    echo "     - No optimization, full debug info"
    echo "     - Sanitizers available"
    echo "     - Valgrind-friendly"
    echo ""
    echo "  ${GREEN}5)${NC} Clean All Builds"
    echo "     - Remove all build directories"
    echo "     - Fresh start"
    echo ""
    echo "  ${GREEN}6)${NC} System Information"
    echo "     - Show CPU capabilities"
    echo "     - Available tools"
    echo "     - Build environment"
    echo ""
    echo "  ${GREEN}q)${NC} Quit"
    echo ""
}

system_info() {
    echo -e "${BLUE}============================================================================${NC}"
    echo -e "${BLUE}System Information${NC}"
    echo -e "${BLUE}============================================================================${NC}"
    echo ""

    echo -e "${GREEN}CPU Information:${NC}"
    if [ -f /proc/cpuinfo ]; then
        CPU_MODEL=$(grep "model name" /proc/cpuinfo | head -1 | cut -d: -f2 | xargs)
        CPU_CORES=$(nproc)
        echo "  Model: ${CPU_MODEL}"
        echo "  Cores: ${CPU_CORES}"

        echo ""
        echo -e "${GREEN}CPU Features (SIMD):${NC}"
        if grep -q "avx512" /proc/cpuinfo; then
            echo "  ✓ AVX-512 (detected)"
        fi
        if grep -q "avx2" /proc/cpuinfo; then
            echo "  ✓ AVX2 (detected)"
        fi
        if grep -q " avx " /proc/cpuinfo; then
            echo "  ✓ AVX (detected)"
        fi
        if grep -q "sse4_2" /proc/cpuinfo; then
            echo "  ✓ SSE4.2 (detected)"
        fi
        if grep -q " fma " /proc/cpuinfo; then
            echo "  ✓ FMA (detected)"
        fi
    fi

    echo ""
    echo -e "${GREEN}Compiler:${NC}"
    if command -v g++ &> /dev/null; then
        echo "  GCC: $(g++ --version | head -1)"
    fi
    if command -v clang++ &> /dev/null; then
        echo "  Clang: $(clang++ --version | head -1)"
    fi

    echo ""
    echo -e "${GREEN}Build Tools:${NC}"
    command -v cmake &> /dev/null && echo "  ✓ CMake: $(cmake --version | head -1 | awk '{print $3}')" || echo "  ✗ CMake: Not found"
    command -v conan &> /dev/null && echo "  ✓ Conan: $(conan --version | head -1)" || echo "  ✗ Conan: Not found"
    command -v ninja &> /dev/null && echo "  ✓ Ninja: $(ninja --version)" || echo "  ✗ Ninja: Not found"

    echo ""
    echo -e "${GREEN}Profiling Tools:${NC}"
    command -v perf &> /dev/null && echo "  ✓ perf (Linux performance profiler)" || echo "  ✗ perf: Not available"
    command -v valgrind &> /dev/null && echo "  ✓ valgrind: $(valgrind --version)" || echo "  ✗ valgrind: Not installed"
    command -v hotspot &> /dev/null && echo "  ✓ hotspot (GUI profiler)" || echo "  ✗ hotspot: Not installed"
    command -v heaptrack &> /dev/null && echo "  ✓ heaptrack (memory profiler)" || echo "  ✗ heaptrack: Not installed"
    command -v stackcollapse-perf.pl &> /dev/null && echo "  ✓ FlameGraph tools" || echo "  ✗ FlameGraph: Not installed"

    echo ""
    echo -e "${GREEN}Memory:${NC}"
    if [ -f /proc/meminfo ]; then
        MEM_TOTAL=$(grep "MemTotal" /proc/meminfo | awk '{print $2}')
        MEM_GB=$((MEM_TOTAL / 1024 / 1024))
        echo "  Total: ${MEM_GB} GB"
    fi

    echo ""
}

clean_all() {
    echo -e "${YELLOW}Cleaning all build directories...${NC}"

    for dir in build build-profiling build-debug; do
        if [ -d "${PROJECT_ROOT}/${dir}" ]; then
            echo "  Removing ${dir}..."
            rm -rf "${PROJECT_ROOT}/${dir}"
        fi
    done

    # Clean Conan cache (optional)
    read -p "Also clean Conan cache? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        conan remove "*" -c 2>/dev/null || true
        echo "  Conan cache cleaned"
    fi

    echo -e "${GREEN}Clean complete!${NC}"
}

pgo_workflow() {
    echo -e "${BLUE}============================================================================${NC}"
    echo -e "${BLUE}Profile-Guided Optimization (PGO) Workflow${NC}"
    echo -e "${BLUE}============================================================================${NC}"
    echo ""

    PGO_BUILD_DIR="${PROJECT_ROOT}/build-pgo"

    echo -e "${YELLOW}Phase 1: Build with instrumentation${NC}"
    echo ""

    # Clean PGO directory
    if [ -d "${PGO_BUILD_DIR}" ]; then
        rm -rf "${PGO_BUILD_DIR}"
    fi

    # Build PGO-Gen
    "${SCRIPT_DIR}/build-optimized.sh" "PGO-Gen"

    if [ $? -ne 0 ]; then
        echo -e "${RED}PGO-Gen build failed!${NC}"
        return 1
    fi

    echo ""
    echo -e "${YELLOW}============================================================================${NC}"
    echo -e "${YELLOW}Run the executable to generate profile data:${NC}"
    echo -e "${YELLOW}============================================================================${NC}"
    echo ""
    echo "  cd ${PGO_BUILD_DIR} && ./Blackhole"
    echo ""
    echo "Exercise typical workload (render scenes, adjust settings, etc.)"
    echo ""
    read -p "Press Enter after you've finished profiling run..."

    # For Clang, merge profile data
    if command -v llvm-profdata &> /dev/null; then
        PROFRAW="${PGO_BUILD_DIR}/pgo-profiles/default.profraw"
        PROFDATA="${PGO_BUILD_DIR}/pgo-profiles/default.profdata"

        if [ -f "${PROFRAW}" ]; then
            echo ""
            echo -e "${YELLOW}Merging Clang profile data...${NC}"
            llvm-profdata merge -output="${PROFDATA}" "${PROFRAW}"

            if [ $? -eq 0 ]; then
                echo -e "${GREEN}Profile data merged successfully${NC}"
            else
                echo -e "${RED}Failed to merge profile data${NC}"
                return 1
            fi
        fi
    fi

    # Check if profile data exists
    if [ ! -d "${PGO_BUILD_DIR}/pgo-profiles" ]; then
        echo -e "${RED}Profile data not found! Did you run the executable?${NC}"
        return 1
    fi

    echo ""
    echo -e "${YELLOW}Phase 2: Build with profile optimization${NC}"
    echo ""

    # Build PGO-Use
    "${SCRIPT_DIR}/build-optimized.sh" "PGO-Use"

    if [ $? -eq 0 ]; then
        echo ""
        echo -e "${GREEN}============================================================================${NC}"
        echo -e "${GREEN}PGO Build Complete!${NC}"
        echo -e "${GREEN}============================================================================${NC}"
        echo ""
        echo "Optimized executable: ${PGO_BUILD_DIR}/Blackhole"
        echo ""
        echo "Expected improvement: 10-20% over standard -O3 build"
        echo ""
    else
        echo -e "${RED}PGO-Use build failed!${NC}"
        return 1
    fi
}

# Main script
show_banner

# Interactive mode if no arguments
if [ $# -eq 0 ]; then
    while true; do
        show_menu
        read -p "Enter choice: " choice
        echo ""

        case $choice in
            1)
                echo -e "${GREEN}Building Release (Maximum Performance)...${NC}"
                "${SCRIPT_DIR}/build-optimized.sh" "Release"
                echo ""
                read -p "Press Enter to continue..."
                ;;
            2)
                echo -e "${GREEN}Building Profiling Configuration...${NC}"
                "${SCRIPT_DIR}/build-profiling.sh"
                echo ""
                read -p "Press Enter to continue..."
                ;;
            3)
                pgo_workflow
                echo ""
                read -p "Press Enter to continue..."
                ;;
            4)
                echo -e "${GREEN}Building Debug Configuration...${NC}"
                "${SCRIPT_DIR}/build-optimized.sh" "Debug"
                echo ""
                read -p "Press Enter to continue..."
                ;;
            5)
                clean_all
                echo ""
                read -p "Press Enter to continue..."
                ;;
            6)
                system_info
                echo ""
                read -p "Press Enter to continue..."
                ;;
            q|Q)
                echo "Exiting..."
                exit 0
                ;;
            *)
                echo -e "${RED}Invalid choice!${NC}"
                sleep 1
                ;;
        esac
    done
else
    # Non-interactive mode
    case "$1" in
        release|Release)
            "${SCRIPT_DIR}/build-optimized.sh" "Release"
            ;;
        profiling|Profiling)
            "${SCRIPT_DIR}/build-profiling.sh"
            ;;
        pgo|PGO)
            pgo_workflow
            ;;
        debug|Debug)
            "${SCRIPT_DIR}/build-optimized.sh" "Debug"
            ;;
        clean)
            clean_all
            ;;
        info)
            system_info
            ;;
        *)
            echo "Usage: $0 {release|profiling|pgo|debug|clean|info}"
            exit 1
            ;;
    esac
fi
