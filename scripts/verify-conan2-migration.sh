#!/bin/bash
# ============================================================================
# Conan 2.x Migration Verification Script
# ============================================================================
# Verifies that the Conan 2.x migration was successful
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}============================================================================${NC}"
echo -e "${BLUE}Conan 2.x Migration Verification${NC}"
echo -e "${BLUE}============================================================================${NC}"
echo ""

pass=0
fail=0
warn=0

check() {
    local test_name="$1"
    local command="$2"

    echo -n "Checking: $test_name... "

    if eval "$command" &>/dev/null; then
        echo -e "${GREEN}✓ PASS${NC}"
        ((pass++))
        return 0
    else
        echo -e "${RED}✗ FAIL${NC}"
        ((fail++))
        return 1
    fi
}

check_warn() {
    local test_name="$1"
    local command="$2"

    echo -n "Checking: $test_name... "

    if eval "$command" &>/dev/null; then
        echo -e "${GREEN}✓ PASS${NC}"
        ((pass++))
        return 0
    else
        echo -e "${YELLOW}⚠ WARN${NC}"
        ((warn++))
        return 1
    fi
}

info() {
    echo -e "${BLUE}$1${NC}"
}

section() {
    echo ""
    echo -e "${BLUE}=== $1 ===${NC}"
}

# Check Conan version
section "Conan Installation"
check "Conan 2.x installed" "conan --version | grep -E '^Conan version 2\.[0-9]+'"

# Check conanfile.py
section "Conanfile Configuration"
cd "${PROJECT_ROOT}"

check "conanfile.py exists" "test -f conanfile.py"
check "Version is 0.2" "grep -q 'version = \"0.2\"' conanfile.py"
check "Uses ConanFile from conan" "grep -q 'from conan import ConanFile' conanfile.py"
check "Uses cmake_layout" "grep -q 'from conan.tools.cmake import cmake_layout' conanfile.py"
check "Has validate() method" "grep -q 'def validate(self):' conanfile.py"

# Check updated packages
section "Package Versions"
check "xsimd 14.0.0" "grep -q 'xsimd/14.0.0' conanfile.py"
check "highway 1.3.0" "grep -q 'highway/1.3.0' conanfile.py"
check "entt 3.16.0" "grep -q 'entt/3.16.0' conanfile.py"
check "spdlog 1.17.0" "grep -q 'spdlog/1.17.0' conanfile.py"
check "gtest 1.17.0" "grep -q 'gtest/1.17.0' conanfile.py"
check "z3 4.15.4" "grep -q 'z3/4.15.4' conanfile.py"
check "meshoptimizer 1.0" "grep -q 'meshoptimizer/1.0' conanfile.py"
check "eigen 3.4.1" "grep -q 'eigen/3.4.1' conanfile.py"

# Check C++17
section "C++ Standard"
check "CMakeLists.txt uses C++17" "grep -q 'set(BLACKHOLE_CXX_STANDARD 17)' CMakeLists.txt"
check "BLACKHOLE_CXX17 defined" "grep -q 'BLACKHOLE_CXX17=1' CMakeLists.txt"
check "C++23 references removed" "! grep -q 'BLACKHOLE_CXX23' CMakeLists.txt"

# Check build artifacts
section "Build Verification"
if [ -d "build" ]; then
    check_warn "Build directory exists" "test -d build"
    check_warn "Blackhole executable exists" "test -f build/Blackhole"

    if [ -f "build/Blackhole" ]; then
        check_warn "Binary is executable" "test -x build/Blackhole"
        check_warn "Binary has debug symbols" "file build/Blackhole | grep -q 'not stripped'"
        check_warn "Binary has optimizations" "objdump -d build/Blackhole 2>/dev/null | head -1000 | grep -q -E 'fma|avx'"
    fi
else
    echo -e "${YELLOW}⚠ Build directory not found (run build first)${NC}"
fi

# Check Conan cache
section "Conan Cache"
if conan list "*" 2>/dev/null | grep -q "Local Cache"; then
    check "Conan cache populated" "conan list '*' 2>/dev/null | grep -q 'xsimd/14.0.0'"
    check_warn "xsimd 14.0.0 cached" "conan list 'xsimd/*' 2>/dev/null | grep -q '14.0.0'"
    check_warn "highway 1.3.0 cached" "conan list 'highway/*' 2>/dev/null | grep -q '1.3.0'"
    check_warn "entt 3.16.0 cached" "conan list 'entt/*' 2>/dev/null | grep -q '3.16.0'"
else
    echo -e "${YELLOW}⚠ Conan cache empty (packages will download on first build)${NC}"
fi

# Check OpenGL stack
section "OpenGL Stack"
check "glfw 3.4" "grep -q 'glfw/3.4' conanfile.py"
check "glbinding 3.5.0" "grep -q 'glbinding/3.5.0' conanfile.py"
check "glm 1.0.1" "grep -q 'glm/1.0.1' conanfile.py"
check "imgui docking" "grep -q 'imgui/1.92.5-docking' conanfile.py"

# Check no deprecated Conan 1.x features
section "Conan 1.x Deprecation Check"
check "No cpp_info.names" "! grep -q 'cpp_info.names' conanfile.py"
check "No cpp_info.filenames" "! grep -q 'cpp_info.filenames' conanfile.py"
check "No env_info" "! grep -q 'env_info' conanfile.py"
check "No user_info" "! grep -q 'user_info' conanfile.py"

# Summary
echo ""
echo -e "${BLUE}============================================================================${NC}"
echo -e "${BLUE}Verification Summary${NC}"
echo -e "${BLUE}============================================================================${NC}"
echo ""

echo -e "${GREEN}Passed:  $pass${NC}"
if [ $warn -gt 0 ]; then
    echo -e "${YELLOW}Warnings: $warn${NC}"
fi
if [ $fail -gt 0 ]; then
    echo -e "${RED}Failed:  $fail${NC}"
fi

echo ""

if [ $fail -eq 0 ]; then
    echo -e "${GREEN}✓ Migration verification PASSED${NC}"
    echo ""
    echo "All checks passed! The Conan 2.x migration is successful."
    echo ""
    if [ $warn -gt 0 ]; then
        echo -e "${YELLOW}Note: $warn warnings (usually build artifacts not present yet)${NC}"
        echo "Run ./scripts/build-optimized.sh Release to build"
    fi
    exit 0
else
    echo -e "${RED}✗ Migration verification FAILED${NC}"
    echo ""
    echo "Some checks failed. Review the output above."
    exit 1
fi
