cmake_minimum_required(VERSION 3.21)

project(Blackhole
  VERSION 1.0.0
  DESCRIPTION "Black hole visualization with physically accurate ray tracing"
  LANGUAGES CXX
)

# ============================================================================
# Conan 2.x Integration
# ============================================================================
# Usage:
#   ./scripts/conan_install.sh Release <cmake-build-dir>
#   cmake --preset release (or: cmake -B <cmake-build-dir> -DCMAKE_BUILD_TYPE=Release)
#   cmake --build build
# ============================================================================

# Look for Conan-generated toolchain and dependencies
set(CONAN_TOOLCHAIN_PATH "")
if(CMAKE_TOOLCHAIN_FILE)
  if(NOT CMAKE_TOOLCHAIN_FILE MATCHES "conan_toolchain.cmake$")
    message(FATAL_ERROR "This project requires Conan's toolchain. Set CMAKE_TOOLCHAIN_FILE to conan_toolchain.cmake.")
  endif()
  set(CONAN_TOOLCHAIN_PATH "${CMAKE_TOOLCHAIN_FILE}")
elseif(EXISTS "${CMAKE_BINARY_DIR}/conan_toolchain.cmake")
  set(CONAN_TOOLCHAIN_PATH "${CMAKE_BINARY_DIR}/conan_toolchain.cmake")
elseif(EXISTS "${CMAKE_SOURCE_DIR}/build/conan_toolchain.cmake")
  set(CONAN_TOOLCHAIN_PATH "${CMAKE_SOURCE_DIR}/build/conan_toolchain.cmake")
elseif(EXISTS "${CMAKE_BINARY_DIR}/generators/conan_toolchain.cmake")
  set(CONAN_TOOLCHAIN_PATH "${CMAKE_BINARY_DIR}/generators/conan_toolchain.cmake")
elseif(EXISTS "${CMAKE_SOURCE_DIR}/build/Release/generators/conan_toolchain.cmake")
  set(CONAN_TOOLCHAIN_PATH "${CMAKE_SOURCE_DIR}/build/Release/generators/conan_toolchain.cmake")
endif()

if(CONAN_TOOLCHAIN_PATH)
  if(NOT CMAKE_TOOLCHAIN_FILE)
    include("${CONAN_TOOLCHAIN_PATH}")
  endif()
else()
  message(FATAL_ERROR "Conan toolchain not found. Run: ./scripts/conan_install.sh Release <cmake-build-dir>")
endif()

# ============================================================================
# C++ Standard (C++23 only)
# ============================================================================

set(BLACKHOLE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD ${BLACKHOLE_CXX_STANDARD})
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_compile_definitions(
  BLACKHOLE_CXX_STANDARD=${BLACKHOLE_CXX_STANDARD}
  BLACKHOLE_CXX23=1
)

message(STATUS "Using C++ standard: C++${BLACKHOLE_CXX_STANDARD}")

# Add Conan generators directory to module path
list(APPEND CMAKE_MODULE_PATH "${CMAKE_BINARY_DIR}")
list(APPEND CMAKE_PREFIX_PATH "${CMAKE_BINARY_DIR}")

# Also check cmake_layout default locations
if(EXISTS "${CMAKE_SOURCE_DIR}/build/Release/generators")
  list(APPEND CMAKE_PREFIX_PATH "${CMAKE_SOURCE_DIR}/build/Release/generators")
endif()
if(EXISTS "${CMAKE_SOURCE_DIR}/build/Debug/generators")
  list(APPEND CMAKE_PREFIX_PATH "${CMAKE_SOURCE_DIR}/build/Debug/generators")
endif()

find_package(imgui REQUIRED)
find_package(imguizmo REQUIRED)
find_package(glfw3 REQUIRED)
find_package(glbinding REQUIRED)
find_package(glm REQUIRED)
find_package(stb REQUIRED)
find_package(HighFive REQUIRED)
find_package(CLI11 REQUIRED)
find_package(nlohmann_json REQUIRED)
# SPIR-V Tooling removed in Phase 3 (C++23 -> GLSL transpilation)
# All SPIR-V compilation now uses GLSL 4.60 shader includes directly
# Validation and optional compilation still available via glslangValidator and glslc

# ============================================================================
# Mesh Optimization (meshoptimizer)
# ============================================================================

option(ENABLE_MESHOPTIMIZER "Enable meshoptimizer for geometry optimization" ON)
if(ENABLE_MESHOPTIMIZER)
  find_package(meshoptimizer CONFIG QUIET)
  if(meshoptimizer_FOUND)
    message(STATUS "meshoptimizer found: overdraw optimization available")
  else()
    message(STATUS "meshoptimizer not found: overdraw optimization disabled")
    set(ENABLE_MESHOPTIMIZER OFF)
  endif()
endif()

# ============================================================================
# Optional UI Layers
# ============================================================================

option(ENABLE_RMLUI "Enable RmlUi overlay" OFF)
if(ENABLE_RMLUI)
  find_package(rmlui REQUIRED)
endif()

option(ENABLE_TRACY "Enable Tracy profiling" OFF)
if(ENABLE_TRACY)
  find_package(Tracy REQUIRED)
endif()

option(ENABLE_Z3 "Enable Z3 constraint solver tooling" OFF)
if(ENABLE_Z3)
  find_package(Z3 CONFIG REQUIRED)
  if(TARGET z3::libz3)
    set(Z3_TARGET z3::libz3)
  elseif(TARGET z3::z3)
    set(Z3_TARGET z3::z3)
  elseif(TARGET Z3::Z3)
    set(Z3_TARGET Z3::Z3)
  else()
    message(FATAL_ERROR "Z3 target not found after find_package(Z3).")
  endif()
endif()

option(ENABLE_KTX "Enable KTX texture IO (optional)" OFF)
if(ENABLE_KTX)
  add_compile_definitions(BLACKHOLE_ENABLE_KTX=1)
endif()

# ============================================================================
# Taskflow (parallel task execution)
# ============================================================================

option(ENABLE_TASKFLOW "Enable Taskflow for parallel LUT generation" ON)
if(ENABLE_TASKFLOW)
  find_package(Taskflow CONFIG QUIET)
  if(Taskflow_FOUND)
    message(STATUS "Taskflow found: parallel batch processing available")
  else()
    message(STATUS "Taskflow not found: falling back to serial execution")
    set(ENABLE_TASKFLOW OFF)
  endif()
endif()

# ============================================================================
# xsimd (explicit SIMD abstraction library)
# ============================================================================

option(ENABLE_XSIMD "Enable xsimd for explicit SIMD vectorization" ON)
if(ENABLE_XSIMD)
  find_package(xsimd CONFIG QUIET)
  if(xsimd_FOUND)
    message(STATUS "xsimd found: explicit SIMD abstraction available")
  else()
    message(STATUS "xsimd not found: using Eigen auto-vectorization only")
    set(ENABLE_XSIMD OFF)
  endif()
endif()

# ============================================================================
# Highway (performance-portable SIMD with runtime dispatch)
# ============================================================================

option(ENABLE_HIGHWAY "Enable Highway for performance-portable SIMD" ON)
if(ENABLE_HIGHWAY)
  find_package(hwy CONFIG QUIET)
  if(hwy_FOUND)
    message(STATUS "Highway found: performance-portable SIMD available")
  else()
    message(STATUS "Highway not found: SIMD functionality limited to xsimd/Eigen")
    set(ENABLE_HIGHWAY OFF)
  endif()
endif()

# ============================================================================
# SLEEF (vectorized transcendental math functions)
# ============================================================================

option(ENABLE_SLEEF "Enable SLEEF for optimized vectorized transcendentals" ON)
if(ENABLE_SLEEF)
  find_package(sleef CONFIG QUIET)
  if(sleef_FOUND)
    message(STATUS "SLEEF found: vectorized sin/cos/sqrt available")
  else()
    message(STATUS "SLEEF not found: using xsimd transcendentals")
    set(ENABLE_SLEEF OFF)
  endif()
endif()

# Global compile definitions for SIMD flags
add_compile_definitions(BLACKHOLE_ENABLE_XSIMD=$<IF:$<BOOL:${ENABLE_XSIMD}>,1,0>)
add_compile_definitions(BLACKHOLE_ENABLE_SLEEF=$<IF:$<BOOL:${ENABLE_SLEEF}>,1,0>)
add_compile_definitions(BLACKHOLE_ENABLE_HIGHWAY=$<IF:$<BOOL:${ENABLE_HIGHWAY}>,1,0>)

option(ENABLE_OPENIMAGEIO "Enable OpenImageIO ingestion (optional)" OFF)
if(ENABLE_OPENIMAGEIO)
  add_compile_definitions(BLACKHOLE_ENABLE_OPENIMAGEIO=1)
endif()

# Optional: allow project to opt-in to using Eigen for physics math types.
# This requires Eigen to be present in the Conan toolchain/configuration.
option(ENABLE_EIGEN "Enable Eigen-backed physics math types (adds -DBLACKHOLE_USE_EIGEN)" OFF)
if(ENABLE_EIGEN)
  add_compile_definitions(BLACKHOLE_USE_EIGEN=1)
  message(STATUS "Eigen backend enabled: BLACKHOLE_USE_EIGEN will be defined for targets")
endif()

option(ENABLE_SHADER_WATCHER "Enable shader hot-reload file watcher" OFF)
if(ENABLE_SHADER_WATCHER)
  find_package(watcher REQUIRED)
  add_compile_definitions(BLACKHOLE_ENABLE_SHADER_WATCHER=1)
  message(STATUS "Shader watcher enabled: hot-reload support active")
endif()

# ============================================================================
# FastNoise2 (procedural noise generation)
# ============================================================================

option(ENABLE_FASTNOISE2 "Enable FastNoise2 for procedural texture generation" ON)
if(ENABLE_FASTNOISE2)
  find_package(FastNoise2 CONFIG QUIET)
  if(FastNoise2_FOUND)
    add_compile_definitions(BLACKHOLE_ENABLE_FASTNOISE2=1)
    message(STATUS "FastNoise2 found: procedural noise generation available")
  else()
    message(STATUS "FastNoise2 not found: procedural noise disabled")
    set(ENABLE_FASTNOISE2 OFF)
  endif()
endif()

# ============================================================================
# Optional non-Conan dependencies (FetchContent)
# ============================================================================

include(FetchContent)

option(ENABLE_IMNODES "Enable ImNodes UI module (FetchContent)" OFF)
if(ENABLE_IMNODES)
  FetchContent_Declare(
    imnodes
    GIT_REPOSITORY https://github.com/nelarius/imnodes.git
    GIT_TAG v0.5
  )
  FetchContent_MakeAvailable(imnodes)
endif()

option(ENABLE_AUTODIFF "Enable autodiff (FetchContent)" OFF)
if(ENABLE_AUTODIFF)
  FetchContent_Declare(
    autodiff
    GIT_REPOSITORY https://github.com/autodiff/autodiff.git
    GIT_TAG v1.0.3
  )
  FetchContent_MakeAvailable(autodiff)
endif()

option(ENABLE_ENZYME "Enable Enzyme autodiff (requires LLVM/Clang toolchain)" OFF)
set(ENZYME_CLANG "" CACHE FILEPATH "Path to clang with Enzyme plugin")
set(ENZYME_PLUGIN "" CACHE FILEPATH "Path to Enzyme LLVM plugin")
if(ENABLE_ENZYME)
  add_compile_definitions(ENABLE_ENZYME=1)
  message(STATUS "Enzyme enabled; configure ENZYME_CLANG and ENZYME_PLUGIN paths.")
endif()

option(ENABLE_AMREX "Enable AMReX (FetchContent, heavy)" OFF)
if(ENABLE_AMREX)
  FetchContent_Declare(
    amrex
    GIT_REPOSITORY https://github.com/AMReX-Codes/amrex.git
    GIT_TAG 23.08
  )
  FetchContent_MakeAvailable(amrex)
endif()

# ============================================================================
# ImPlot (vendored until Conan packages support ImGui 1.92+)
# ============================================================================

set(IMPLOT_SOURCE_DIR "${PROJECT_SOURCE_DIR}/external/implot")
if(NOT EXISTS "${IMPLOT_SOURCE_DIR}/implot.cpp")
  message(FATAL_ERROR "ImPlot sources not found in ${IMPLOT_SOURCE_DIR}. Run scripts/fetch_implot.sh.")
endif()

add_library(implot STATIC
  "${IMPLOT_SOURCE_DIR}/implot.cpp"
  "${IMPLOT_SOURCE_DIR}/implot_items.cpp"
)
target_include_directories(implot SYSTEM PUBLIC "${IMPLOT_SOURCE_DIR}")
target_link_libraries(implot PUBLIC imgui::imgui)
target_compile_options(implot PRIVATE -w)
add_library(implot::implot ALIAS implot)

# ============================================================================
# SIMD and Optimization Configuration
# ============================================================================
# Comprehensive SIMD detection and configuration for SSE through AVX-512.
# GLM, Eigen, and compiler flags are configured based on detected capabilities.
# ============================================================================

include(CheckCXXCompilerFlag)
include(CheckCXXSourceCompiles)

# SIMD tier: AUTO detects best available, or set explicitly to SSE2/SSE4/AVX/AVX2/AVX512
set(SIMD_TIER "AUTO" CACHE STRING "SIMD instruction set tier: AUTO, SSE2, SSE4, AVX, AVX2, AVX512")
set_property(CACHE SIMD_TIER PROPERTY STRINGS AUTO SSE2 SSE4 AVX AVX2 AVX512)

# Native architecture optimization (enables best SIMD for build machine)
option(ENABLE_NATIVE_ARCH "Enable -march=native for optimal SIMD on this CPU" OFF)

# Detect available SIMD extensions
message(STATUS "=== SIMD Detection ===")

# First, check compiler support for SIMD flags (required for code generation)
check_cxx_compiler_flag("-msse" COMPILER_SUPPORTS_SSE)
check_cxx_compiler_flag("-msse2" COMPILER_SUPPORTS_SSE2)
check_cxx_compiler_flag("-msse3" COMPILER_SUPPORTS_SSE3)
check_cxx_compiler_flag("-mssse3" COMPILER_SUPPORTS_SSSE3)
check_cxx_compiler_flag("-msse4.1" COMPILER_SUPPORTS_SSE41)
check_cxx_compiler_flag("-msse4.2" COMPILER_SUPPORTS_SSE42)
check_cxx_compiler_flag("-mfma" COMPILER_SUPPORTS_FMA)
check_cxx_compiler_flag("-mavx" COMPILER_SUPPORTS_AVX)
check_cxx_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
check_cxx_compiler_flag("-mavx512f" COMPILER_SUPPORTS_AVX512F)
check_cxx_compiler_flag("-mavx512dq" COMPILER_SUPPORTS_AVX512DQ)
check_cxx_compiler_flag("-mavx512cd" COMPILER_SUPPORTS_AVX512CD)
check_cxx_compiler_flag("-mavx512bw" COMPILER_SUPPORTS_AVX512BW)
check_cxx_compiler_flag("-mavx512vl" COMPILER_SUPPORTS_AVX512VL)

# For AUTO mode, detect actual CPU features via CPUID (not just compiler support)
# This ensures we only use instructions the CPU actually supports at runtime
include(CheckCXXSourceRuns)

if(SIMD_TIER STREQUAL "AUTO" AND NOT CMAKE_CROSSCOMPILING)
  # CPU feature detection using CPUID
  set(CMAKE_REQUIRED_FLAGS "")

  # Check AVX-512 support (requires both CPU and OS support via XGETBV)
  check_cxx_source_runs("
    #include <cpuid.h>
    #include <cstdint>
    int main() {
      unsigned int eax, ebx, ecx, edx;
      if (!__get_cpuid_count(7, 0, &eax, &ebx, &ecx, &edx)) return 1;
      bool avx512f = (ebx >> 16) & 1;
      bool avx512dq = (ebx >> 17) & 1;
      if (!avx512f || !avx512dq) return 1;
      // Check XGETBV for OS support of ZMM registers (bits 5,6,7 of XCR0)
      unsigned int xcr0_lo, xcr0_hi;
      asm volatile(\"xgetbv\" : \"=a\"(xcr0_lo), \"=d\"(xcr0_hi) : \"c\"(0));
      bool zmm_enabled = ((xcr0_lo >> 5) & 7) == 7;
      return zmm_enabled ? 0 : 1;
    }
  " CPU_HAS_AVX512)

  # Check AVX2 + FMA support
  check_cxx_source_runs("
    #include <cpuid.h>
    int main() {
      unsigned int eax, ebx, ecx, edx;
      if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) return 1;
      bool fma = (ecx >> 12) & 1;
      bool avx = (ecx >> 28) & 1;
      if (!fma || !avx) return 1;
      if (!__get_cpuid_count(7, 0, &eax, &ebx, &ecx, &edx)) return 1;
      bool avx2 = (ebx >> 5) & 1;
      return avx2 ? 0 : 1;
    }
  " CPU_HAS_AVX2)

  # Check AVX support
  check_cxx_source_runs("
    #include <cpuid.h>
    int main() {
      unsigned int eax, ebx, ecx, edx;
      if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) return 1;
      bool avx = (ecx >> 28) & 1;
      // Also check OSXSAVE to ensure OS supports AVX state
      bool osxsave = (ecx >> 27) & 1;
      return (avx && osxsave) ? 0 : 1;
    }
  " CPU_HAS_AVX)

  # Check SSE4.2 support
  check_cxx_source_runs("
    #include <cpuid.h>
    int main() {
      unsigned int eax, ebx, ecx, edx;
      if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) return 1;
      bool sse42 = (ecx >> 20) & 1;
      return sse42 ? 0 : 1;
    }
  " CPU_HAS_SSE42)

  # Report actual CPU capabilities
  set(CPU_DETECTED "")
  if(CPU_HAS_SSE42)
    list(APPEND CPU_DETECTED "SSE4.2")
  endif()
  if(CPU_HAS_AVX)
    list(APPEND CPU_DETECTED "AVX")
  endif()
  if(CPU_HAS_AVX2)
    list(APPEND CPU_DETECTED "AVX2+FMA")
  endif()
  if(CPU_HAS_AVX512)
    list(APPEND CPU_DETECTED "AVX-512")
  endif()
  list(JOIN CPU_DETECTED ", " CPU_DETECTED_STR)
  message(STATUS "CPU SIMD features: ${CPU_DETECTED_STR}")
else()
  message(STATUS "Using compiler-based SIMD detection (explicit tier or cross-compiling)")
endif()

# Determine effective SIMD tier based on AUTO detection or explicit selection
set(SIMD_EFFECTIVE_TIER "SSE2") # Baseline
if(SIMD_TIER STREQUAL "AUTO")
  if(NOT CMAKE_CROSSCOMPILING)
    # Use actual CPU capabilities for AUTO mode
    if(CPU_HAS_AVX512 AND COMPILER_SUPPORTS_AVX512F)
      set(SIMD_EFFECTIVE_TIER "AVX512")
    elseif(CPU_HAS_AVX2 AND COMPILER_SUPPORTS_AVX2)
      set(SIMD_EFFECTIVE_TIER "AVX2")
    elseif(CPU_HAS_AVX AND COMPILER_SUPPORTS_AVX)
      set(SIMD_EFFECTIVE_TIER "AVX")
    elseif(CPU_HAS_SSE42 AND COMPILER_SUPPORTS_SSE42)
      set(SIMD_EFFECTIVE_TIER "SSE4")
    else()
      set(SIMD_EFFECTIVE_TIER "SSE2")
    endif()
  else()
    # Cross-compiling: fall back to conservative SSE2
    set(SIMD_EFFECTIVE_TIER "SSE2")
  endif()
  message(STATUS "AUTO-detected SIMD tier: ${SIMD_EFFECTIVE_TIER}")
else()
  set(SIMD_EFFECTIVE_TIER ${SIMD_TIER})
  message(STATUS "Explicit SIMD tier: ${SIMD_EFFECTIVE_TIER}")
endif()

# Native architecture flag (overrides specific tier when enabled)
if(ENABLE_NATIVE_ARCH)
  check_cxx_compiler_flag("-march=native" COMPILER_SUPPORTS_MARCH_NATIVE)
  if(COMPILER_SUPPORTS_MARCH_NATIVE)
    add_compile_options(-march=native)
    message(STATUS "Native architecture optimization enabled (-march=native)")
    # Native implies best available, skip explicit flags
    set(SIMD_USE_NATIVE ON)
  else()
    set(SIMD_USE_NATIVE OFF)
  endif()
else()
  set(SIMD_USE_NATIVE OFF)
endif()

# Apply SIMD tier flags and definitions
if(NOT SIMD_USE_NATIVE)
  if(SIMD_EFFECTIVE_TIER STREQUAL "AVX512")
    add_compile_options(-mavx512f -mavx512dq -mavx512cd -mavx512bw -mavx512vl)
    add_compile_options(-mavx2 -mfma -mavx -msse4.2 -msse4.1 -mssse3 -msse3 -msse2)
    message(STATUS "Enabling AVX-512 (F+DQ+CD+BW+VL) + all predecessors")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX2")
    add_compile_options(-mavx2 -mfma -mavx -msse4.2 -msse4.1 -mssse3 -msse3 -msse2)
    message(STATUS "Enabling AVX2 + FMA + all SSE variants")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX")
    add_compile_options(-mavx -msse4.2 -msse4.1 -mssse3 -msse3 -msse2)
    message(STATUS "Enabling AVX + all SSE variants")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "SSE4")
    add_compile_options(-msse4.2 -msse4.1 -mssse3 -msse3 -msse2)
    message(STATUS "Enabling SSE4.2 + SSE4.1 + SSSE3 + SSE3 + SSE2")
  else()
    add_compile_options(-msse2)
    message(STATUS "Enabling SSE2 baseline")
  endif()
endif()

# GLM SIMD intrinsics configuration
add_compile_definitions(GLM_FORCE_INTRINSICS)
add_compile_definitions(GLM_FORCE_ALIGNED_GENTYPES)

if(SIMD_EFFECTIVE_TIER STREQUAL "AVX512" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX512))
  add_compile_definitions(GLM_FORCE_AVX512F)
  add_compile_definitions(GLM_FORCE_AVX2)
  add_compile_definitions(GLM_FORCE_AVX)
  add_compile_definitions(GLM_FORCE_SSE42)
  add_compile_definitions(GLM_FORCE_SSE41)
  add_compile_definitions(GLM_FORCE_SSE2)
elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX2" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX2))
  add_compile_definitions(GLM_FORCE_AVX2)
  add_compile_definitions(GLM_FORCE_AVX)
  add_compile_definitions(GLM_FORCE_SSE42)
  add_compile_definitions(GLM_FORCE_SSE41)
  add_compile_definitions(GLM_FORCE_SSE2)
elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX))
  add_compile_definitions(GLM_FORCE_AVX)
  add_compile_definitions(GLM_FORCE_SSE42)
  add_compile_definitions(GLM_FORCE_SSE41)
  add_compile_definitions(GLM_FORCE_SSE2)
elseif(SIMD_EFFECTIVE_TIER STREQUAL "SSE4" OR (SIMD_USE_NATIVE AND CPU_HAS_SSE42))
  add_compile_definitions(GLM_FORCE_SSE42)
  add_compile_definitions(GLM_FORCE_SSE41)
  add_compile_definitions(GLM_FORCE_SSE2)
else()
  add_compile_definitions(GLM_FORCE_SSE2)
endif()

# Eigen-specific SIMD configuration (when ENABLE_EIGEN is ON)
if(ENABLE_EIGEN)
  add_compile_definitions(EIGEN_DONT_VECTORIZE=0)

  if(SIMD_EFFECTIVE_TIER STREQUAL "AVX512" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX512))
    add_compile_definitions(EIGEN_VECTORIZE_AVX512)
    add_compile_definitions(EIGEN_VECTORIZE_AVX2)
    add_compile_definitions(EIGEN_VECTORIZE_FMA)
    add_compile_definitions(EIGEN_VECTORIZE_AVX)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_2)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_1)
    add_compile_definitions(EIGEN_VECTORIZE_SSSE3)
    add_compile_definitions(EIGEN_VECTORIZE_SSE3)
    message(STATUS "Eigen AVX-512 vectorization enabled (full stack)")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX2" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX2))
    add_compile_definitions(EIGEN_VECTORIZE_AVX2)
    add_compile_definitions(EIGEN_VECTORIZE_FMA)
    add_compile_definitions(EIGEN_VECTORIZE_AVX)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_2)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_1)
    add_compile_definitions(EIGEN_VECTORIZE_SSSE3)
    add_compile_definitions(EIGEN_VECTORIZE_SSE3)
    message(STATUS "Eigen AVX2+FMA vectorization enabled")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "AVX" OR (SIMD_USE_NATIVE AND CPU_HAS_AVX))
    add_compile_definitions(EIGEN_VECTORIZE_AVX)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_2)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_1)
    add_compile_definitions(EIGEN_VECTORIZE_SSSE3)
    add_compile_definitions(EIGEN_VECTORIZE_SSE3)
    message(STATUS "Eigen AVX vectorization enabled")
  elseif(SIMD_EFFECTIVE_TIER STREQUAL "SSE4" OR (SIMD_USE_NATIVE AND CPU_HAS_SSE42))
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_2)
    add_compile_definitions(EIGEN_VECTORIZE_SSE4_1)
    add_compile_definitions(EIGEN_VECTORIZE_SSSE3)
    add_compile_definitions(EIGEN_VECTORIZE_SSE3)
    message(STATUS "Eigen SSE4.2 vectorization enabled")
  else()
    message(STATUS "Eigen SSE2 baseline vectorization enabled")
  endif()
endif()

message(STATUS "=== SIMD Configuration Complete ===")

# Fast math for non-critical paths (can be disabled for precision)
option(ENABLE_FAST_MATH "Enable fast math optimizations" ON)
if(ENABLE_FAST_MATH)
  add_compile_options(-ffast-math)
  # Note: infinity/NaN usage is handled via safe_limits.h which uses compiler
  # builtins (__builtin_huge_val) that work correctly with -ffast-math.
  message(STATUS "Fast math optimizations enabled")
endif()

# ============================================================================
# Tiered Warning Flag System (OpenSSF Recommended + C++ Specific)
# ============================================================================
# Set WARNING_LEVEL 1-5 to progressively increase strictness
# Level 1: Core warnings (OpenSSF baseline)
# Level 2: Format string & type safety
# Level 3: C++ specific warnings
# Level 4: Extra strictness (GCC specific)
# Level 5: Maximum (all above + additional)
# ============================================================================

set(WARNING_LEVEL "5" CACHE STRING "Warning strictness level 1-5")
set_property(CACHE WARNING_LEVEL PROPERTY STRINGS "1" "2" "3" "4" "5")
option(ENABLE_WERROR "Treat compiler warnings as errors" ON)

# Level 1: Core warnings (OpenSSF recommended baseline)
set(WARN_LEVEL1
  -Wall
  -Wextra
  -Wpedantic
)

# Level 2: Format string security & type safety
set(WARN_LEVEL2
  ${WARN_LEVEL1}
  -Wformat=2
  -Wformat-security
  -Wshadow
  -Wconversion
  -Wsign-conversion
  -Wfloat-conversion
  -Wnarrowing
  -Wstrict-overflow=2
)
# GCC-specific format warnings (not supported by Clang)
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND WARN_LEVEL2
    -Wformat-overflow=2
    -Wformat-truncation=2
    -Wformat-signedness
  )
endif()

# Level 3: C++ specific warnings
set(WARN_LEVEL3
  ${WARN_LEVEL2}
  -Wnon-virtual-dtor
  -Woverloaded-virtual
  -Wold-style-cast
  -Wcast-align
  -Wcast-qual
  -Wzero-as-null-pointer-constant
  -Wextra-semi
  -Wmissing-declarations
)
# GCC-specific C++ warnings
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND WARN_LEVEL3 -Wuseless-cast)
endif()

# Level 4: Extra strictness
set(WARN_LEVEL4
  ${WARN_LEVEL3}
  -Wdouble-promotion
  -Wnull-dereference
  -Wundef
  -Wunused-macros
)
# GCC-specific level 4 warnings
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND WARN_LEVEL4
    -Wimplicit-fallthrough=5
    -Wduplicated-cond
    -Wduplicated-branches
    -Wlogical-op
    -Wstack-usage=8192
  )
elseif(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  list(APPEND WARN_LEVEL4 -Wimplicit-fallthrough)
endif()

# Level 5: Maximum strictness
set(WARN_LEVEL5
  ${WARN_LEVEL4}
  -Walloca
  -Wvla
  -Wredundant-decls
  # Note: -Winline omitted as it triggers on implicit destructors
)
# GCC-specific level 5 warnings
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  list(APPEND WARN_LEVEL5
    -Warray-bounds=2
    -Wattribute-alias=2
    -Wstringop-overflow=4
    -Wtrampolines
    -Wshift-overflow=2
  )
elseif(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  list(APPEND WARN_LEVEL5
    -Warray-bounds
    -Wshift-overflow
  )
endif()

# Select warning level
if(WARNING_LEVEL STREQUAL "1")
  set(PROJECT_WARNINGS ${WARN_LEVEL1})
elseif(WARNING_LEVEL STREQUAL "2")
  set(PROJECT_WARNINGS ${WARN_LEVEL2})
elseif(WARNING_LEVEL STREQUAL "3")
  set(PROJECT_WARNINGS ${WARN_LEVEL3})
elseif(WARNING_LEVEL STREQUAL "4")
  set(PROJECT_WARNINGS ${WARN_LEVEL4})
else()
  set(PROJECT_WARNINGS ${WARN_LEVEL5})
endif()

message(STATUS "Using warning level ${WARNING_LEVEL}")
if(ENABLE_WERROR)
  list(APPEND PROJECT_WARNINGS -Werror)
  message(STATUS "Warnings are treated as errors")
else()
  message(STATUS "Warnings are not treated as errors")
endif()

# ============================================================================
# Runtime Hardening Flags
# ============================================================================

option(ENABLE_HARDENING "Enable runtime hardening flags" ON)
if(ENABLE_HARDENING)
  add_compile_definitions(_FORTIFY_SOURCE=3)
  add_compile_options(-fstack-protector-strong)
  add_compile_options(-fstack-clash-protection)
  add_compile_options(-fcf-protection)
  message(STATUS "Runtime hardening enabled")
endif()

# ============================================================================
# Sanitizer Support (Debug builds)
# ============================================================================

option(ENABLE_ASAN "Enable AddressSanitizer" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer" OFF)
option(ENABLE_TSAN "Enable ThreadSanitizer" OFF)

if(ENABLE_ASAN)
  add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
  add_link_options(-fsanitize=address)
  message(STATUS "AddressSanitizer enabled")
endif()

if(ENABLE_UBSAN)
  add_compile_options(-fsanitize=undefined -fno-omit-frame-pointer)
  add_link_options(-fsanitize=undefined)
  message(STATUS "UndefinedBehaviorSanitizer enabled")
endif()

if(ENABLE_TSAN)
  add_compile_options(-fsanitize=thread -fno-omit-frame-pointer)
  add_link_options(-fsanitize=thread)
  message(STATUS "ThreadSanitizer enabled")
endif()

# ============================================================================
# Profiling/Instrumentation Flags
# ============================================================================

option(ENABLE_PROFILING "Enable profiling-friendly flags" OFF)
option(ENABLE_GPROF "Enable gprof instrumentation (-pg)" OFF)

if(ENABLE_PROFILING)
  add_compile_options(-fno-omit-frame-pointer -fno-optimize-sibling-calls)
  add_link_options(-fno-omit-frame-pointer)
  if(NOT CMAKE_BUILD_TYPE STREQUAL "Debug")
    add_compile_options(-g)
  endif()
  message(STATUS "Profiling-friendly flags enabled")
endif()

if(ENABLE_GPROF)
  add_compile_options(-pg)
  add_link_options(-pg)
  message(STATUS "gprof instrumentation enabled")
endif()

# ============================================================================
# Coverage Instrumentation
# ============================================================================

option(ENABLE_COVERAGE "Enable coverage instrumentation" OFF)

if(ENABLE_COVERAGE)
  if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
    add_link_options(-fprofile-instr-generate -fcoverage-mapping)
  elseif(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    add_compile_options(--coverage -fprofile-arcs -ftest-coverage)
    add_link_options(--coverage)
  else()
    message(WARNING "Coverage instrumentation not supported for this compiler")
  endif()
  message(STATUS "Coverage instrumentation enabled")
endif()

# ============================================================================
# Linker Hardening
# ============================================================================

option(ENABLE_LINKER_HARDENING "Enable linker hardening" ON)
if(ENABLE_LINKER_HARDENING)
  add_link_options(-Wl,-z,relro,-z,now)
  add_link_options(-Wl,-z,noexecstack)
  if(NOT APPLE)
    add_compile_options(-fPIE)
    add_link_options(-pie)
  endif()
  message(STATUS "Linker hardening enabled (RELRO, PIE)")
endif()

# ============================================================================
# OpenGL Debug Context (Debug builds)
# ============================================================================

option(ENABLE_GL_DEBUG "Enable OpenGL debug context" ON)
if(ENABLE_GL_DEBUG)
  add_compile_definitions(ENABLE_GL_DEBUG_CONTEXT)
  message(STATUS "OpenGL debug context enabled")
endif()

# ============================================================================
# Source Files
# ============================================================================

# Physics library source files (pure physics, no OpenGL dependencies)
set(PHYSICS_SRC_FILES
  "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/geodesics.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/cosmology.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/kerr.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/noise.cpp"
)

# Separate project source files from third-party imgui implementation
set(PROJECT_SRC_FILES
  "${PROJECT_SOURCE_DIR}/src/main.cpp"
  "${PROJECT_SOURCE_DIR}/src/hud_overlay.cpp"
  "${PROJECT_SOURCE_DIR}/src/rmlui_overlay.cpp"
  "${PROJECT_SOURCE_DIR}/src/overlay.cpp"
  "${PROJECT_SOURCE_DIR}/src/render.cpp"
  "${PROJECT_SOURCE_DIR}/src/render/noise_generator.cpp"
  "${PROJECT_SOURCE_DIR}/src/render/noise_texture_cache.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader_manager.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader_watcher.cpp"
  "${PROJECT_SOURCE_DIR}/src/texture.cpp"
  "${PROJECT_SOURCE_DIR}/src/grmhd_packed_loader.cpp"
  "${PROJECT_SOURCE_DIR}/src/stb_image.cpp"
  "${PROJECT_SOURCE_DIR}/src/input.cpp"
  "${PROJECT_SOURCE_DIR}/src/settings.cpp"
  "${PROJECT_SOURCE_DIR}/src/GLDebugMessageCallback.cc"
  "${PROJECT_SOURCE_DIR}/src/physics/hawking_renderer.cpp"  # OpenGL-dependent physics renderer
  ${PHYSICS_SRC_FILES}
)

set(THIRDPARTY_SRC_FILES
  "${PROJECT_SOURCE_DIR}/src/imgui_impl_glfw.cpp"
  "${PROJECT_SOURCE_DIR}/src/imgui_impl_opengl3.cpp"
)

# Collect all header files including physics and render subdirectories
file(GLOB HEADER_FILES "${PROJECT_SOURCE_DIR}/src/*.h" "${PROJECT_SOURCE_DIR}/src/*.hpp")
file(GLOB PHYSICS_HEADER_FILES "${PROJECT_SOURCE_DIR}/src/physics/*.h")
file(GLOB RENDER_HEADER_FILES "${PROJECT_SOURCE_DIR}/src/render/*.h")
list(APPEND HEADER_FILES ${PHYSICS_HEADER_FILES} ${RENDER_HEADER_FILES})

add_executable(${CMAKE_PROJECT_NAME} ${PROJECT_SRC_FILES} ${THIRDPARTY_SRC_FILES} ${HEADER_FILES})

set_target_properties(${CMAKE_PROJECT_NAME} PROPERTIES
  CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)

# Apply tiered warning flags only to project source files
set_source_files_properties(${PROJECT_SRC_FILES} PROPERTIES
  COMPILE_OPTIONS "${PROJECT_WARNINGS}"
)

# Sanitizers and heavy inlining can push stack usage estimates beyond the strict global threshold.
# Keep -Wstack-usage enabled for most of the codebase, but avoid failing the build on main.cpp.
# Note: -Wstack-usage is GCC-only
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  set_source_files_properties("${PROJECT_SOURCE_DIR}/src/main.cpp" PROPERTIES
    COMPILE_OPTIONS "-Wno-stack-usage"
  )
endif()

# Third-party files get relaxed warnings
set_source_files_properties(${THIRDPARTY_SRC_FILES} PROPERTIES
  COMPILE_OPTIONS "-w"
)

target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE imgui::imgui)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE imguizmo::imguizmo)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE implot::implot)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE glfw)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE glbinding::glbinding)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE glm::glm)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE nlohmann_json::nlohmann_json)
target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE stb::stb)
find_library(CPPTRACE_LIBRARY cpptrace)
if(CPPTRACE_LIBRARY)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE ${CPPTRACE_LIBRARY})
  target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE BLACKHOLE_HAS_CPPTRACE=1)
else()
  target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE BLACKHOLE_HAS_CPPTRACE=0)
endif()
if(ENABLE_RMLUI)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE rmlui::rmlui)
endif()
if(ENABLE_TRACY)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE Tracy::TracyClient)
endif()
if(ENABLE_SHADER_WATCHER)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE watcher::watcher)
endif()
if(ENABLE_FASTNOISE2)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE FastNoise2::FastNoise)
endif()
if(ENABLE_MESHOPTIMIZER)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE meshoptimizer::meshoptimizer)
endif()
if(ENABLE_TASKFLOW)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE Taskflow::Taskflow)
endif()
if(ENABLE_XSIMD)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE xsimd)
endif()
if(ENABLE_HIGHWAY)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE hwy::hwy)
endif()
if(ENABLE_SLEEF)
  target_link_libraries(${CMAKE_PROJECT_NAME} PRIVATE sleef::sleef)
endif()

target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE
  GLFW_INCLUDE_NONE
  IMGUI_IMPL_OPENGL_LOADER_CUSTOM
  BLACKHOLE_ENABLE_RMLUI=$<BOOL:${ENABLE_RMLUI}>
  BLACKHOLE_ENABLE_MESHOPTIMIZER=$<BOOL:${ENABLE_MESHOPTIMIZER}>
  BLACKHOLE_ENABLE_TASKFLOW=$<BOOL:${ENABLE_TASKFLOW}>
  BLACKHOLE_ENABLE_XSIMD=$<BOOL:${ENABLE_XSIMD}>
  BLACKHOLE_ENABLE_HIGHWAY=$<BOOL:${ENABLE_HIGHWAY}>
  BLACKHOLE_ENABLE_SLEEF=$<BOOL:${ENABLE_SLEEF}>
)
if(ENABLE_TRACY)
  target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE TRACY_ENABLE)
endif()

# Include directories for physics library
target_include_directories(${CMAKE_PROJECT_NAME} PRIVATE
  "${PROJECT_SOURCE_DIR}/src"
  "${PROJECT_SOURCE_DIR}/src/physics"
)

# ============================================================================
# Benchmarks
# ============================================================================

add_executable(physics_bench
  "${PROJECT_SOURCE_DIR}/bench/physics_bench.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/kerr.cpp"
  "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
)

set_target_properties(physics_bench PROPERTIES
  CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)

target_include_directories(physics_bench PRIVATE
  "${PROJECT_SOURCE_DIR}/src"
  "${PROJECT_SOURCE_DIR}/src/physics"
)

target_compile_options(physics_bench PRIVATE ${PROJECT_WARNINGS})
target_compile_definitions(physics_bench PRIVATE
  GLFW_INCLUDE_NONE
  IMGUI_IMPL_OPENGL_LOADER_CUSTOM
  BLACKHOLE_ENABLE_XSIMD=$<BOOL:${ENABLE_XSIMD}>
  BLACKHOLE_ENABLE_HIGHWAY=$<BOOL:${ENABLE_HIGHWAY}>
  BLACKHOLE_ENABLE_SLEEF=$<BOOL:${ENABLE_SLEEF}>
)
target_link_libraries(physics_bench PRIVATE glfw glbinding::glbinding glm::glm)
if(ENABLE_XSIMD)
  target_link_libraries(physics_bench PRIVATE xsimd)
endif()
if(ENABLE_HIGHWAY)
  target_link_libraries(physics_bench PRIVATE hwy::hwy)
endif()
if(ENABLE_SLEEF)
  target_link_libraries(physics_bench PRIVATE sleef::sleef)
endif()

# Copy assets files after build.
add_custom_command(
  TARGET ${CMAKE_PROJECT_NAME}
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy_directory "${PROJECT_SOURCE_DIR}/assets"
          "$<TARGET_FILE_DIR:${CMAKE_PROJECT_NAME}>/assets")

add_custom_command(
  TARGET ${CMAKE_PROJECT_NAME}
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy_directory "${PROJECT_SOURCE_DIR}/shader/"
          "$<TARGET_FILE_DIR:${CMAKE_PROJECT_NAME}>/shader")

# ============================================================================
# Tools
# ============================================================================

add_executable(nubhlight_inspect
  "${PROJECT_SOURCE_DIR}/tools/nubhlight_inspect.cpp"
)

set_target_properties(nubhlight_inspect PROPERTIES
  CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)

target_link_libraries(nubhlight_inspect PRIVATE HighFive::HighFive CLI11::CLI11)
target_compile_options(nubhlight_inspect PRIVATE ${PROJECT_WARNINGS})
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  target_compile_options(nubhlight_inspect PRIVATE -Wno-stack-usage)
endif()

add_executable(nubhlight_pack
  "${PROJECT_SOURCE_DIR}/tools/nubhlight_pack.cpp"
)

set_target_properties(nubhlight_pack PROPERTIES
  CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)

target_link_libraries(nubhlight_pack PRIVATE HighFive::HighFive CLI11::CLI11)
target_compile_options(nubhlight_pack PRIVATE ${PROJECT_WARNINGS})
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  target_compile_options(nubhlight_pack PRIVATE -Wno-stack-usage)
endif()

if(ENABLE_Z3)
  add_executable(z3_sanity
    "${PROJECT_SOURCE_DIR}/tools/z3_sanity.cpp"
  )

  set_target_properties(z3_sanity PROPERTIES
    CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
    CXX_STANDARD_REQUIRED ON
    CXX_EXTENSIONS OFF
  )

  target_link_libraries(z3_sanity PRIVATE ${Z3_TARGET})
  target_compile_options(z3_sanity PRIVATE ${PROJECT_WARNINGS})
endif()

# ============================================================================
# Static Analysis Tools Integration
# ============================================================================

option(ENABLE_CLANG_TIDY "Enable clang-tidy static analysis" OFF)
option(ENABLE_CPPCHECK "Enable cppcheck static analysis" OFF)
option(ENABLE_IWYU "Enable include-what-you-use" OFF)
option(ENABLE_GCC_ANALYZER "Enable GCC -fanalyzer" OFF)

# --------------------------------------------------------------------------
# clang-tidy Integration
# --------------------------------------------------------------------------
if(ENABLE_CLANG_TIDY)
  find_program(CLANG_TIDY_EXE NAMES "clang-tidy" "clang-tidy-17" "clang-tidy-16" "clang-tidy-15")
  if(CLANG_TIDY_EXE)
    message(STATUS "clang-tidy found: ${CLANG_TIDY_EXE}")
    set(CLANG_TIDY_EXTRA_ARGS
      "--extra-arg=-Wno-unknown-warning-option"
      "--extra-arg=-Wno-unknown-argument"
      "--extra-arg=-Wno-error=unknown-warning-option"
      "--extra-arg=-Wno-error=unknown-argument"
    )
    # Use .clang-tidy config file if present, otherwise use inline checks
    if(EXISTS "${PROJECT_SOURCE_DIR}/.clang-tidy")
      set(CMAKE_CXX_CLANG_TIDY "${CLANG_TIDY_EXE}" ${CLANG_TIDY_EXTRA_ARGS})
    else()
      set(CMAKE_CXX_CLANG_TIDY
        "${CLANG_TIDY_EXE}"
        ${CLANG_TIDY_EXTRA_ARGS}
        "-checks=bugprone-*,cert-*,clang-analyzer-*,cppcoreguidelines-*,misc-*,modernize-*,performance-*,portability-*,readability-*,-modernize-use-trailing-return-type,-readability-magic-numbers,-cppcoreguidelines-avoid-magic-numbers"
        "-header-filter=${PROJECT_SOURCE_DIR}/src/.*"
        "-warnings-as-errors=bugprone-*,cert-*"
      )
    endif()
  else()
    message(WARNING "clang-tidy requested but not found")
  endif()
endif()

# --------------------------------------------------------------------------
# cppcheck Integration
# --------------------------------------------------------------------------
if(ENABLE_CPPCHECK)
  find_program(CPPCHECK_EXE NAMES "cppcheck")
  if(CPPCHECK_EXE)
    message(STATUS "cppcheck found: ${CPPCHECK_EXE}")
    set(CMAKE_CXX_CPPCHECK
      "${CPPCHECK_EXE}"
      "--enable=warning,style,performance,portability"
      "--std=c++${BLACKHOLE_CXX_STANDARD}"
      "--suppress=missingInclude"
      "--suppress=unmatchedSuppression"
      "--suppress=unusedFunction"
      "--inline-suppr"
      "--quiet"
      "-I${PROJECT_SOURCE_DIR}/src"
      "-I${PROJECT_SOURCE_DIR}/src/physics"
    )
  else()
    message(WARNING "cppcheck requested but not found")
  endif()
endif()

# --------------------------------------------------------------------------
# include-what-you-use Integration
# --------------------------------------------------------------------------
if(ENABLE_IWYU)
  find_program(IWYU_EXE NAMES "include-what-you-use" "iwyu")
  if(IWYU_EXE)
    message(STATUS "include-what-you-use found: ${IWYU_EXE}")
    set(IWYU_EXTRA_ARGS
      "-Wno-unknown-warning-option"
      "-Wno-unknown-argument"
      "-Wno-error=unknown-warning-option"
      "-Wno-error=unknown-argument"
    )
    set(CMAKE_CXX_INCLUDE_WHAT_YOU_USE
      "${IWYU_EXE}"
      ${IWYU_EXTRA_ARGS}
      "-Xiwyu" "--transitive_includes_only"
      "-Xiwyu" "--no_fwd_decls"
    )
  else()
    message(WARNING "include-what-you-use requested but not found")
  endif()
endif()

# --------------------------------------------------------------------------
# GCC -fanalyzer Integration
# --------------------------------------------------------------------------
if(ENABLE_GCC_ANALYZER)
  if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_GREATER_EQUAL "10")
    message(STATUS "GCC analyzer enabled")
    add_compile_options(
      -fanalyzer
      -Wanalyzer-double-free
      -Wanalyzer-null-dereference
      -Wanalyzer-use-after-free
      -Wanalyzer-malloc-leak
    )
  else()
    message(WARNING "GCC analyzer requires GCC 10+")
  endif()
endif()

# ============================================================================
# GLSL Shader Validation Target
# ============================================================================

option(ENABLE_SHADER_VALIDATION "Enable GLSL shader validation" ON)

if(ENABLE_SHADER_VALIDATION)
  find_program(GLSLANG_VALIDATOR NAMES "glslangValidator" "glslang")
  find_program(GLSLC NAMES "glslc")

  if(GLSLANG_VALIDATOR)
    message(STATUS "glslangValidator found: ${GLSLANG_VALIDATOR}")

    # Collect all shader files
    file(GLOB_RECURSE FRAG_SHADERS "${PROJECT_SOURCE_DIR}/shader/*.frag")
    file(GLOB_RECURSE VERT_SHADERS "${PROJECT_SOURCE_DIR}/shader/*.vert")
    file(GLOB_RECURSE COMP_SHADERS "${PROJECT_SOURCE_DIR}/shader/*.comp")

    set(ALL_SHADERS ${FRAG_SHADERS} ${VERT_SHADERS} ${COMP_SHADERS})

    # Create validation commands for each shader
    # Use OpenGL mode (-G) instead of Vulkan (-V) since our shaders are OpenGL
    set(SHADER_VALIDATION_COMMANDS)
    foreach(shader ${ALL_SHADERS})
      get_filename_component(shader_name ${shader} NAME)
      get_filename_component(shader_ext ${shader} LAST_EXT)

      # Determine shader stage from extension
      if(shader_ext STREQUAL ".vert")
        set(SHADER_STAGE "vert")
      elseif(shader_ext STREQUAL ".frag")
        set(SHADER_STAGE "frag")
      elseif(shader_ext STREQUAL ".comp")
        set(SHADER_STAGE "comp")
      else()
        continue()
      endif()

      list(APPEND SHADER_VALIDATION_COMMANDS
        COMMAND ${CMAKE_COMMAND}
          -DGLSLANG_VALIDATOR:FILEPATH=${GLSLANG_VALIDATOR}
          -DSHADER:FILEPATH=${shader}
          -DSTAGE=${SHADER_STAGE}
          -DGLSL_VERSION=460
          -DWARN_AS_ERROR:BOOL=${ENABLE_WERROR}
          -DINCLUDE_DIR:PATH=${PROJECT_SOURCE_DIR}/shader/include
          -P ${PROJECT_SOURCE_DIR}/cmake/ValidateShader.cmake
      )
    endforeach()

    # Custom target to validate all shaders
    add_custom_target(validate-shaders
      ${SHADER_VALIDATION_COMMANDS}
      COMMENT "Validating GLSL shaders with glslangValidator"
      VERBATIM
    )

    # SPIR-V compilation removed in Phase 3 (pure GLSL 4.60 pipeline)
    # For optional SPIR-V compilation via glslc, use: glslc -c shader.frag -o out.spv
  else()
    message(STATUS "glslangValidator not found - shader validation disabled")
  endif()
endif()

# ============================================================================
# Static Analysis Aggregate Target
# ============================================================================

# Create a target that runs all enabled analysis tools
add_custom_target(analyze
  COMMENT "Running static analysis tools"
)

# Performance pack: GPU timing + flamegraph + analysis reports
add_custom_target(perf-pack
  COMMAND ${CMAKE_COMMAND} -E echo "Collecting performance pack (5s run)..."
  COMMAND ${PROJECT_SOURCE_DIR}/scripts/collect_perf_pack.sh 5
  DEPENDS Blackhole
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
  COMMENT "Collecting GPU timing, flamegraph, and analysis reports"
  VERBATIM
)

# GPU timing analysis only (no app run)
add_custom_target(analyze-gpu-timing
  COMMAND ${CMAKE_COMMAND} -E echo "Analyzing GPU timing data..."
  COMMAND python3 ${PROJECT_SOURCE_DIR}/scripts/analyze_gpu_timing.py
    ${PROJECT_SOURCE_DIR}/logs/perf/gpu_timing.csv
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
  COMMENT "Analyzing GPU timing CSV with outlier detection"
  VERBATIM
)

# cppcheck standalone target
if(CPPCHECK_EXE)
  add_custom_target(cppcheck
    COMMAND ${CPPCHECK_EXE}
      --enable=all
      --std=c++${BLACKHOLE_CXX_STANDARD}
      --suppress=missingInclude
      --suppress=unmatchedSuppression
      --error-exitcode=1
      -I${PROJECT_SOURCE_DIR}/src
      -I${PROJECT_SOURCE_DIR}/src/physics
      ${PROJECT_SOURCE_DIR}/src
    COMMENT "Running cppcheck analysis"
    VERBATIM
  )
  add_dependencies(analyze cppcheck)
endif()

# clang-tidy standalone target (for full project scan)
if(CLANG_TIDY_EXE)
  add_custom_target(clang-tidy-check
    COMMAND ${CLANG_TIDY_EXE}
      -p ${CMAKE_BINARY_DIR}
      ${PROJECT_SRC_FILES}
    COMMENT "Running clang-tidy analysis"
    VERBATIM
  )
endif()

# ============================================================================
# Coverage Report Target
# ============================================================================

if(ENABLE_COVERAGE)
  find_program(GCOVR_EXE NAMES "gcovr")
  if(GCOVR_EXE)
    set(COVERAGE_OUTPUT_DIR "${CMAKE_BINARY_DIR}/coverage")
    add_custom_target(coverage-report
      COMMAND ${CMAKE_COMMAND} -E make_directory ${COVERAGE_OUTPUT_DIR}
      COMMAND ${GCOVR_EXE}
        --root ${PROJECT_SOURCE_DIR}
        --filter ${PROJECT_SOURCE_DIR}/src
        --exclude ${PROJECT_SOURCE_DIR}/external
        --exclude ${PROJECT_SOURCE_DIR}/bench
        --exclude ${PROJECT_SOURCE_DIR}/tests
        --html
        --html-details
        -o ${COVERAGE_OUTPUT_DIR}/coverage.html
      WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
      COMMENT "Generating coverage report with gcovr"
      VERBATIM
    )
  else()
    message(STATUS "gcovr not found - coverage-report target disabled")
  endif()
endif()

# ============================================================================
# GLSL Shader Generation from C++23 Verified Kernels (Phase 9.0.1)
# ============================================================================
# Pipeline: verified C++23 headers -> GLSL 4.60 shaders via transpiler
# Supports Lovelace (SM_89) consumer GPU optimization

find_program(PYTHON3_EXECUTABLE python3)

if(PYTHON3_EXECUTABLE)
  set(GLSL_SOURCE_DIR "${PROJECT_SOURCE_DIR}/src/physics/verified")
  set(GLSL_OUTPUT_DIR "${PROJECT_SOURCE_DIR}/shader/include/verified")

  # Custom target to generate GLSL shaders from C++23 headers
  add_custom_target(generate_glsl
    COMMAND ${PYTHON3_EXECUTABLE} "${PROJECT_SOURCE_DIR}/scripts/cpp_to_glsl.py"
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    COMMENT "Generating GLSL 4.60 shaders from verified C++23 kernels"
    VERBATIM
  )

  # Find all generated GLSL files
  file(GLOB GENERATED_GLSL_FILES "${GLSL_OUTPUT_DIR}/*.glsl")

  message(STATUS "GLSL shader generation configured")
  message(STATUS "  Source: ${GLSL_SOURCE_DIR}")
  message(STATUS "  Output: ${GLSL_OUTPUT_DIR}")
  if(GENERATED_GLSL_FILES)
    list(LENGTH GENERATED_GLSL_FILES GLSL_COUNT)
    message(STATUS "  Generated shaders: ${GLSL_COUNT} files")
  endif()
else()
  message(STATUS "python3 not found - GLSL shader generation disabled")
endif()

# ============================================================================
# Testing Support (CTest)
# ============================================================================

option(BUILD_TESTING "Build test targets" ON)
option(ENABLE_PRECISION_TESTS "Enable multiprecision regression tests" OFF)

if(BUILD_TESTING)
  enable_testing()
  set(SANITIZER_TEST_ENV "")
  if(ENABLE_ASAN OR ENABLE_UBSAN OR ENABLE_TSAN)
    list(APPEND SANITIZER_TEST_ENV "LD_PRELOAD=")
  endif()
  if(ENABLE_ASAN)
    list(APPEND SANITIZER_TEST_ENV "ASAN_OPTIONS=detect_leaks=0")
    list(APPEND SANITIZER_TEST_ENV "LSAN_OPTIONS=detect_leaks=0")
  endif()

  # Physics library validation tests
  if(EXISTS "${PROJECT_SOURCE_DIR}/src/physics/physics_test.cpp")
    add_executable(physics_test
      "${PROJECT_SOURCE_DIR}/src/physics/physics_test.cpp"
      ${PHYSICS_SRC_FILES}
    )
    target_include_directories(physics_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    set_target_properties(physics_test PROPERTIES
      CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
      CXX_STANDARD_REQUIRED ON
      CXX_EXTENSIONS OFF
	    )
	    # Apply project warnings to test sources
	    target_compile_options(physics_test PRIVATE ${PROJECT_WARNINGS})
	    # physics_test has a large, table-driven runner that can exceed the global
	    # stack-usage threshold when warnings are promoted to errors.
	    if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	      target_compile_options(physics_test PRIVATE -Wno-stack-usage)
	    endif()
	    if(ENABLE_FAST_MATH)
	      target_compile_options(physics_test PRIVATE -fno-fast-math)
	    endif()

	    # Link SIMD libraries to physics_test
	    if(ENABLE_XSIMD)
	      target_link_libraries(physics_test PRIVATE xsimd)
	    endif()
	    if(ENABLE_SLEEF)
	      target_link_libraries(physics_test PRIVATE sleef::sleef)
	    endif()
	    if(ENABLE_HIGHWAY)
	      target_link_libraries(physics_test PRIVATE hwy::hwy)
	    endif()

    # Register with CTest
    add_test(NAME physics_validation COMMAND physics_test)
    set_tests_properties(physics_validation PROPERTIES
      LABELS "physics;unit"
      TIMEOUT 60
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(physics_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/grmhd_pack_test.cpp")
    add_executable(grmhd_pack_test
      "${PROJECT_SOURCE_DIR}/tests/grmhd_pack_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/grmhd_packed_loader.cpp"
      "${PROJECT_SOURCE_DIR}/src/render.cpp"
      "${PROJECT_SOURCE_DIR}/src/shader.cpp"
    )
    add_dependencies(grmhd_pack_test nubhlight_pack)
    target_include_directories(grmhd_pack_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(grmhd_pack_test PRIVATE ${PROJECT_WARNINGS})
    target_compile_definitions(grmhd_pack_test PRIVATE
      GLFW_INCLUDE_NONE
      IMGUI_IMPL_OPENGL_LOADER_CUSTOM
    )
    if(ENABLE_FAST_MATH)
      target_compile_options(grmhd_pack_test PRIVATE -fno-fast-math)
    endif()
    target_link_libraries(grmhd_pack_test PRIVATE
      HighFive::HighFive
      nlohmann_json::nlohmann_json
      glfw
      glbinding::glbinding
      glm::glm
    )

    add_test(NAME grmhd_pack_fixture COMMAND grmhd_pack_test)
    set_tests_properties(grmhd_pack_fixture PROPERTIES
      LABELS "grmhd;io"
      TIMEOUT 60
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(grmhd_pack_fixture PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # HUD overlay compile-only test
  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/hud_overlay_compile_test.cpp")
    add_executable(hud_overlay_compile_test
      "${PROJECT_SOURCE_DIR}/tests/hud_overlay_compile_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/hud_overlay.cpp"
      "${PROJECT_SOURCE_DIR}/src/shader.cpp"
    )
    target_include_directories(hud_overlay_compile_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
    )
    target_compile_options(hud_overlay_compile_test PRIVATE ${PROJECT_WARNINGS})
    target_compile_definitions(hud_overlay_compile_test PRIVATE GLM_FORCE_PURE)
    target_link_libraries(hud_overlay_compile_test PRIVATE glbinding::glbinding stb::stb)
    add_test(NAME hud_overlay_compile COMMAND hud_overlay_compile_test)
    set_tests_properties(hud_overlay_compile PROPERTIES
      LABELS "hud;compile"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(hud_overlay_compile PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # Math types compile-only test
  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/math_types_compile_test.cpp")
    add_executable(math_types_compile_test
      "${PROJECT_SOURCE_DIR}/tests/math_types_compile_test.cpp"
    )
    target_include_directories(math_types_compile_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(math_types_compile_test PRIVATE ${PROJECT_WARNINGS})
    target_compile_definitions(math_types_compile_test PRIVATE GLM_FORCE_PURE)
    add_test(NAME math_types_compile COMMAND math_types_compile_test)
    set_tests_properties(math_types_compile PROPERTIES
      LABELS "math;compile"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(math_types_compile PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # Math types parity test (round-trip Eigen <-> GLM)
  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/math_types_parity_test.cpp")
    add_executable(math_types_parity_test
      "${PROJECT_SOURCE_DIR}/tests/math_types_parity_test.cpp"
    )
    target_include_directories(math_types_parity_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(math_types_parity_test PRIVATE ${PROJECT_WARNINGS})
    target_compile_definitions(math_types_parity_test PRIVATE GLM_FORCE_PURE)
    target_link_libraries(math_types_parity_test PRIVATE glm::glm)
    if(ENABLE_EIGEN)
      find_package(Eigen3 CONFIG REQUIRED)
      target_link_libraries(math_types_parity_test PRIVATE Eigen3::Eigen)
    endif()
    add_test(NAME math_types_parity COMMAND math_types_parity_test)
    set_tests_properties(math_types_parity PROPERTIES
      LABELS "math;parity"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(math_types_parity PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # Coordinate transformation validation tests (Phase 1.4.5)
  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/coordinates_test.cpp")
    add_executable(coordinates_test
      "${PROJECT_SOURCE_DIR}/tests/coordinates_test.cpp"
    )
    target_include_directories(coordinates_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(coordinates_test PRIVATE ${PROJECT_WARNINGS})
    add_test(NAME coordinates_validation COMMAND coordinates_test)
    set_tests_properties(coordinates_validation PROPERTIES
      LABELS "physics;coordinates"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(coordinates_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # Connection coefficient validation tests (Phase 1.4.6)
  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/connection_test.cpp")
    add_executable(connection_test
      "${PROJECT_SOURCE_DIR}/tests/connection_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
    )
    target_include_directories(connection_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(connection_test PRIVATE ${PROJECT_WARNINGS})
    add_test(NAME connection_validation COMMAND connection_test)
    set_tests_properties(connection_validation PROPERTIES
      LABELS "physics;connection"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(connection_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # ========================================================================
  # Phase 8.3: Horizon Dynamics Verification Tests
  # ========================================================================

  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/horizon_dynamics_test.cpp")
    add_executable(horizon_dynamics_test
      "${PROJECT_SOURCE_DIR}/tests/horizon_dynamics_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
    )
    target_include_directories(horizon_dynamics_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(horizon_dynamics_test PRIVATE ${PROJECT_WARNINGS})
    add_test(NAME horizon_dynamics_validation COMMAND horizon_dynamics_test)
    set_tests_properties(horizon_dynamics_validation PROPERTIES
      LABELS "physics;horizon;kerr"
      TIMEOUT 15
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(horizon_dynamics_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # ========================================================================
  # Phase 10.1: Hawking Radiation Tests
  # ========================================================================

  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/hawking_glow_test.cpp")
    add_executable(hawking_glow_test
      "${PROJECT_SOURCE_DIR}/tests/hawking_glow_test.cpp"
    )
    target_include_directories(hawking_glow_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(hawking_glow_test PRIVATE ${PROJECT_WARNINGS})
    if(ENABLE_FAST_MATH)
      target_compile_options(hawking_glow_test PRIVATE -fno-fast-math)
    endif()
    add_test(NAME hawking_glow_validation COMMAND hawking_glow_test)
    set_tests_properties(hawking_glow_validation PROPERTIES
      LABELS "physics;hawking;phase10"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(hawking_glow_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  if(EXISTS "${PROJECT_SOURCE_DIR}/tests/hawking_spectrum_test.cpp")
    add_executable(hawking_spectrum_test
      "${PROJECT_SOURCE_DIR}/tests/hawking_spectrum_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
    )
    target_include_directories(hawking_spectrum_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(hawking_spectrum_test PRIVATE ${PROJECT_WARNINGS})
    if(ENABLE_FAST_MATH)
      target_compile_options(hawking_spectrum_test PRIVATE -fno-fast-math)
    endif()
    add_test(NAME hawking_spectrum_validation COMMAND hawking_spectrum_test)
    set_tests_properties(hawking_spectrum_validation PROPERTIES
      LABELS "physics;hawking;spectrum;phase10"
      TIMEOUT 10
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(hawking_spectrum_validation PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # FastNoise2 integration test
  if(ENABLE_FASTNOISE2)
    add_executable(noise_generator_test
      "${PROJECT_SOURCE_DIR}/tests/noise_generator_test.cpp"
      "${PROJECT_SOURCE_DIR}/src/render/noise_generator.cpp"
    )
    target_include_directories(noise_generator_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
    )
    target_compile_options(noise_generator_test PRIVATE ${PROJECT_WARNINGS})
    target_link_libraries(noise_generator_test PRIVATE FastNoise2::FastNoise)
    add_test(NAME noise_generator_validation COMMAND noise_generator_test)
    set_tests_properties(noise_generator_validation PROPERTIES
      LABELS "render;noise;procedural;phase3"
      TIMEOUT 30
    )

    # FastNoise2 mathematical audit (deep verification)
    add_executable(noise_math_audit
      "${PROJECT_SOURCE_DIR}/tests/noise_math_audit.cpp"
      "${PROJECT_SOURCE_DIR}/src/render/noise_generator.cpp"
    )
    target_include_directories(noise_math_audit PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
    )
    target_compile_options(noise_math_audit PRIVATE ${PROJECT_WARNINGS})
    target_link_libraries(noise_math_audit PRIVATE FastNoise2::FastNoise)
  endif()

  # ========================================================================
  # Phase 4: Z3 SMT Solver Constraint Verification (Formal Verification)
  # ========================================================================

  # Z3 verification test - coupled GPU/Z3 constraint verification
  option(ENABLE_Z3_VERIFICATION "Enable Z3 constraint verification tests (Phase 4)" ON)

  if(ENABLE_Z3_VERIFICATION AND EXISTS "${PROJECT_SOURCE_DIR}/tests/z3_verification_test.cpp")
    # Find Z3 library (optional for build, required for runtime)
    find_package(Z3 CONFIG QUIET)

    # Establish Z3 target if found
    if(Z3_FOUND)
      if(TARGET z3::libz3)
        set(Z3_VERIFICATION_TARGET z3::libz3)
      elseif(TARGET z3::z3)
        set(Z3_VERIFICATION_TARGET z3::z3)
      elseif(TARGET Z3::Z3)
        set(Z3_VERIFICATION_TARGET Z3::Z3)
      elseif(TARGET Z3::libz3)
        set(Z3_VERIFICATION_TARGET Z3::libz3)
      else()
        message(WARNING "Z3 found but target not identified. Z3 features will be disabled.")
        set(Z3_FOUND FALSE)
      endif()
    endif()

    add_executable(z3_verification_test
      "${PROJECT_SOURCE_DIR}/tests/z3_verification_test.cpp"
      ${PHYSICS_SRC_FILES}
    )

    # Z3 verification requires OpenGL 4.6 and GLFW
    target_include_directories(z3_verification_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )

    target_compile_definitions(z3_verification_test PRIVATE
      GLFW_INCLUDE_NONE
      IMGUI_IMPL_OPENGL_LOADER_CUSTOM
    )

    target_compile_options(z3_verification_test PRIVATE ${PROJECT_WARNINGS})

    if(ENABLE_FAST_MATH)
      target_compile_options(z3_verification_test PRIVATE -fno-fast-math)
    endif()

    target_link_libraries(z3_verification_test PRIVATE
      glfw
      glbinding::glbinding
      glm::glm
    )

    # Optional Z3 linking if available
    if(Z3_FOUND)
      target_link_libraries(z3_verification_test PRIVATE ${Z3_VERIFICATION_TARGET})
      target_compile_definitions(z3_verification_test PRIVATE BLACKHOLE_Z3_AVAILABLE=1)
      message(STATUS "Z3 library found: Z3 constraint proofs enabled")
    else()
      message(STATUS "Z3 not found: Z3 constraint proofs will be skipped (fallback to numerical verification)")
    endif()

    # Register with CTest
    add_test(NAME z3_verification COMMAND z3_verification_test)
    set_tests_properties(z3_verification PROPERTIES
      LABELS "phase4;verification;gpu"
      TIMEOUT 300  # 5 minute timeout for comprehensive testing
    )

    if(SANITIZER_TEST_ENV)
      set_tests_properties(z3_verification PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()

  # Python Z3 constraint verification scripts (Phase 4)
  option(ENABLE_Z3_PYTHON_SCRIPTS "Enable Z3 Python constraint verification (Phase 4)" ON)

  if(ENABLE_Z3_PYTHON_SCRIPTS)
    # Create custom target to run Z3 verification scripts
    add_custom_target(verify-constraints
      COMMAND python3 "${PROJECT_SOURCE_DIR}/rocq/z3/constraint_verification.py" --verbose
      COMMAND python3 "${PROJECT_SOURCE_DIR}/rocq/z3/christoffel_symmetry.py"
      COMMAND python3 "${PROJECT_SOURCE_DIR}/rocq/z3/conservation_laws.py"
      COMMENT "Running Z3 constraint verification scripts"
      WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}"
      VERBATIM
    )
  endif()

  # TLA+ Specification (Phase 4)
  option(ENABLE_TLAPLUS "Enable TLA+ model checking (Phase 4)" ON)

  if(ENABLE_TLAPLUS)
    message(STATUS "TLA+ model specification available: rocq/tla+/Geodesic.tla")
    message(STATUS "  Run TLC model checker with: tlc rocq/tla+/Geodesic.tla")
    message(STATUS "  Or use Apalache symbolic checker for larger state spaces")

    # Create informational custom target
    add_custom_target(check-tla
      COMMAND ${CMAKE_COMMAND} -E echo "TLA+ model checking requires TLC or Apalache:"
      COMMAND ${CMAKE_COMMAND} -E echo "  1. Install TLA+ Toolbox or use tlc directly"
      COMMAND ${CMAKE_COMMAND} -E echo "  2. Run: tlc rocq/tla+/Geodesic.tla -config rocq/tla+/Geodesic.cfg"
      COMMAND ${CMAKE_COMMAND} -E echo "  3. See rocq/docs/PHASE4_VALIDATION.md for details"
      COMMENT "TLA+ model checking instructions"
      VERBATIM
    )
  endif()

  if(ENABLE_PRECISION_TESTS AND EXISTS "${PROJECT_SOURCE_DIR}/tests/precision_regression_test.cpp")
    find_package(gmp CONFIG REQUIRED)
    find_package(mpfr CONFIG REQUIRED)
    add_executable(precision_regression_test
      "${PROJECT_SOURCE_DIR}/tests/precision_regression_test.cpp"
      ${PHYSICS_SRC_FILES}
    )
    target_include_directories(precision_regression_test PRIVATE
      "${PROJECT_SOURCE_DIR}/src"
      "${PROJECT_SOURCE_DIR}/src/physics"
    )
    target_compile_options(precision_regression_test PRIVATE ${PROJECT_WARNINGS})
    if(ENABLE_FAST_MATH)
      target_compile_options(precision_regression_test PRIVATE -fno-fast-math)
    endif()
    target_link_libraries(precision_regression_test PRIVATE
      gmp::gmp
      mpfr::mpfr
    )

    add_test(NAME precision_regression COMMAND precision_regression_test)
    set_tests_properties(precision_regression PROPERTIES
      LABELS "precision;unit"
      TIMEOUT 120
    )
    if(SANITIZER_TEST_ENV)
      set_tests_properties(precision_regression PROPERTIES
        ENVIRONMENT "${SANITIZER_TEST_ENV}"
      )
    endif()
  endif()
endif()

# ============================================================================
# Fuzzing Support (libFuzzer)
# ============================================================================

option(ENABLE_FUZZING "Enable fuzzing targets" OFF)

if(ENABLE_FUZZING)
  if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(STATUS "Fuzzing support enabled (libFuzzer)")

    # Fuzzing compile flags
    set(FUZZ_FLAGS
      -fsanitize=fuzzer,address,undefined
      -fno-omit-frame-pointer
      -g
    )

    # Physics library fuzz target
    if(EXISTS "${PROJECT_SOURCE_DIR}/fuzz/fuzz_physics.cpp")
      add_executable(fuzz_physics
        "${PROJECT_SOURCE_DIR}/fuzz/fuzz_physics.cpp"
        ${PHYSICS_SRC_FILES}
      )
      target_compile_options(fuzz_physics PRIVATE ${FUZZ_FLAGS})
      target_link_options(fuzz_physics PRIVATE -fsanitize=fuzzer,address,undefined)
      target_include_directories(fuzz_physics PRIVATE
        "${PROJECT_SOURCE_DIR}/src"
        "${PROJECT_SOURCE_DIR}/src/physics"
      )
      set_target_properties(fuzz_physics PROPERTIES
        CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
        CXX_STANDARD_REQUIRED ON
      )
    endif()

    # Shader preprocessor fuzz target
    if(EXISTS "${PROJECT_SOURCE_DIR}/fuzz/fuzz_shader.cpp")
      add_executable(fuzz_shader
        "${PROJECT_SOURCE_DIR}/fuzz/fuzz_shader.cpp"
      )
      target_compile_options(fuzz_shader PRIVATE ${FUZZ_FLAGS})
      target_link_options(fuzz_shader PRIVATE -fsanitize=fuzzer,address,undefined)
      target_include_directories(fuzz_shader PRIVATE
        "${PROJECT_SOURCE_DIR}/src"
      )
      set_target_properties(fuzz_shader PROPERTIES
        CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
        CXX_STANDARD_REQUIRED ON
      )
    endif()

    # Header-only physics library fuzz target
    if(EXISTS "${PROJECT_SOURCE_DIR}/fuzz/fuzz_headers.cpp")
      add_executable(fuzz_headers
        "${PROJECT_SOURCE_DIR}/fuzz/fuzz_headers.cpp"
        ${PHYSICS_SRC_FILES}
      )
      target_compile_options(fuzz_headers PRIVATE ${FUZZ_FLAGS})
      target_link_options(fuzz_headers PRIVATE -fsanitize=fuzzer,address,undefined)
      target_include_directories(fuzz_headers PRIVATE
        "${PROJECT_SOURCE_DIR}/src"
        "${PROJECT_SOURCE_DIR}/src/physics"
      )
      set_target_properties(fuzz_headers PROPERTIES
        CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
        CXX_STANDARD_REQUIRED ON
      )
    endif()
  else()
    message(WARNING "Fuzzing requires Clang compiler")
  endif()
endif()

# ============================================================================
# Code Formatting Target
# ============================================================================

find_program(CLANG_FORMAT_EXE NAMES "clang-format" "clang-format-17" "clang-format-16")
if(CLANG_FORMAT_EXE)
  message(STATUS "clang-format found: ${CLANG_FORMAT_EXE}")

  add_custom_target(format
    COMMAND ${CLANG_FORMAT_EXE}
      -i
      -style=file
      ${PROJECT_SRC_FILES}
      ${HEADER_FILES}
    COMMENT "Formatting source code with clang-format"
    VERBATIM
  )

  add_custom_target(format-check
    COMMAND ${CLANG_FORMAT_EXE}
      --dry-run
      --Werror
      -style=file
      ${PROJECT_SRC_FILES}
      ${HEADER_FILES}
    COMMENT "Checking code formatting"
    VERBATIM
  )
endif()

# ============================================================================
# Summary of Analysis Options
# ============================================================================

message(STATUS "")
message(STATUS "=== Static Analysis Configuration ===")
message(STATUS "  ENABLE_CLANG_TIDY:        ${ENABLE_CLANG_TIDY}")
message(STATUS "  ENABLE_CPPCHECK:          ${ENABLE_CPPCHECK}")
message(STATUS "  ENABLE_IWYU:              ${ENABLE_IWYU}")
message(STATUS "  ENABLE_GCC_ANALYZER:      ${ENABLE_GCC_ANALYZER}")
message(STATUS "  ENABLE_SHADER_VALIDATION: ${ENABLE_SHADER_VALIDATION}")
message(STATUS "  ENABLE_FUZZING:           ${ENABLE_FUZZING}")
message(STATUS "  ENABLE_PROFILING:         ${ENABLE_PROFILING}")
message(STATUS "  ENABLE_GPROF:             ${ENABLE_GPROF}")
message(STATUS "  ENABLE_COVERAGE:          ${ENABLE_COVERAGE}")
message(STATUS "  ENABLE_KTX:               ${ENABLE_KTX}")
message(STATUS "  ENABLE_OPENIMAGEIO:       ${ENABLE_OPENIMAGEIO}")
message(STATUS "")
