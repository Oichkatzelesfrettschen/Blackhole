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

# ============================================================================
# SPIR-V Tooling (shaderc + spirv-tools + spirv-cross)
# ============================================================================

option(ENABLE_SPIRV_TOOLING "Enable SPIR-V build/reflect tooling" ON)
if(ENABLE_SPIRV_TOOLING)
  find_package(shaderc REQUIRED)
  find_package(SPIRV-Tools REQUIRED)
  find_package(spirv-cross REQUIRED)
  find_package(SPIRV-Headers REQUIRED)

  function(resolve_imported_target OUT_VAR)
    foreach(CANDIDATE IN LISTS ARGN)
      if(TARGET ${CANDIDATE})
        set(${OUT_VAR} ${CANDIDATE} PARENT_SCOPE)
        return()
      endif()
    endforeach()
    message(FATAL_ERROR "Required target not found: ${ARGN}")
  endfunction()

  resolve_imported_target(SHADERC_TARGET
    shaderc::shaderc
    shaderc::shaderc_shared
    shaderc
  )
  resolve_imported_target(SPIRV_TOOLS_TARGET
    SPIRV-Tools::SPIRV-Tools
    spirv-tools::spirv-tools
    SPIRV-Tools
  )
  resolve_imported_target(SPIRV_CROSS_TARGET
    spirv-cross::spirv-cross
    spirv-cross
  )
  resolve_imported_target(SPIRV_HEADERS_TARGET
    spirv-headers::spirv-headers
    SPIRV-Headers::SPIRV-Headers
    spirv-headers
  )

  add_library(spirv_tooling INTERFACE)
  target_link_libraries(spirv_tooling INTERFACE
    ${SHADERC_TARGET}
    ${SPIRV_TOOLS_TARGET}
    ${SPIRV_CROSS_TARGET}
    ${SPIRV_HEADERS_TARGET}
  )
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

# GLM SIMD intrinsics - enable SSE2 for portable SIMD
add_compile_definitions(GLM_FORCE_INTRINSICS)
add_compile_definitions(GLM_FORCE_SSE2)
add_compile_definitions(GLM_FORCE_ALIGNED_GENTYPES)

# Detect if AVX2 is available on build machine (optional)
include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
if(COMPILER_SUPPORTS_AVX2)
  option(ENABLE_AVX2 "Enable AVX2 optimizations" OFF)
  if(ENABLE_AVX2)
    add_compile_definitions(GLM_FORCE_AVX2)
    add_compile_options(-mavx2 -mfma)
    message(STATUS "AVX2 SIMD optimizations enabled")
  endif()
endif()

# Fast math for non-critical paths (can be disabled for precision)
option(ENABLE_FAST_MATH "Enable fast math optimizations" ON)
if(ENABLE_FAST_MATH)
  add_compile_options(-ffast-math)
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
option(ENABLE_WERROR "Treat compiler warnings as errors" OFF)

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
  -Wformat-overflow=2
  -Wformat-truncation=2
  -Wformat-security
  -Wformat-signedness
  -Wshadow
  -Wconversion
  -Wsign-conversion
  -Wfloat-conversion
  -Wnarrowing
  -Wstrict-overflow=2
)

# Level 3: C++ specific warnings
set(WARN_LEVEL3
  ${WARN_LEVEL2}
  -Wnon-virtual-dtor
  -Woverloaded-virtual
  -Wold-style-cast
  -Wcast-align
  -Wcast-qual
  -Wuseless-cast
  -Wzero-as-null-pointer-constant
  -Wextra-semi
  -Wmissing-declarations
)

# Level 4: Extra strictness (GCC-specific, may not work on Clang)
set(WARN_LEVEL4
  ${WARN_LEVEL3}
  -Wdouble-promotion
  -Wnull-dereference
  -Wimplicit-fallthrough=5
  -Wduplicated-cond
  -Wduplicated-branches
  -Wlogical-op
  -Wundef
  -Wunused-macros
  -Wstack-usage=8192
)

# Level 5: Maximum strictness
set(WARN_LEVEL5
  ${WARN_LEVEL4}
  -Warray-bounds=2
  -Wattribute-alias=2
  -Wstringop-overflow=4
  -Walloca
  -Wvla
  -Wtrampolines
  -Wshift-overflow=2
  -Wredundant-decls
  # Note: -Winline omitted as it triggers on implicit destructors
)

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

# Physics library source files
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
  "${PROJECT_SOURCE_DIR}/src/render.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader.cpp"
  "${PROJECT_SOURCE_DIR}/src/shader_manager.cpp"
  "${PROJECT_SOURCE_DIR}/src/texture.cpp"
  "${PROJECT_SOURCE_DIR}/src/grmhd_packed_loader.cpp"
  "${PROJECT_SOURCE_DIR}/src/stb_image.cpp"
  "${PROJECT_SOURCE_DIR}/src/input.cpp"
  "${PROJECT_SOURCE_DIR}/src/settings.cpp"
  "${PROJECT_SOURCE_DIR}/src/GLDebugMessageCallback.cc"
  ${PHYSICS_SRC_FILES}
)

set(THIRDPARTY_SRC_FILES
  "${PROJECT_SOURCE_DIR}/src/imgui_impl_glfw.cpp"
  "${PROJECT_SOURCE_DIR}/src/imgui_impl_opengl3.cpp"
)

# Collect all header files including physics subdirectory
file(GLOB HEADER_FILES "${PROJECT_SOURCE_DIR}/src/*.h" "${PROJECT_SOURCE_DIR}/src/*.hpp")
file(GLOB PHYSICS_HEADER_FILES "${PROJECT_SOURCE_DIR}/src/physics/*.h")
list(APPEND HEADER_FILES ${PHYSICS_HEADER_FILES})

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
set_source_files_properties("${PROJECT_SOURCE_DIR}/src/main.cpp" PROPERTIES
  COMPILE_OPTIONS "-Wno-stack-usage"
)

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

target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE
  GLFW_INCLUDE_NONE
  IMGUI_IMPL_OPENGL_LOADER_CUSTOM
  BLACKHOLE_ENABLE_RMLUI=$<BOOL:${ENABLE_RMLUI}>
  BLACKHOLE_ENABLE_SPIRV_TOOLING=$<BOOL:${ENABLE_SPIRV_TOOLING}>
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
)
target_link_libraries(physics_bench PRIVATE glfw glbinding::glbinding glm::glm)

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
target_compile_options(nubhlight_inspect PRIVATE -Wno-stack-usage)

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
target_compile_options(nubhlight_pack PRIVATE -Wno-stack-usage)

if(ENABLE_SPIRV_TOOLING)
  add_executable(spirv_bake
    "${PROJECT_SOURCE_DIR}/tools/spirv_bake.cpp"
  )

  set_target_properties(spirv_bake PROPERTIES
    CXX_STANDARD ${BLACKHOLE_CXX_STANDARD}
    CXX_STANDARD_REQUIRED ON
    CXX_EXTENSIONS OFF
  )

  target_link_libraries(spirv_bake PRIVATE CLI11::CLI11 spirv_tooling)
  target_compile_options(spirv_bake PRIVATE ${PROJECT_WARNINGS})
  target_compile_definitions(spirv_bake PRIVATE BLACKHOLE_ENABLE_SPIRV_TOOLING=1)
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
  find_program(SPIRV_VAL NAMES "spirv-val")
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

    # SPIR-V compilation target (optional)
    if(GLSLC)
      message(STATUS "glslc found: ${GLSLC}")

      set(SPIRV_OUTPUT_DIR "${CMAKE_BINARY_DIR}/spirv")
      file(MAKE_DIRECTORY ${SPIRV_OUTPUT_DIR})

      set(SPIRV_COMPILE_COMMANDS)
      foreach(shader ${ALL_SHADERS})
        get_filename_component(shader_name ${shader} NAME)
        set(spirv_output "${SPIRV_OUTPUT_DIR}/${shader_name}.spv")
        list(APPEND SPIRV_COMPILE_COMMANDS
          COMMAND ${GLSLC}
            -c
            -O
            -I${PROJECT_SOURCE_DIR}/shader/include
            ${shader}
            -o ${spirv_output}
        )
      endforeach()

      add_custom_target(compile-spirv
        ${SPIRV_COMPILE_COMMANDS}
        COMMENT "Compiling shaders to SPIR-V"
        VERBATIM
      )
    endif()
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
	    target_compile_options(physics_test PRIVATE -Wno-stack-usage)
	    if(ENABLE_FAST_MATH)
	      target_compile_options(physics_test PRIVATE -fno-fast-math)
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
