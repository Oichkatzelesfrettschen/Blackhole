# Phase 9.T.1: GPU/CPU Parity Test Suite
# Builds test executables for validating verified physics shaders

cmake_minimum_required(VERSION 3.20)
project(BlackholeTests CXX)

# C++23 standard for consistency with verified physics headers
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Compiler flags: treat warnings as errors
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -O3")

# Include verified physics headers
include_directories(${CMAKE_SOURCE_DIR})

# Metric Parity Test
add_executable(metric_parity_test
    metric_parity_test.cpp
)

# Test target: run all tests
add_custom_target(run_tests
    COMMAND ./metric_parity_test
    DEPENDS metric_parity_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    COMMENT "Running GPU/CPU parity tests..."
)

# Install tests to build directory
install(TARGETS metric_parity_test
    RUNTIME DESTINATION bin/tests
)

# Display test build configuration
message(STATUS "Phase 9.T.1 Test Suite Configuration:")
message(STATUS "  C++ Standard: C++${CMAKE_CXX_STANDARD}")
message(STATUS "  Compiler: ${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")
message(STATUS "  Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  Test executable: metric_parity_test")
