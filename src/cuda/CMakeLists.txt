# src/cuda/CMakeLists.txt
# CUDA ray tracing backend library for Blackhole
#
# WHY: Isolates CUDA C++17 code from the C++23 host codebase.
# WHAT: Builds a static library (blackhole_cuda_rt) containing all .cu files.
# HOW: Separable compilation, --use_fast_math, SM89+SM80, C-compat firewall check.

add_library(blackhole_cuda_rt STATIC
    cuda_gl_interop.cu
    cuda_backend.cu
    kernel_launch.cu
    kernel_registry.cu
    kernels_fp32.cu
    kernels_fp16.cu
    kernels_fp16_h2.cu
    lut_manager.cu
)

# CUDA device code is C++17 (nvcc limitation). Host code remains C++23.
set_target_properties(blackhole_cuda_rt PROPERTIES
    CUDA_STANDARD 17
    CUDA_STANDARD_REQUIRED ON
    CUDA_SEPARABLE_COMPILATION ON
    POSITION_INDEPENDENT_CODE ON
)

# YSU-engine build flags: --use_fast_math -lineinfo -Xptxas=-v -dlto
target_compile_options(blackhole_cuda_rt PRIVATE
    $<$<COMPILE_LANGUAGE:CUDA>:
        --use_fast_math
        -lineinfo
        -Xptxas=-v
        --expt-relaxed-constexpr
    >
)
# NOTE: -dlto conflicts with multi-arch -gencode (SM89;80). LTO for CUDA
# with multiple architectures requires code=lto_<arch> in CMAKE_CUDA_ARCHITECTURES
# which is a CMake 3.25+ feature. Omitted here for compatibility.

target_include_directories(blackhole_cuda_rt PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

target_link_libraries(blackhole_cuda_rt PRIVATE
    CUDA::cudart
)

# OpenGL interop: link against libGL for cudaGraphicsGLRegisterImage at
# link time only. Do NOT use target_link_libraries(... OpenGL::GL) here --
# that injects -isystem /usr/include into the nvcc compile command, which
# breaks the GCC 15 cmath -> #include_next <math.h> chain with CCCL.
# nvcc discovers GL headers automatically via the host compiler (GCC) paths.
target_link_libraries(blackhole_cuda_rt PRIVATE -lGL)

# ============================================================================
# C-compatibility firewall check
# ============================================================================
# Verify that kernel_launch.h compiles as pure C to enforce the POD-only
# boundary between C++23 host and C++17 CUDA device code.

include(CheckCSourceCompiles)
set(CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_SOURCE_DIR}")
check_c_source_compiles("
#include \"kernel_launch.h\"
int main(void) {
    struct BH_LaunchParams p;
    p.rs = 1.0f;
    p.width = 1920;
    (void)p;
    return 0;
}
" KERNEL_LAUNCH_H_IS_C_COMPATIBLE)

if(NOT KERNEL_LAUNCH_H_IS_C_COMPATIBLE)
    message(FATAL_ERROR
        "kernel_launch.h failed C-compatibility check. "
        "The CUDA/host firewall is broken: this header must contain ONLY "
        "C-compatible POD types. No std::, glm::, or C++ templates allowed."
    )
endif()
