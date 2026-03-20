# src/blender_bridge/CMakeLists.txt
#
# WHY: Build libblackhole_bridge.so for Blender Python ctypes integration.
# WHAT: Shared library wrapping physics:: namespace in a flat C ABI.
# HOW: cmake --preset release -DENABLE_BLENDER_BRIDGE=ON

add_library(blackhole_bridge SHARED
    blender_bridge.cpp
)

set_target_properties(blackhole_bridge PROPERTIES
    CXX_STANDARD 23
    CXX_STANDARD_REQUIRED ON
    POSITION_INDEPENDENT_CODE ON
    VERSION 1.0.0
    SOVERSION 1
    OUTPUT_NAME blackhole_bridge
)

target_include_directories(blackhole_bridge PRIVATE
    "${PROJECT_SOURCE_DIR}/src"
    "${PROJECT_SOURCE_DIR}/src/physics"
)

# Link physics sources (header-only for most, but geodesics.cpp etc. need compilation)
target_sources(blackhole_bridge PRIVATE
    "${PROJECT_SOURCE_DIR}/src/physics/geodesics.cpp"
    "${PROJECT_SOURCE_DIR}/src/physics/kerr.cpp"
    "${PROJECT_SOURCE_DIR}/src/physics/schwarzschild.cpp"
    "${PROJECT_SOURCE_DIR}/src/physics/noise.cpp"
    "${PROJECT_SOURCE_DIR}/src/physics/cosmology.cpp"
)

# Boost (optional, for Bessel/Jacobi)
if(TARGET Boost::boost)
    target_link_libraries(blackhole_bridge PRIVATE Boost::boost)
endif()

# CUDA backend: adds the ray-traced renderer (cuda_renderer.cu)
if(ENABLE_CUDA)
    target_sources(blackhole_bridge PRIVATE cuda_renderer.cu cuda_postprocess.cu)
    set_source_files_properties(cuda_renderer.cu PROPERTIES LANGUAGE CUDA)
    target_link_libraries(blackhole_bridge PRIVATE blackhole_cuda_rt CUDA::cudart)
    target_compile_definitions(blackhole_bridge PRIVATE BLACKHOLE_HAS_CUDA=1)
    # CUDA properties for the .cu file
    set_target_properties(blackhole_bridge PROPERTIES
        CUDA_STANDARD 17
        CUDA_SEPARABLE_COMPILATION ON
    )
endif()

# Install to a location Blender addons can find
install(TARGETS blackhole_bridge
    LIBRARY DESTINATION lib
    RUNTIME DESTINATION bin
)
install(FILES blender_bridge.h
    DESTINATION include/blackhole
)
