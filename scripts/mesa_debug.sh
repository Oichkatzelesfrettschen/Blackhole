#!/bin/bash
# Mesa/OpenGL Debug Environment Script for Blackhole
#
# Usage:
#   source scripts/mesa_debug.sh [mode]
#
# Modes:
#   shader  - Enable shader debugging and capture
#   driver  - Enable driver debug output
#   full    - Enable all debug features
#   perf    - Performance analysis mode
#   clear   - Clear all debug variables
#
# After sourcing, run the application normally:
#   ./build/Blackhole

set -e

MODE="${1:-full}"

# Clear existing debug variables
clear_debug_vars() {
    unset MESA_DEBUG
    unset MESA_GLSL
    unset MESA_SHADER_CAPTURE_PATH
    unset LIBGL_ALWAYS_SOFTWARE
    unset LIBGL_DEBUG
    unset INTEL_DEBUG
    unset AMD_DEBUG
    unset RADV_DEBUG
    unset NIR_DEBUG
    unset GALLIUM_PRINT_OPTIONS
    unset __GL_THREADED_OPTIMIZATIONS
    unset vblank_mode
    echo "Cleared all Mesa debug environment variables"
}

# Shader debugging mode
shader_mode() {
    export MESA_DEBUG=1
    export MESA_GLSL=errors
    export MESA_SHADER_CAPTURE_PATH="/tmp/blackhole_shaders"
    mkdir -p "$MESA_SHADER_CAPTURE_PATH"
    echo "Shader debug mode enabled"
    echo "  - GLSL warnings as errors"
    echo "  - Shaders captured to: $MESA_SHADER_CAPTURE_PATH"
}

# Driver debug mode
driver_mode() {
    export MESA_DEBUG=1
    export LIBGL_DEBUG=verbose

    # Detect GPU vendor and set appropriate debug flags
    if lspci | grep -qi nvidia; then
        echo "NVIDIA GPU detected - use nvidia-smi for debugging"
    elif lspci | grep -qi "AMD\|ATI"; then
        export AMD_DEBUG=shaders
        export RADV_DEBUG=checkir,errors,info
        echo "AMD GPU detected - AMD debug enabled"
    elif lspci | grep -qi intel; then
        export INTEL_DEBUG=shader,vs,fs,gs,cs,bat,perf
        echo "Intel GPU detected - Intel debug enabled"
    fi
}

# Full debug mode
full_mode() {
    shader_mode
    driver_mode

    export NIR_DEBUG=print_vs,print_fs
    export GALLIUM_PRINT_OPTIONS=1

    # Disable threading optimizations for debugging
    export __GL_THREADED_OPTIMIZATIONS=0

    echo "Full debug mode enabled"
}

# Performance analysis mode
perf_mode() {
    export MESA_DEBUG=0
    export vblank_mode=0  # Disable vsync
    export __GL_THREADED_OPTIMIZATIONS=1

    # Vendor-specific perf options
    if lspci | grep -qi "AMD\|ATI"; then
        export RADV_PERFTEST=aco
        echo "AMD performance mode enabled (ACO)"
    elif lspci | grep -qi intel; then
        export INTEL_DEBUG=perf
        echo "Intel performance mode enabled"
    fi

    echo "Performance analysis mode enabled"
    echo "  - VSync disabled"
    echo "  - Threaded optimizations enabled"
}

# Software rendering mode (for debugging without GPU)
software_mode() {
    export LIBGL_ALWAYS_SOFTWARE=1
    export MESA_DEBUG=1
    echo "Software rendering mode enabled (llvmpipe)"
}

# Main dispatch
case "$MODE" in
    shader)
        clear_debug_vars
        shader_mode
        ;;
    driver)
        clear_debug_vars
        driver_mode
        ;;
    full)
        clear_debug_vars
        full_mode
        ;;
    perf)
        clear_debug_vars
        perf_mode
        ;;
    software)
        clear_debug_vars
        software_mode
        ;;
    clear)
        clear_debug_vars
        ;;
    *)
        echo "Unknown mode: $MODE"
        echo "Available modes: shader, driver, full, perf, software, clear"
        exit 1
        ;;
esac

echo ""
echo "Now run: ./build/Blackhole"
