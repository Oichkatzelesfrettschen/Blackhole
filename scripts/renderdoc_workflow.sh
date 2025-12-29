#!/bin/bash
# RenderDoc Integration Workflow for Blackhole
#
# This script provides utilities for GPU debugging with RenderDoc.
#
# Prerequisites:
#   - Install RenderDoc: https://renderdoc.org/
#   - Linux: apt install renderdoc
#   - Or download from: https://github.com/baldurk/renderdoc/releases
#
# Usage:
#   ./scripts/renderdoc_workflow.sh [command]
#
# Commands:
#   capture  - Launch Blackhole under RenderDoc
#   analyze  - Open latest capture in RenderDoc
#   info     - Print RenderDoc setup information

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
BUILD_DIR="$PROJECT_ROOT/build"
CAPTURE_DIR="$PROJECT_ROOT/captures"

# Find RenderDoc executables
RENDERDOC_CMD=""
if command -v renderdoccmd &> /dev/null; then
    RENDERDOC_CMD="renderdoccmd"
elif [ -f "/opt/renderdoc/bin/renderdoccmd" ]; then
    RENDERDOC_CMD="/opt/renderdoc/bin/renderdoccmd"
fi

RENDERDOC_GUI=""
if command -v qrenderdoc &> /dev/null; then
    RENDERDOC_GUI="qrenderdoc"
elif [ -f "/opt/renderdoc/bin/qrenderdoc" ]; then
    RENDERDOC_GUI="/opt/renderdoc/bin/qrenderdoc"
fi

# Print setup information
print_info() {
    echo "=== RenderDoc Workflow for Blackhole ==="
    echo ""
    echo "Build directory: $BUILD_DIR"
    echo "Capture directory: $CAPTURE_DIR"
    echo ""

    if [ -n "$RENDERDOC_CMD" ]; then
        echo "RenderDoc CLI: $RENDERDOC_CMD"
    else
        echo "RenderDoc CLI: NOT FOUND"
        echo "  Install with: apt install renderdoc"
    fi

    if [ -n "$RENDERDOC_GUI" ]; then
        echo "RenderDoc GUI: $RENDERDOC_GUI"
    else
        echo "RenderDoc GUI: NOT FOUND"
    fi

    echo ""
    echo "=== Manual RenderDoc Usage ==="
    echo ""
    echo "1. Launch RenderDoc GUI:"
    echo "   qrenderdoc"
    echo ""
    echo "2. In RenderDoc:"
    echo "   - File > Launch Application"
    echo "   - Executable Path: $BUILD_DIR/Blackhole"
    echo "   - Working Directory: $BUILD_DIR"
    echo "   - Click 'Launch'"
    echo ""
    echo "3. In the running application:"
    echo "   - Press F12 or PrintScreen to capture a frame"
    echo "   - Or use RenderDoc overlay controls"
    echo ""
    echo "4. Analyze the capture:"
    echo "   - Double-click the capture thumbnail in RenderDoc"
    echo "   - Use Event Browser to step through draw calls"
    echo "   - Use Texture Viewer to inspect render targets"
    echo "   - Use Mesh Viewer to inspect vertex data"
    echo ""
    echo "=== Debugging Shader Issues ==="
    echo ""
    echo "In RenderDoc Texture Viewer:"
    echo "  - Right-click shader stage > Edit"
    echo "  - Modify GLSL and recompile live"
    echo "  - Use History to see value at pixel"
    echo ""
    echo "In Pipeline State:"
    echo "  - View all uniforms and their values"
    echo "  - Inspect buffer bindings"
    echo "  - Check framebuffer attachments"
    echo ""
}

# Launch application under RenderDoc
capture_frame() {
    if [ -z "$RENDERDOC_CMD" ]; then
        echo "Error: RenderDoc CLI not found"
        echo "Install with: apt install renderdoc"
        exit 1
    fi

    mkdir -p "$CAPTURE_DIR"

    if [ ! -f "$BUILD_DIR/Blackhole" ]; then
        echo "Error: Blackhole not built"
        echo "Build first with: cmake --preset release && cmake --build --preset release"
        exit 1
    fi

    echo "Launching Blackhole under RenderDoc..."
    echo "Press F12 in the application to capture a frame"
    echo ""

    # Set up capture settings
    export RENDERDOC_HOOK_EGL=0  # Use GLX only
    export LD_PRELOAD=""  # Clear any preloads that might interfere

    cd "$BUILD_DIR"
    "$RENDERDOC_CMD" capture \
        --capture-callstacks \
        --capture-all-cmd-lists \
        --opt-api-validation \
        --wait-for-exit \
        --working-dir "$BUILD_DIR" \
        --capture-file "$CAPTURE_DIR/blackhole_capture" \
        ./Blackhole
}

# Open latest capture in RenderDoc GUI
analyze_capture() {
    if [ -z "$RENDERDOC_GUI" ]; then
        echo "Error: RenderDoc GUI not found"
        exit 1
    fi

    # Find most recent capture
    LATEST=$(ls -t "$CAPTURE_DIR"/*.rdc 2>/dev/null | head -1)

    if [ -z "$LATEST" ]; then
        echo "No captures found in $CAPTURE_DIR"
        echo "Run './scripts/renderdoc_workflow.sh capture' first"
        exit 1
    fi

    echo "Opening capture: $LATEST"
    "$RENDERDOC_GUI" "$LATEST" &
}

# Main dispatch
case "${1:-info}" in
    capture)
        capture_frame
        ;;
    analyze)
        analyze_capture
        ;;
    info|help|*)
        print_info
        ;;
esac
