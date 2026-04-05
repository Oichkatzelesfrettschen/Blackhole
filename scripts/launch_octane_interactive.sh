#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

unset OCIO

if [[ -z "${BLACKHOLE_BRIDGE_LIB:-}" ]]; then
  for candidate in \
    "$ROOT_DIR/build/Release/src/blender_bridge/libblackhole_bridge.so.1.0.0" \
    "$ROOT_DIR/build/Release/src/blender_bridge/libblackhole_bridge.so" \
    "$ROOT_DIR/build/BlenderBridge/Release/src/blender_bridge/libblackhole_bridge.so.1.0.0" \
    "$ROOT_DIR/build/BlenderBridge/Release/src/blender_bridge/libblackhole_bridge.so"; do
    if [[ -f "$candidate" ]]; then
      export BLACKHOLE_BRIDGE_LIB="$candidate"
      break
    fi
  done
fi

exec /usr/bin/OctaneBlender "$@"
