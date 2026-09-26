#!/bin/sh
# Report whether a CMake build tree is configured like the ci preset.
#
# usage: scripts/ci/check_ci_config.sh BUILD_DIR
#
# The expected values are the ci preset's cacheVariables in CMakePresets.json,
# with its inherited presets resolved, so the check follows the preset when it
# changes. Every variable is compared except CMAKE_TOOLCHAIN_FILE (a path) and
# ENABLE_CLANG_TIDY / ENABLE_CPPCHECK (ci-analysis turns them on to run the
# analyzers; they register no sources). The compared set covers the switches
# that decide which targets and sources exist -- BUILD_TESTING,
# ENABLE_DESKTOP_APP, ENABLE_CUDA, ENABLE_BLENDER_BRIDGE,
# ENABLE_SHADER_VALIDATION -- and the ones that select preprocessor branches:
# SIMD_TIER, ENABLE_FAST_MATH, ENABLE_NATIVE_ARCH, CMAKE_BUILD_TYPE (the
# __AVX2__ paths in src/physics/batch.h and the __FAST_MATH__ guard in
# src/physics/compensated_rk4.h, for example). Exits 0 when
# BUILD_DIR/CMakeCache.txt matches, 1 after printing each mismatch as
# KEY=VALUE on one line, and 2 when the cache or presets cannot be read.
# scripts/ci/tidy18.sh and scripts/ci/cppcheck_ci.sh call it.
set -eu

[ "$#" = 1 ] || { sed -n '4p' "$0" >&2; exit 2; }
root=$(git rev-parse --show-toplevel)
cache=$1/CMakeCache.txt
[ -r "$cache" ] || { echo "check_ci_config: $cache is missing" >&2; exit 2; }
PYTHON=${PYTHON:-python3}
"$PYTHON" - "$root/CMakePresets.json" "$cache" <<'PY'
import json
import re
import sys

presets_path, cache_path = sys.argv[1], sys.argv[2]
IGNORED = {"CMAKE_TOOLCHAIN_FILE", "ENABLE_CLANG_TIDY", "ENABLE_CPPCHECK"}
try:
    presets = {p["name"]: p for p in json.load(open(presets_path))["configurePresets"]}
except (OSError, KeyError, ValueError) as error:
    print(f"check_ci_config: cannot read {presets_path}: {error}", file=sys.stderr)
    sys.exit(2)

expected = {}
chain = []
name = "ci"
while name:
    preset = presets[name]
    chain.append(preset)
    parent = preset.get("inherits")
    name = parent[0] if isinstance(parent, list) else parent
for preset in reversed(chain):
    expected.update(preset.get("cacheVariables", {}))

cache = {}
for line in open(cache_path, encoding="utf-8", errors="replace"):
    match = re.match(r"^([A-Za-z0-9_]+):[A-Z]+=(.*)$", line.rstrip("\n"))
    if match:
        cache.setdefault(match.group(1), match.group(2))

mismatch = [
    f"{key}={cache.get(key, 'unset')}"
    for key, value in sorted(expected.items())
    if key not in IGNORED and cache.get(key) != str(value)
]
if mismatch:
    print(" ".join(mismatch))
    sys.exit(1)
PY
