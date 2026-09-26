#!/bin/sh
# Report whether a CMake build tree is configured like the ci preset in the
# settings that change what the analyzers see.
#
# usage: scripts/ci/check_ci_config.sh BUILD_DIR
#
# ci-analysis analyzes the ci configuration: SIMD_TIER=SSE2, ENABLE_FAST_MATH
# and ENABLE_NATIVE_ARCH OFF. Those settings select preprocessor branches (the
# __AVX2__ paths in src/physics/batch.h and the __FAST_MATH__ guard in
# src/physics/compensated_rk4.h, for example), so a tree configured otherwise
# analyzes code the gate never compiles and misses code it does. Exits 0 when
# BUILD_DIR/CMakeCache.txt matches, 1 after printing each mismatch as KEY=VALUE
# on one line, and 2 when the cache is missing. scripts/ci/tidy18.sh and
# scripts/ci/cppcheck_ci.sh call it.
set -eu

[ "$#" = 1 ] || { sed -n '5p' "$0" >&2; exit 2; }
cache=$1/CMakeCache.txt
[ -r "$cache" ] || { echo "check_ci_config: $cache is missing" >&2; exit 2; }
mismatch=
for want in SIMD_TIER=SSE2 ENABLE_FAST_MATH=OFF ENABLE_NATIVE_ARCH=OFF; do
  key=${want%%=*}
  have=$(sed -n "s/^$key:[A-Z]*=//p" "$cache" | head -1)
  [ "$have" = "${want#*=}" ] || mismatch="$mismatch $key=${have:-unset}"
done
[ -z "$mismatch" ] && exit 0
echo "${mismatch# }"
exit 1
