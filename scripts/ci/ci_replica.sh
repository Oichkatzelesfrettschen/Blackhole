#!/bin/sh
# Reproduce the GCC 14 `ci` lane (or `ci-release` with CI_REPLICA_RELEASE=1)
# on a workstation whose Conan toolchain pins clang.
#
# usage: scripts/ci/ci_replica.sh [CTEST_REGEX]
#
#   CTEST_REGEX            run only matching tests (default: the whole suite)
#   CI_REPLICA_RELEASE=1   mirror ci-release: -ffast-math plus fat LTO, in
#                          build/CiLikeRelease instead of build/CiLike
#   CI_REPLICA_SANITIZE=1  mirror ci-sanitize: ASan plus UBSan, hardening and
#                          -Werror off, in build/CiLikeSanitize; excludes the
#                          same GL-context tests as the lane
#   CI_REPLICA_NO_TEST=1   stop after the build
#   CI_REPLICA_JOBS=N      build and test parallelism (default: nproc)
#   GCC14 / GXX14          compiler names (default gcc-14 / g++-14)
#
# Prerequisite: `./scripts/conan_install.sh Release build` in this checkout.
# The runner builds its dependencies with GCC 14 through conan/profiles/ci;
# the replica reuses the local Release packages and swaps the compiler in a
# copy of the generated toolchain, because the toolchain's own
# set(CMAKE_CXX_COMPILER ...) overrides a -D on the command line. The
# generators directory is copied whole since the toolchain resolves package
# configs relative to CMAKE_CURRENT_LIST_DIR. The runner has no system glm, so
# bwrap mounts an empty /usr/include/glm and a test that reaches glm only
# through /usr/include fails here as it does in CI.
# Logs: build/cilike-configure.log, build/cilike.log, build/cilike-ctest.log.
set -eu

root=$(git rev-parse --show-toplevel)
cd "$root"
rx=${1:-}
bdir=build/CiLike
fast_math=OFF
lto=OFF
sanitize=OFF
hardening=ON
werror=ON
exclude=
if [ "${CI_REPLICA_RELEASE:-0}" = 1 ]; then
  bdir=build/CiLikeRelease
  fast_math=ON
  lto=ON
elif [ "${CI_REPLICA_SANITIZE:-0}" = 1 ]; then
  bdir=build/CiLikeSanitize
  sanitize=ON
  hardening=OFF
  werror=OFF
  # Keep in step with the ci-sanitize case of the Test step in ci.yml.
  exclude='^(gpu_cpu_parity|kerr_shader_capture)$'
fi
cc=${GCC14:-gcc-14}
cxx=${GXX14:-g++-14}
jobs=${CI_REPLICA_JOBS:-$(nproc)}

# A linked worktree shares the primary checkout's package cache.
common=$(git rev-parse --path-format=absolute --git-common-dir)
CONAN_HOME=${BLACKHOLE_CONAN_HOME:-$(dirname "$common")/.conan}
export CONAN_HOME

gen=build/Release/generators
[ -r "$gen/conan_toolchain.cmake" ] || {
  echo "ci_replica: missing $gen/conan_toolchain.cmake; run ./scripts/conan_install.sh Release build" >&2
  exit 2
}
for tool in "$cc" "$cxx" bwrap cmake ninja ctest; do
  command -v "$tool" >/dev/null 2>&1 || { echo "ci_replica: $tool not found" >&2; exit 2; }
done

# Each mode keeps its own toolchain copy, so replicas of different modes can
# run side by side. awk takes the compiler names as data (-v), so a path such
# as /usr/bin/g++-14 needs no escaping.
tcdir=$bdir-toolchain
mkdir -p "$tcdir"
cp -R "$gen/." "$tcdir/"
awk -v cc="$cc" -v cxx="$cxx" '
  /^set\(CMAKE_C_COMPILER / { print "set(CMAKE_C_COMPILER \"" cc "\")"; next }
  /^set\(CMAKE_CXX_COMPILER / { print "set(CMAKE_CXX_COMPILER \"" cxx "\")"; next }
  { gsub(/ -stdlib=libstdc\+\+/, ""); print }
' "$gen/conan_toolchain.cmake" >"$tcdir/conan_toolchain.cmake"

hide_glm() {
  if [ -d /usr/include/glm ]; then
    bwrap --dev-bind / / --tmpfs /usr/include/glm "$@"
  else
    "$@"
  fi
}

hide_glm cmake -S . -B "$bdir" -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE="$root/$tcdir/conan_toolchain.cmake" \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER="$cc" -DCMAKE_CXX_COMPILER="$cxx" \
  -DENABLE_NATIVE_ARCH=OFF -DENABLE_LTO="$lto" -DENABLE_FAT_LTO="$lto" \
  -DENABLE_FAST_MATH="$fast_math" -DENABLE_CLANG_TIDY=OFF -DENABLE_CPPCHECK=OFF \
  -DENABLE_WERROR="$werror" -DWARNING_LEVEL=5 -DENABLE_CUDA=OFF -DENABLE_BLENDER_BRIDGE=OFF \
  -DENABLE_DESKTOP_APP=ON -DBUILD_TESTING=ON -DENABLE_SHADER_VALIDATION=ON \
  -DSIMD_TIER=SSE2 -DENABLE_ASAN="$sanitize" -DENABLE_UBSAN="$sanitize" \
  -DENABLE_HARDENING="$hardening" >build/cilike-configure.log 2>&1 || {
  tail -30 build/cilike-configure.log >&2
  exit 1
}
hide_glm cmake --build "$bdir" --parallel "$jobs" -- -k 0 >build/cilike.log 2>&1 || {
  grep -nE 'FAILED:|error:|fatal error' build/cilike.log | head -40 >&2
  exit 1
}
echo "ci_replica: $bdir build ok"
[ "${CI_REPLICA_NO_TEST:-0}" = 1 ] && exit 0

set -- --test-dir "$bdir" --output-on-failure --no-tests=error --parallel "$jobs"
[ -n "$rx" ] && set -- "$@" -R "$rx"
[ -n "$exclude" ] && set -- "$@" --exclude-regex "$exclude"
if hide_glm ctest "$@" >build/cilike-ctest.log 2>&1; then
  grep -E "tests passed" build/cilike-ctest.log
else
  grep -E 'tests passed|Failed|\*\*\*' build/cilike-ctest.log | tail -20 >&2
  exit 1
fi
