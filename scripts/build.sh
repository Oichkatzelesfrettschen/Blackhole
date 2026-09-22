#!/usr/bin/env sh
# Explicit jobs keep Make and Ninja consistent across developer machines.
set -eu
build_preset=${1:-release}
if [ "$#" -gt 0 ]; then
  shift
fi
build_jobs=${CMAKE_BUILD_PARALLEL_LEVEL:-$(nproc)}
case "$build_jobs" in
  ''|0|*[!0-9]*) echo 'CMAKE_BUILD_PARALLEL_LEVEL must be a positive integer' >&2; exit 2 ;;
esac
exec cmake --build --preset "$build_preset" --parallel "$build_jobs" "$@"
