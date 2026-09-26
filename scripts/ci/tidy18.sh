#!/bin/sh
# Run clang-tidy 18 over selected translation units, as the ci-analysis lane
# does with Ubuntu 24.04's clang-tidy-18 package (LLVM 18.1.3).
#
# usage: scripts/ci/tidy18.sh [-p BUILD_DIR] [-o OUT_DIR] [-f] FILE...
#
#   -p BUILD_DIR  directory holding compile_commands.json (default build/CiLike,
#                 the GCC 14 tree scripts/ci/ci_replica.sh configures)
#   -o OUT_DIR    per-file logs (default build/tidy18)
#   -f            analyze a tree whose configuration differs from the ci preset
#   FILE          repository-relative source paths, e.g. src/render/env_config.cpp
#
# scripts/ci/check_ci_config.sh compares BUILD_DIR/CMakeCache.txt with the ci
# preset's cache variables in CMakePresets.json (target switches such as
# BUILD_TESTING, ENABLE_DESKTOP_APP, and ENABLE_CUDA, and preprocessor switches
# such as SIMD_TIER and ENABLE_FAST_MATH); the driver exits 2 on a mismatch
# unless -f is given.
#
# The executable is $CLANG_TIDY when set, otherwise the PyPI wheel pinned at
# 18.1.1 through `uvx --from clang-tidy==18.1.1 clang-tidy`. PyPI carries no
# 18.1.3 wheel; 18.1.1 is the nearest release, and its `--list-checks
# --checks='*'` output matches both the Ubuntu 18.1.3 binary's and the 18.1.8
# wheel's (537 checks). clang-tidy 18
# cannot parse the libstdc++ of a newer host GCC, so the driver replaces the
# compile database's standard-library search path with GCC 14's, the library
# the CI runner compiles against; $GXX14 overrides the g++-14 used to find it.
# The summary prints one sorted `path:line check message` row per diagnostic.
# Exit status: 1 when any diagnostic remains; 2 when clang-tidy (or uvx) exits
# nonzero on a file without printing a diagnostic, which is a tool failure, not
# a clean result -- the tail of that file's log is printed.
set -eu

root=$(git rev-parse --show-toplevel)
build_dir=build/CiLike
out_dir=build/tidy18
force=0
while getopts p:o:f opt; do
  case $opt in
    p) build_dir=$OPTARG ;;
    o) out_dir=$OPTARG ;;
    f) force=1 ;;
    *) sed -n '5,12p' "$0" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
[ "$#" -gt 0 ] || { sed -n '5,12p' "$0" >&2; exit 2; }

cd "$root"
[ -r "$build_dir/compile_commands.json" ] || {
  echo "tidy18: $build_dir/compile_commands.json is missing; configure that tree first" >&2
  echo "  (CI_REPLICA_NO_TEST=1 scripts/ci/ci_replica.sh configures build/CiLike)" >&2
  exit 2
}

if ! mismatch=$(scripts/ci/check_ci_config.sh "$build_dir"); then
  if [ "$force" = 1 ]; then
    echo "tidy18: warning: $build_dir differs from the ci preset: $mismatch" >&2
  else
    echo "tidy18: $build_dir differs from the ci preset: $mismatch" >&2
    echo "  use the ci_replica.sh tree (default -p build/CiLike) or pass -f" >&2
    exit 2
  fi
fi

gxx=${GXX14:-g++-14}
command -v "$gxx" >/dev/null 2>&1 || { echo "tidy18: $gxx not found" >&2; exit 2; }
# The first three C++ search directories g++ reports are the libstdc++ headers,
# its target-specific directory, and backward/.
stdinc=$("$gxx" -E -x c++ -v /dev/null -o /dev/null 2>&1 |
  sed -n '/#include <...> search starts here:/,/End of search list./p' |
  grep '/include/c++' | sed 's/^ *//')
[ -n "$stdinc" ] || { echo "tidy18: no libstdc++ include path from $gxx" >&2; exit 2; }

if [ -n "${CLANG_TIDY:-}" ]; then
  tidy=$CLANG_TIDY
else
  command -v uvx >/dev/null 2>&1 || {
    echo "tidy18: set CLANG_TIDY or install uv (uvx) for the pinned clang-tidy 18.1.1" >&2
    exit 2
  }
  tidy="uvx --from clang-tidy==18.1.1 clang-tidy"
fi

extra="--extra-arg=-Wno-unknown-warning-option --extra-arg=-Wno-unknown-argument"
extra="$extra --extra-arg=-Wno-unused-command-line-argument --extra-arg=-nostdinc++"
for dir in $stdinc; do
  extra="$extra --extra-arg=-isystem$dir"
done

mkdir -p "$out_dir"
rm -f "$out_dir"/*.log "$out_dir"/*.rc
jobs=${TIDY_JOBS:-$(nproc)}
# Word splitting of $tidy and $extra is intended: each holds several arguments.
# shellcheck disable=SC2016
printf '%s\n' "$@" | xargs -P "$jobs" -I{} sh -c '
  base="$1/$(printf "%s" "$2" | tr / _)"
  # shellcheck disable=SC2086
  $3 -p "$4" $5 "$2" >"$base.log" 2>&1
  echo "$?" >"$base.rc"
' tidy18 "$out_dir" {} "$tidy" "$build_dir" "$extra"

diag_re='(error|warning): .*\[[a-z0-9.,-]+\]$'
failed=0
for f in "$@"; do
  base="$out_dir/$(printf '%s' "$f" | tr / _)"
  rc=$(cat "$base.rc" 2>/dev/null || echo missing)
  if [ "$rc" != 0 ] && ! grep -Eq "$diag_re" "$base.log" 2>/dev/null; then
    echo "tidy18: clang-tidy failed on $f (exit $rc) without a diagnostic:" >&2
    tail -5 "$base.log" >&2 2>/dev/null || true
    failed=1
  fi
done

summary=$(cat "$out_dir"/*.log | grep -E "$diag_re" |
  sed -E 's#^([^:]+):([0-9]+):[0-9]+: (error|warning): (.*) \[([a-z0-9.,-]+)\]$#\1:\2 \5 \4#' |
  awk -v prefix="$root/" 'index($0, prefix) == 1 { $0 = substr($0, length(prefix) + 1) } { print }' |
  sort -u) || true
[ "$failed" = 0 ] || exit 2
if [ -n "$summary" ]; then
  printf '%s\n' "$summary"
  exit 1
fi
echo "tidy18: no diagnostics in $# file(s)"
