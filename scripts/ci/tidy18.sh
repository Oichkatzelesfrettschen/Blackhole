#!/bin/sh
# Run clang-tidy 18.1.8, the version the ci-analysis lane installs from Ubuntu
# 24.04 (clang-tidy-18), over selected translation units.
#
# usage: scripts/ci/tidy18.sh [-p BUILD_DIR] [-o OUT_DIR] FILE...
#
#   -p BUILD_DIR  directory holding compile_commands.json (default build/Release)
#   -o OUT_DIR    per-file logs (default build/tidy18)
#   FILE          repository-relative source paths, e.g. src/render/env_config.cpp
#
# The executable is $CLANG_TIDY when set, otherwise the PyPI wheel pinned at
# 18.1.8 through `uvx --from clang-tidy==18.1.8 clang-tidy`. clang-tidy 18
# cannot parse the libstdc++ of a newer host GCC, so the driver replaces the
# compile database's standard-library search path with GCC 14's, the library
# the CI runner compiles against; $GXX14 overrides the g++-14 used to find it.
# The summary prints one sorted `path:line check message` row per diagnostic;
# the exit status is 1 when any diagnostic remains.
set -eu

root=$(git rev-parse --show-toplevel)
build_dir=build/Release
out_dir=build/tidy18
while getopts p:o: opt; do
  case $opt in
    p) build_dir=$OPTARG ;;
    o) out_dir=$OPTARG ;;
    *) sed -n '5,10p' "$0" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
[ "$#" -gt 0 ] || { sed -n '5,10p' "$0" >&2; exit 2; }

cd "$root"
[ -r "$build_dir/compile_commands.json" ] || {
  echo "tidy18: $build_dir/compile_commands.json is missing; configure that tree first" >&2
  exit 2
}

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
    echo "tidy18: set CLANG_TIDY or install uv (uvx) for the pinned clang-tidy 18.1.8" >&2
    exit 2
  }
  tidy="uvx --from clang-tidy==18.1.8 clang-tidy"
fi

extra="--extra-arg=-Wno-unknown-warning-option --extra-arg=-Wno-unknown-argument"
extra="$extra --extra-arg=-Wno-unused-command-line-argument --extra-arg=-nostdinc++"
for dir in $stdinc; do
  extra="$extra --extra-arg=-isystem$dir"
done

mkdir -p "$out_dir"
rm -f "$out_dir"/*.log
jobs=${TIDY_JOBS:-$(nproc)}
# Word splitting of $tidy and $extra is intended: each holds several arguments.
# shellcheck disable=SC2016
printf '%s\n' "$@" | xargs -P "$jobs" -I{} sh -c '
  log="$1/$(printf "%s" "$2" | tr / _).log"
  # shellcheck disable=SC2086
  $3 -p "$4" $5 "$2" >"$log" 2>&1 || true
' tidy18 "$out_dir" {} "$tidy" "$build_dir" "$extra"

summary=$(cat "$out_dir"/*.log |
  grep -E '(error|warning): .*\[[a-z0-9.,-]+\]$' |
  sed -E 's#^([^:]+):([0-9]+):[0-9]+: (error|warning): (.*) \[([a-z0-9.,-]+)\]$#\1:\2 \5 \4#' |
  sed "s#^$root/##" | sort -u) || true
if [ -n "$summary" ]; then
  printf '%s\n' "$summary"
  exit 1
fi
echo "tidy18: no diagnostics in $# file(s)"
