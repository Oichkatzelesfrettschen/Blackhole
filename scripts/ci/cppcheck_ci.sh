#!/bin/sh
# Run cppcheck 2.13.0, the version the ci-analysis lane installs from Ubuntu
# 24.04, over project translation units in a container.
#
# usage: scripts/ci/cppcheck_ci.sh [-p BUILD_DIR] [-b BASE_REF] [FILE...]
#
#   -p BUILD_DIR  directory holding compile_commands.json (default build/Release)
#   -b BASE_REF   check every .cpp that differs from the merge base with BASE_REF,
#                 committed or not, plus untracked non-ignored .cpp files
#                 (default origin/main); ignored with FILE arguments
#   FILE          repository-relative .cpp paths
#
# The image comes from scripts/ci/Dockerfile.cppcheck and is built on first
# use as bh-ci-cppcheck; $CONTAINER_ENGINE selects docker or podman. Each file
# runs with the cppcheck arguments CMake attaches in CMakeLists.txt
# (CMAKE_CXX_CPPCHECK) plus the -D, -I, and -U flags of its compile_commands.json
# entry, as CMake passes them. The checkout and the Conan package cache mount
# read-only at their host paths so the recorded include paths resolve inside
# the container. A file the build does not compile is skipped with a notice;
# the run fails when every file is skipped, when a compile database records
# paths outside this checkout (a tree configured from another worktree or a
# container), or when reading the database fails.
# Tests under tests/ add --library=googletest; CMake adds it only
# to GTest targets, so a finding on a non-GTest test may be absent in CI.
set -eu

root=$(git rev-parse --show-toplevel)
cd "$root"
build_dir=build/Release
base=origin/main
while getopts p:b: opt; do
  case $opt in
    p) build_dir=$OPTARG ;;
    b) base=$OPTARG ;;
    *) sed -n '5,12p' "$0" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))

db=$root/$build_dir/compile_commands.json
[ -r "$db" ] || { echo "cppcheck_ci: $db is missing; configure that tree first" >&2; exit 2; }
PYTHON=${PYTHON:-python3}
engine=${CONTAINER_ENGINE:-docker}
image=bh-ci-cppcheck
common=$(git rev-parse --path-format=absolute --git-common-dir)
conan_home=${BLACKHOLE_CONAN_HOME:-$(dirname "$common")/.conan}

if [ "$#" -eq 0 ]; then
  fork=$(git merge-base "$base" HEAD)
  # Changed tracked files plus untracked, non-ignored ones: a new source that
  # is not yet added is still part of the change under review.
  files=$({ git diff --name-only "$fork" -- '*.cpp'
    git ls-files --others --exclude-standard -- '*.cpp'; } | sort -u |
    while read -r f; do [ -f "$f" ] && printf '%s\n' "$f"; done)
  [ -n "$files" ] || { echo "cppcheck_ci: no .cpp differs from $base"; exit 0; }
  # Word splitting is intended: repository paths carry no whitespace.
  # shellcheck disable=SC2086
  set -- $files
fi

# A compile database written for another checkout names files this one never
# matches, which would otherwise skip every file silently.
"$PYTHON" - "$db" "$root" <<'EOF' || exit 2
import json
import sys

db, root = sys.argv[1], sys.argv[2]
entries = json.load(open(db))
if not any(e["file"].startswith(root + "/") for e in entries):
    sample = entries[0]["file"] if entries else "(empty)"
    sys.exit(f"cppcheck_ci: {db} records no file under {root} (e.g. {sample}); reconfigure it here")
EOF

if ! "$engine" image inspect "$image" >/dev/null 2>&1; then
  "$engine" build -t "$image" -f scripts/ci/Dockerfile.cppcheck scripts/ci >&2
fi

rc=0
checked=0
for f in "$@"; do
  # CMake's co-compile driver forwards only the -D, -I, and -U arguments of the
  # compile line to cppcheck; -isystem dependency headers stay invisible to it.
  flags=$("$PYTHON" - "$db" "$root/$f" <<'EOF'
import json
import shlex
import sys

db, path = sys.argv[1], sys.argv[2]
entries = [e for e in json.load(open(db)) if e["file"] == path]
if not entries:
    sys.exit(3)
args = entries[0].get("arguments") or shlex.split(entries[0]["command"])
print(shlex.join(a for a in args if a.startswith(("-D", "-I", "-U"))))
EOF
  ) || {
    status=$?
    [ -f "$f" ] || { echo "cppcheck_ci: $f does not exist" >&2; rc=1; continue; }
    if [ "$status" = 3 ]; then
      # CI analyzes exactly the translation units its build compiles.
      echo "cppcheck_ci: $f is not compiled in $build_dir; skipped" >&2
    else
      echo "cppcheck_ci: reading $db for $f failed (exit $status)" >&2
      rc=1
    fi
    continue
  }
  checked=$((checked + 1))
  lib=
  case $f in tests/*) lib=--library=googletest ;; esac
  # $flags was shlex-quoted above; eval restores the argument list.
  eval "set -- $flags"
  "$engine" run --rm -v "$root:$root:ro" -v "$conan_home:$conan_home:ro" -w "$root" \
    "$image" cppcheck --enable=warning,style,performance,portability --std=c++23 \
    --suppress=missingInclude --suppress=unmatchedSuppression --suppress=unusedFunction \
    --inline-suppr --quiet --error-exitcode=1 -I"$root/src" -I"$root/src/physics" \
    ${lib:+"$lib"} "$@" "$root/$f" || rc=1
done
if [ "$checked" = 0 ] && [ "$rc" = 0 ]; then
  echo "cppcheck_ci: no requested file is compiled in $build_dir; nothing was checked" >&2
  exit 1
fi
exit "$rc"
