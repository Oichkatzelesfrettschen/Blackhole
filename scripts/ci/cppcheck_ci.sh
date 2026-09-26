#!/bin/sh
# Run cppcheck 2.13.0, the version the ci-analysis lane installs from Ubuntu
# 24.04, over project translation units in a container.
#
# usage: scripts/ci/cppcheck_ci.sh [-p BUILD_DIR] [-b BASE_REF] [-f] [FILE...]
#
#   -p BUILD_DIR  directory holding compile_commands.json (default build/CiLike,
#                 the GCC 14 tree scripts/ci/ci_replica.sh configures)
#   -b BASE_REF   check every .cpp that differs from the merge base with BASE_REF,
#                 committed or not, plus untracked non-ignored .cpp files
#                 (default origin/main); ignored with FILE arguments
#   -f            analyze a tree whose configuration differs from the ci preset
#   FILE          repository-relative .cpp paths
#   CPPCHECK_CI_VERBOSE=1  print how many distinct flag sets each file had
#
# scripts/ci/check_ci_config.sh compares BUILD_DIR/CMakeCache.txt with the ci
# preset's cache variables in CMakePresets.json (target switches such as
# BUILD_TESTING, ENABLE_DESKTOP_APP, and ENABLE_CUDA, and preprocessor switches
# such as SIMD_TIER and ENABLE_FAST_MATH); the script exits 2 on a mismatch
# unless -f is given.
#
# The image comes from scripts/ci/Dockerfile.cppcheck and is built on first
# use as bh-ci-cppcheck; $CONTAINER_ENGINE selects docker or podman. Each file
# runs with the cppcheck arguments CMake attaches in CMakeLists.txt
# (CMAKE_CXX_CPPCHECK) plus the -D, -I, and -U flags of a compile_commands.json
# entry, as CMake passes them. A source compiled by several targets (main.cpp
# for each desktop variant, with BLACKHOLE_APP_VARIANT_* definitions) has one
# entry per target; each distinct flag set is analyzed once. The checkout and the Conan package cache mount
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
build_dir=build/CiLike
base=origin/main
force=0
while getopts p:b:f opt; do
  case $opt in
    p) build_dir=$OPTARG ;;
    b) base=$OPTARG ;;
    f) force=1 ;;
    *) sed -n '5,20p' "$0" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))

db=$root/$build_dir/compile_commands.json
[ -r "$db" ] || {
  echo "cppcheck_ci: $db is missing; configure that tree first" >&2
  echo "  (CI_REPLICA_NO_TEST=1 scripts/ci/ci_replica.sh configures build/CiLike)" >&2
  exit 2
}
if ! mismatch=$(scripts/ci/check_ci_config.sh "$build_dir"); then
  if [ "$force" = 1 ]; then
    echo "cppcheck_ci: warning: $build_dir differs from the ci preset: $mismatch" >&2
  else
    echo "cppcheck_ci: $build_dir differs from the ci preset: $mismatch" >&2
    echo "  use the ci_replica.sh tree (default -p build/CiLike) or pass -f" >&2
    exit 2
  fi
fi
PYTHON=${PYTHON:-python3}
VERBOSE=${CPPCHECK_CI_VERBOSE:-0}
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
  # One output line per distinct flag set among the file's entries.
  flagsets=$("$PYTHON" - "$db" "$root/$f" <<'EOF'
import json
import shlex
import sys

db, path = sys.argv[1], sys.argv[2]
entries = [e for e in json.load(open(db)) if e["file"] == path]
if not entries:
    sys.exit(3)
seen = []
for entry in entries:
    args = entry.get("arguments") or shlex.split(entry["command"])
    flags = shlex.join(a for a in args if a.startswith(("-D", "-I", "-U")))
    if flags not in seen:
        seen.append(flags)
print("\n".join(seen))
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
  lib=
  case $f in tests/*) lib=--library=googletest ;; esac
  while IFS= read -r flags; do
    checked=$((checked + 1))
    # $flags was shlex-quoted above; eval restores the argument list.
    eval "set -- $flags"
    "$engine" run --rm -v "$root:$root:ro" -v "$conan_home:$conan_home:ro" -w "$root" \
      "$image" cppcheck --enable=warning,style,performance,portability --std=c++23 \
      --suppress=missingInclude --suppress=unmatchedSuppression --suppress=unusedFunction \
      --inline-suppr --quiet --error-exitcode=1 -I"$root/src" -I"$root/src/physics" \
      ${lib:+"$lib"} "$@" "$root/$f" </dev/null || rc=1
  done <<FLAGSETS
$flagsets
FLAGSETS
  [ "$VERBOSE" = 1 ] && echo "cppcheck_ci: $f: $(printf '%s\n' "$flagsets" | wc -l) flag set(s)" >&2
done
if [ "$checked" = 0 ] && [ "$rc" = 0 ]; then
  echo "cppcheck_ci: no requested file is compiled in $build_dir; nothing was checked" >&2
  exit 1
fi
exit "$rc"
