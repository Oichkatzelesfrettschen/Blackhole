#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Conan cache/config stays inside a checkout rather than a system path. The
# default is this tree's .conan; a linked worktree sets BLACKHOLE_CONAN_HOME
# to the primary checkout's .conan so every worktree reuses one package cache.
# A dedicated variable keeps an unrelated global CONAN_HOME from redirecting
# the build into a system cache.
export CONAN_HOME="${BLACKHOLE_CONAN_HOME:-${ROOT}/.conan}"
export CONAN_USER_HOME="${CONAN_HOME}"
mkdir -p "${CONAN_HOME}"
