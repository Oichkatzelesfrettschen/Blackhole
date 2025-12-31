#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

# Prefer Conan 2.x-friendly local exports when available; fall back to
# older commands for Conan 1.x compatibility.
CONAN_VER_STR="$(conan --version 2>/dev/null || true)"
if [[ "${CONAN_VER_STR}" =~ ^Conan\ version\ ([0-9]+)\. ]] ; then
  CONAN_MAJOR=${BASH_REMATCH[1]}
else
  CONAN_MAJOR=1
fi

if (( CONAN_MAJOR >= 2 )); then
  echo "Exporting local recipes for Conan 2.x"
  # In Conan 2.x 'conan export' still works for local cache; keep same behaviour
  conan export "${ROOT}/conan/recipes/imgui/1.92.5-docking"
  conan export "${ROOT}/conan/recipes/tracy/0.13.1"
  conan export "${ROOT}/conan/recipes/rmlui/6.1"
else
  echo "Using legacy Conan 1.x export commands"
  conan export "${ROOT}/conan/recipes/imgui/1.92.5-docking"
  conan export "${ROOT}/conan/recipes/tracy/0.13.1"
  conan export "${ROOT}/conan/recipes/rmlui/6.1"
fi
