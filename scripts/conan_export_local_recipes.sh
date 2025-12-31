#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

conan export "${ROOT}/conan/recipes/imgui/1.92.5-docking"
conan export "${ROOT}/conan/recipes/tracy/0.13.1"
conan export "${ROOT}/conan/recipes/rmlui/6.1"
