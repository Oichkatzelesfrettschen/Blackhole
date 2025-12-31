#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CONAN_HOME="${ROOT}/.conan"
export CONAN_USER_HOME="${ROOT}/.conan"

conan export "${ROOT}/conan/recipes/imgui/1.92.5-docking"
conan export "${ROOT}/conan/recipes/tracy/0.12.2"
conan export "${ROOT}/conan/recipes/rmlui/4.4"
