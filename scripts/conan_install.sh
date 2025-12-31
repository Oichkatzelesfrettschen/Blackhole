#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

BUILD_TYPE="${1:-Release}"
OUTPUT_DIR="${2:-build}"

"${ROOT}/scripts/conan_init.sh"
"${ROOT}/scripts/conan_export_local_recipes.sh"

conan install "${ROOT}" \
  --output-folder="${OUTPUT_DIR}" \
  --build=missing \
  -s build_type="${BUILD_TYPE}" \
  -s compiler.cppstd=23
