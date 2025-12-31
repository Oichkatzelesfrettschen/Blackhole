#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

conan --version
conan profile detect --force
conan remote update conancenter --url="https://center2.conan.io"
conan remote list
