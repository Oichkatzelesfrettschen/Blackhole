#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CONAN_HOME="${ROOT}/.conan"
export CONAN_USER_HOME="${ROOT}/.conan"

exec conan "$@"
