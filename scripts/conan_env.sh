#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Enforce repo-local Conan cache/config to avoid system paths.
export CONAN_HOME="${ROOT}/.conan"
export CONAN_USER_HOME="${ROOT}/.conan"
mkdir -p "${CONAN_HOME}"
