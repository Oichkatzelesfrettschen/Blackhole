#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CONAN_HOME="${ROOT}/.conan"
export CONAN_USER_HOME="${ROOT}/.conan"

conan --version
conan profile detect --force
conan remote update conancenter --url="https://center2.conan.io"
conan remote list
