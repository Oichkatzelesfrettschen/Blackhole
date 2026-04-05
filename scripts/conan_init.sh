#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

conan --version
conan profile detect --force

CLANG_VERSION_RAW="$(clang++ -dumpfullversion -dumpversion 2>/dev/null || true)"
if [[ -z "${CLANG_VERSION_RAW}" ]]; then
  echo "ERROR: clang++ is required by scripts/conan_init.sh but was not found in PATH." >&2
  exit 2
fi
CLANG_VERSION_MAJOR="${CLANG_VERSION_RAW%%.*}"
CONAN_MAX_CLANG_VERSION=21
PROFILE_CLANG_VERSION="${CLANG_VERSION_MAJOR}"
if (( CLANG_VERSION_MAJOR > CONAN_MAX_CLANG_VERSION )); then
  echo "WARN: Conan settings only recognize clang ${CONAN_MAX_CLANG_VERSION} in this repo-local home; local clang is ${CLANG_VERSION_RAW}. Using compiler.version=${CONAN_MAX_CLANG_VERSION} for profile compatibility." >&2
  PROFILE_CLANG_VERSION="${CONAN_MAX_CLANG_VERSION}"
fi

# Enforce clang + C++23 in the repo-local default profile.
PROFILE_PATH="${CONAN_HOME}/profiles/default"
cat > "${PROFILE_PATH}" <<EOF
[settings]
arch=x86_64
build_type=Release
compiler=clang
compiler.cppstd=23
compiler.libcxx=libstdc++11
compiler.version=${PROFILE_CLANG_VERSION}
os=Linux
[conf]
tools.build:compiler_executables={"c":"clang","cpp":"clang++"}
[buildenv]
CC=clang
CXX=clang++
EOF
conan remote update conancenter --url="https://center2.conan.io"
conan remote list
