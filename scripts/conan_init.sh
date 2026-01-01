#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT}/scripts/conan_env.sh"

conan --version
conan profile detect --force

# Enforce clang + C++23 in the repo-local default profile.
PROFILE_PATH="${CONAN_HOME}/profiles/default"
cat > "${PROFILE_PATH}" <<'EOF'
[settings]
arch=x86_64
build_type=Release
compiler=clang
compiler.cppstd=23
compiler.libcxx=libstdc++11
compiler.version=21
os=Linux
[conf]
tools.build:compiler_executables={"c":"clang","cpp":"clang++"}
[buildenv]
CC=clang
CXX=clang++
EOF
conan remote update conancenter --url="https://center2.conan.io"
conan remote list
