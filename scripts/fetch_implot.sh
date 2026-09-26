#!/usr/bin/env bash
set -euo pipefail

# ImPlot is vendored from a pinned upstream commit so re-fetches are
# byte-stable; raw.githubusercontent.com content is immutable per
# commit. Bump the pin deliberately and rebuild to upgrade.
# 0.18 WIP, master 2026-07 (ImGui 1.92 docking API compatible).
implot_commit="d65a2bef53d32502407de3a4be80f191e2f412d7"

implot_dir="${1:-external/implot}"
base_url="https://raw.githubusercontent.com/epezent/implot/${implot_commit}"

mkdir -p "${implot_dir}"

files=(
  implot.h
  implot_internal.h
  implot.cpp
  implot_items.cpp
  implot_demo.cpp
  LICENSE
)

for file in "${files[@]}"; do
  curl -fsSL "${base_url}/${file}" -o "${implot_dir}/${file}"
done

echo "Fetched ImPlot @ ${implot_commit} into ${implot_dir}"
sha256sum "${implot_dir}"/implot*.h "${implot_dir}"/implot*.cpp "${implot_dir}/LICENSE"
