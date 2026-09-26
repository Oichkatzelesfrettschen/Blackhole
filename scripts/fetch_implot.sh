#!/usr/bin/env bash
set -euo pipefail

# ImPlot is vendored from a pinned upstream commit so re-fetches are
# byte-stable; raw.githubusercontent.com content is immutable per
# commit. Bump the pin deliberately and rebuild to upgrade.
# 0.18 WIP (upstream 2025-12-03, "fix: DragRect resizing when its size is
# zero"). Every file under external/implot is byte-identical to this commit;
# src/ui/panels.cpp uses its PlotLine(flags, offset) signature, which the 1.x
# ImPlotSpec API replaces.
implot_commit="81b8b1951392767cf458508385fa025fd087a252"

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
