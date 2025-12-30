#!/usr/bin/env bash
set -euo pipefail

implot_dir="${1:-external/implot}"
base_url="https://raw.githubusercontent.com/epezent/implot/master"

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

echo "Fetched ImPlot sources into ${implot_dir}"
