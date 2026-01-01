#!/usr/bin/env bash
set -euo pipefail

if ! command -v glslangValidator >/dev/null 2>&1; then
  echo "glslangValidator not found in PATH." >&2
  exit 1
fi

root_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
shader_dir="${root_dir}/shader"

mapfile -t shader_files < <(
  rg --files \
    -g '*.vert' -g '*.frag' -g '*.comp' -g '*.geom' -g '*.tesc' -g '*.tese' \
    "${shader_dir}"
)

if [[ ${#shader_files[@]} -eq 0 ]]; then
  echo "No shader sources found under ${shader_dir}." >&2
  exit 1
fi

for shader in "${shader_files[@]}"; do
  out="${shader}.spv"
  glslangValidator -G --target-env opengl --auto-map-locations --auto-map-bindings \
    -I"${shader_dir}" -o "${out}" "${shader}"
done

echo "SPIR-V compile complete."
