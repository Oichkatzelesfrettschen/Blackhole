#!/usr/bin/env bash
# SPIR-V shader compiler with hash-based caching
# Uses spirv_bake for compilation/optimization, glslangValidator for preprocessing
# Computes SHA256 of preprocessed shader source (with includes) and caches compiled SPIR-V
set -euo pipefail

# glslangValidator for preprocessing (include resolution)
GLSLANG_VALIDATOR="${GLSLANG_VALIDATOR:-glslangValidator}"

root_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
shader_dir="${root_dir}/shader"
cache_dir="${SPIRV_CACHE_DIR:-${root_dir}/build/shader_cache}"

# Locate spirv_bake binary
SPIRV_BAKE="${SPIRV_BAKE:-${root_dir}/build/Release/spirv_bake}"
if [[ ! -x "${SPIRV_BAKE}" ]]; then
  SPIRV_BAKE="${root_dir}/build/Debug/spirv_bake"
fi

# Configuration flags
OPTIMIZE="${SPIRV_OPTIMIZE:-1}"
STRIP_DEBUG="${SPIRV_STRIP:-0}"
EMIT_REFLECTION="${SPIRV_REFLECT:-0}"
SKIP_OPT_COMPUTE="${SPIRV_SKIP_OPT_COMPUTE:-0}"  # Disable opt for compute shaders (FP precision testing)

if ! command -v "${GLSLANG_VALIDATOR}" >/dev/null 2>&1; then
  echo "Error: glslangValidator not found in PATH." >&2
  exit 1
fi

if [[ ! -x "${SPIRV_BAKE}" ]]; then
  echo "Warning: spirv_bake not found, falling back to glslangValidator only." >&2
  USE_SPIRV_BAKE=0
else
  USE_SPIRV_BAKE=1
  echo "Using spirv_bake: ${SPIRV_BAKE}"
fi
echo "Using glslangValidator: $(command -v ${GLSLANG_VALIDATOR})"

mkdir -p "${cache_dir}"

# Collect all shader source files
mapfile -t shader_files < <(
  find "${shader_dir}" -maxdepth 1 \
    \( -name '*.vert' -o -name '*.frag' -o -name '*.comp' \
       -o -name '*.geom' -o -name '*.tesc' -o -name '*.tese' \) \
    -type f | sort
)

if [[ ${#shader_files[@]} -eq 0 ]]; then
  echo "No shader sources found under ${shader_dir}." >&2
  exit 1
fi

# Preprocess shader and compute hash (resolves includes using glslangValidator -E)
compute_shader_hash() {
  local shader="$1"
  local stage=""
  case "${shader}" in
    *.vert) stage="vert" ;;
    *.frag) stage="frag" ;;
    *.comp) stage="comp" ;;
    *.geom) stage="geom" ;;
    *.tesc) stage="tesc" ;;
    *.tese) stage="tese" ;;
  esac

  # Preprocess to expand includes, then hash
  # -E flag outputs preprocessed source
  if "${GLSLANG_VALIDATOR}" -E -I"${shader_dir}" -I"${shader_dir}/include" \
      -S "${stage}" "${shader}" 2>/dev/null | sha256sum | cut -d' ' -f1; then
    return 0
  fi
  # Fallback: hash raw file if preprocessing fails
  sha256sum "${shader}" | cut -d' ' -f1
}

compiled=0
cached=0
failed=0

for shader in "${shader_files[@]}"; do
  basename="$(basename "${shader}")"
  out="${shader}.spv"

  # Compute hash of preprocessed source
  hash="$(compute_shader_hash "${shader}")"
  cached_spv="${cache_dir}/${basename%.glsl}-${hash:0:16}.spv"

  # Check cache
  if [[ -f "${cached_spv}" ]]; then
    # Cache hit - copy to output location
    cp "${cached_spv}" "${out}"
    echo "[CACHE] ${basename} -> ${basename}.spv (${hash:0:8}...)"
    ((cached++)) || true
    continue
  fi

  # Cache miss - compile
  echo "[BUILD] ${basename} -> ${basename}.spv"

  # Determine shader stage
  shader_stage=""
  case "${shader}" in
    *.vert) shader_stage="vert" ;;
    *.frag) shader_stage="frag" ;;
    *.comp) shader_stage="comp" ;;
    *.geom) shader_stage="geom" ;;
    *.tesc) shader_stage="tesc" ;;
    *.tese) shader_stage="tese" ;;
  esac

  if [[ "${USE_SPIRV_BAKE}" -eq 1 ]]; then
    # spirv_bake path: preprocess with glslangValidator, compile with spirv_bake
    preprocessed_tmp="${cache_dir}/.preprocessed_${basename}"

    # Preprocess to resolve includes
    if ! "${GLSLANG_VALIDATOR}" -E -I"${shader_dir}" -I"${shader_dir}/include" \
        -S "${shader_stage}" "${shader}" > "${preprocessed_tmp}" 2>&1; then
      echo "  FAILED preprocessing: ${basename}" >&2
      rm -f "${preprocessed_tmp}"
      ((failed++)) || true
      continue
    fi

    # Build spirv_bake command
    spirv_bake_args=("--stage" "${shader_stage}")
    # Skip optimization for compute shaders when testing FP precision
    should_opt=0
    if [[ "${OPTIMIZE}" -eq 1 ]]; then
      if [[ "${shader_stage}" == "comp" && "${SKIP_OPT_COMPUTE}" -eq 1 ]]; then
        echo "  [PRECISION] Skipping optimization for compute shader: ${basename}"
        should_opt=0
      else
        should_opt=1
      fi
    fi
    if [[ "${should_opt}" -eq 1 ]]; then
      spirv_bake_args+=("--opt")
    fi
    if [[ "${STRIP_DEBUG}" -eq 1 ]]; then
      spirv_bake_args+=("--strip")
    fi

    # Compile with spirv_bake
    if ! "${SPIRV_BAKE}" "${spirv_bake_args[@]}" "${preprocessed_tmp}" "${out}" 2>&1; then
      echo "  FAILED: ${basename}" >&2
      rm -f "${preprocessed_tmp}"
      ((failed++)) || true
      continue
    fi

    # Emit JSON reflection if requested
    if [[ "${EMIT_REFLECTION}" -eq 1 ]]; then
      reflect_json="${cache_dir}/${basename%.glsl}-reflect.json"
      # Recompile with reflection (uses already-preprocessed source)
      "${SPIRV_BAKE}" --stage "${shader_stage}" --reflect-json "${reflect_json}" \
          "${preprocessed_tmp}" "/dev/null" 2>/dev/null || true
    fi

    rm -f "${preprocessed_tmp}"
  else
    # Fallback: glslangValidator only
    if ! "${GLSLANG_VALIDATOR}" -G --target-env opengl \
        --auto-map-locations --auto-map-bindings \
        -I"${shader_dir}" -I"${shader_dir}/include" \
        -o "${out}" "${shader}" 2>&1; then
      echo "  FAILED: ${basename}" >&2
      ((failed++)) || true
      continue
    fi
  fi

  # Store in cache
  cp "${out}" "${cached_spv}"
  ((compiled++)) || true
done

echo ""
echo "=== SPIR-V Compile Summary ==="
echo "  Compiled: ${compiled}"
echo "  Cached:   ${cached}"
echo "  Failed:   ${failed}"
echo "  Cache:    ${cache_dir}"
if [[ "${USE_SPIRV_BAKE}" -eq 1 ]]; then
  echo "  Backend:  spirv_bake (shaderc + spirv-tools)"
  echo "  Optimize: $( [[ "${OPTIMIZE}" -eq 1 ]] && echo 'yes' || echo 'no' )"
  echo "  Strip:    $( [[ "${STRIP_DEBUG}" -eq 1 ]] && echo 'yes' || echo 'no' )"
  echo "  Reflect:  $( [[ "${EMIT_REFLECTION}" -eq 1 ]] && echo 'yes' || echo 'no' )"
else
  echo "  Backend:  glslangValidator (fallback)"
fi

if [[ ${failed} -gt 0 ]]; then
  exit 1
fi
