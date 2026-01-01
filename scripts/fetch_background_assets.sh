#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${OUT_DIR:-${ROOT}/assets/backgrounds/source}"
MANIFEST="${OUT_DIR}/manifest.sha256"

usage() {
  cat <<'USAGE'
Usage: scripts/fetch_background_assets.sh [--small] [--full]

--small  Download smaller 2K/4K assets only (default).
--full   Download the full list (includes very large files).
OUT_DIR  Override output directory (default: assets/backgrounds/source).
USAGE
}

mode="small"
case "${1:-}" in
  --full) mode="full" ;;
  --small|"") mode="small" ;;
  -h|--help) usage; exit 0 ;;
  *) usage; exit 2 ;;
esac

mkdir -p "$OUT_DIR"
touch "$MANIFEST"

fetch() {
  local name="$1"
  local url="$2"
  local out="${OUT_DIR}/${name}"
  if [[ -f "$out" ]]; then
    echo "[skip] $name"
    return
  fi
  echo "[get]  $name"
  curl -L --fail --retry 3 --retry-delay 2 -o "$out" "$url"
  sha256sum "$out" >> "$MANIFEST"
}

# Small set (2K/4K)
ASSETS_SMALL=(
  "PIA22085_5120x2880.jpg|http://images-assets.nasa.gov/image/PIA22085/PIA22085~orig.jpg"
  "PIA15415_6000x6000.jpg|http://images-assets.nasa.gov/image/PIA15415/PIA15415~orig.jpg"
  "heic1509a_publication_4k.jpg|https://cdn.esahubble.org/archives/images/publicationjpg/heic1509a.jpg"
  "heic1402a_publication_4k.jpg|https://cdn.esahubble.org/archives/images/publicationjpg/heic1402a.jpg"
  "jaxa_hayabusa2_main_001.jpg|https://global.jaxa.jp/projects/sas/hayabusa2/images/hayabusa2_main_001.jpg"
)

# Full set (includes large downloads)
ASSETS_FULL=(
  "${ASSETS_SMALL[@]}"
  "PIA15416_9400x7000.jpg|http://images-assets.nasa.gov/image/PIA15416/PIA15416~orig.jpg"
  "PIA08506_14772x4953.jpg|http://images-assets.nasa.gov/image/PIA08506/PIA08506~orig.jpg"
  "heic1509a_large.jpg|https://cdn.esahubble.org/archives/images/large/heic1509a.jpg"
  "heic1402a_large.jpg|https://cdn.esahubble.org/archives/images/large/heic1402a.jpg"
)

if [[ "$mode" == "full" ]]; then
  assets=("${ASSETS_FULL[@]}")
else
  assets=("${ASSETS_SMALL[@]}")
fi

for item in "${assets[@]}"; do
  name="${item%%|*}"
  url="${item##*|}"
  fetch "$name" "$url"
done

echo "[done] Assets in ${OUT_DIR}"
