#!/bin/sh
# Generate a campaign nebula resolution ladder from one high-resolution source.
#
# The source JPEG under assets/backgrounds/source/ is the single committed source
# of truth for a backdrop; every runtime rendition is derived from it here (never
# committed), so each ladder is reproducible and the repository carries one image
# per backdrop, not seven. The output base name is derived from the source file
# name (its "-4k" and extension stripped), so the same script serves every
# source: crab-nebula-4k.jpg -> crab-nebula-{2k,1080,720,1024,512,ultrawide-*}.jpg.
#
# Usage: generate_nebula_ladder.sh <source.jpg> <output-dir> [magick]
set -eu

SRC="$1"
OUT="$2"
MAGICK="${3:-magick}"

# Base name = source file name without directory, extension, or trailing -4k.
BASE=$(basename "$SRC")
BASE=${BASE%.jpg}
BASE=${BASE%.jpeg}
BASE=${BASE%-4k}

mkdir -p "$OUT"

# 16:9-ish renditions (the source's native aspect), width-fit.
"$MAGICK" "$SRC" -resize 2048x -quality 90 "$OUT/$BASE-2k.jpg"
"$MAGICK" "$SRC" -resize 1920x -quality 88 "$OUT/$BASE-1080.jpg"
"$MAGICK" "$SRC" -resize 1280x -quality 88 "$OUT/$BASE-720.jpg"
"$MAGICK" "$SRC" -resize 1024x -quality 88 "$OUT/$BASE-1024.jpg"
"$MAGICK" "$SRC" -resize 512x -quality 85 "$OUT/$BASE-512.jpg"

# 21:9 ultrawide renditions: fill the width then centre-crop the height. Both
# common "2K ultrawide" sizes -- UWQHD (3440x1440) and UW-FHD (2560x1080).
"$MAGICK" "$SRC" -resize 3440x -gravity center -extent 3440x1440 -quality 90 \
  "$OUT/$BASE-ultrawide-3440x1440.jpg"
"$MAGICK" "$SRC" -resize 2560x -gravity center -extent 2560x1080 -quality 90 \
  "$OUT/$BASE-ultrawide-2560x1080.jpg"
