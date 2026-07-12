#!/bin/sh
# Generate the campaign nebula resolution ladder from the 4K LFS source.
#
# The 4K JPEG under assets/backgrounds/source/ is the single committed source of
# truth; every runtime rendition is derived from it here (never committed), so
# the ladder is reproducible and the repository carries one image, not seven.
#
# Usage: generate_nebula_ladder.sh <source-4k.jpg> <output-dir> [magick]
set -eu

SRC="$1"
OUT="$2"
MAGICK="${3:-magick}"

mkdir -p "$OUT"

# 16:9-ish renditions (the source's native aspect), width-fit.
"$MAGICK" "$SRC" -resize 2048x -quality 90 "$OUT/carina-cosmic-cliffs-2k.jpg"
"$MAGICK" "$SRC" -resize 1920x -quality 88 "$OUT/carina-cosmic-cliffs-1080.jpg"
"$MAGICK" "$SRC" -resize 1280x -quality 88 "$OUT/carina-cosmic-cliffs-720.jpg"
"$MAGICK" "$SRC" -resize 1024x -quality 88 "$OUT/carina-cosmic-cliffs-1024.jpg"
"$MAGICK" "$SRC" -resize 512x -quality 85 "$OUT/carina-cosmic-cliffs-512.jpg"

# 21:9 ultrawide: fill the width then centre-crop the height.
"$MAGICK" "$SRC" -resize 3440x -gravity center -extent 3440x1440 -quality 90 \
  "$OUT/carina-cosmic-cliffs-2k-ultrawide.jpg"
