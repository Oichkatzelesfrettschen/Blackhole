#!/bin/sh
# make_cinematic.sh -- Render the Blackhole cinematic video from scratch.
#
# WHY: Orchestrates the full pipeline: build -> record frames -> download
#      CC-BY audio -> find best 3-minute segment -> compose final MP4.
#
# WHAT: Produces blackhole_cinematic.mp4 at 1920x1080 @ 60fps with
#       the physics HUD overlay and an Interstellar-style CC-BY soundtrack.
#
# HOW:  ./scripts/make_cinematic.sh [--skip-build] [--skip-record]
#         --skip-build    Use existing binary (assumes build/Release/Blackhole exists).
#         --skip-record   Use existing frames in /tmp/bh_frames (skip rendering).
#         --frames N      Override total frame count (default: full 10800 = 3 min).
#         --output FILE   Override output path (default: blackhole_cinematic.mp4).
#
# Requirements: cmake, make, ffmpeg, yt-dlp or wget, python3 (for loudness analysis)
#
# Audio: "Echoes of Time v2" by Kevin MacLeod -- CC-BY 4.0 / Incompetech
#        Chosen for its slow, vast orchestral build matching the cinematic tempo.
#        If unavailable, falls back to a 3-minute slice of any suitable CC file.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"
BUILD_DIR="$REPO_DIR/build/Release"
BINARY="$BUILD_DIR/Blackhole"
FRAMES_DIR="/tmp/bh_frames"
OUTPUT="blackhole_cinematic.mp4"
AUDIO_DIR="/tmp/bh_audio"
TOTAL_FRAMES=10800   # 180 s * 60 fps
FPS=60

# ---- Parse arguments --------------------------------------------------------

SKIP_BUILD=0
SKIP_RECORD=0

for arg in "$@"; do
    case "$arg" in
        --skip-build)   SKIP_BUILD=1  ;;
        --skip-record)  SKIP_RECORD=1 ;;
        --frames)       shift; TOTAL_FRAMES="$1" ;;
        --output)       shift; OUTPUT="$1" ;;
        --help|-h)
            sed -n '2,/^[^#]/p' "$0" | grep '^#' | sed 's/^# \{0,2\}//'
            exit 0
            ;;
    esac
done

DURATION_S=$(( TOTAL_FRAMES / FPS ))

echo "=== Blackhole Cinematic Pipeline ==="
echo "  Frames  : $TOTAL_FRAMES  ($DURATION_S s @ ${FPS} fps)"
echo "  Output  : $OUTPUT"
echo ""

# ---- Step 1: Build ----------------------------------------------------------

if [ "$SKIP_BUILD" -eq 0 ]; then
    echo "--- Step 1: Build (Release) ---"
    cd "$REPO_DIR"
    if [ -f scripts/conan_install.sh ]; then
        sh scripts/conan_install.sh Release build
    fi
    cmake --preset release -DENABLE_CUDA=ON 2>&1 | tail -5
    cmake --build --preset release -- -j"$(nproc)" 2>&1 | tail -10
    echo "Build OK: $BINARY"
else
    echo "--- Step 1: Skipping build (--skip-build) ---"
    if [ ! -x "$BINARY" ]; then
        echo "ERROR: Binary not found: $BINARY" >&2
        exit 1
    fi
fi

# ---- Step 2: Record frames --------------------------------------------------

if [ "$SKIP_RECORD" -eq 0 ]; then
    echo ""
    echo "--- Step 2: Record $TOTAL_FRAMES frames into $FRAMES_DIR ---"
    mkdir -p "$FRAMES_DIR"
    # Remove any stale frames from a previous run
    rm -f "$FRAMES_DIR"/frame_*.png

    cd "$REPO_DIR"
    "$BINARY" --record-frames "$FRAMES_DIR" "$TOTAL_FRAMES"
    CAPTURED=$(ls "$FRAMES_DIR"/frame_*.png 2>/dev/null | wc -l)
    echo "Captured $CAPTURED frames."
    if [ "$CAPTURED" -lt "$TOTAL_FRAMES" ]; then
        echo "WARNING: Expected $TOTAL_FRAMES frames but only found $CAPTURED." >&2
    fi
else
    echo "--- Step 2: Skipping record (--skip-record), using $FRAMES_DIR ---"
    CAPTURED=$(ls "$FRAMES_DIR"/frame_*.png 2>/dev/null | wc -l)
    echo "Found $CAPTURED existing frames."
fi

# ---- Step 3: Download CC-BY audio -------------------------------------------

echo ""
echo "--- Step 3: Download CC-BY soundtrack ---"
mkdir -p "$AUDIO_DIR"

# Primary: Kevin MacLeod "Echoes of Time v2" from Incompetech (CC-BY 4.0).
# The direct URL is from incompetech.com -- always free for download.
AUDIO_URL="https://incompetech.com/music/royalty-free/mp3-royaltyfree/Echoes%20of%20Time%20v2.mp3"
AUDIO_RAW="$AUDIO_DIR/echoes_of_time_v2.mp3"
AUDIO_TRIMMED="$AUDIO_DIR/audio_trimmed.wav"

if [ ! -f "$AUDIO_RAW" ]; then
    echo "  Downloading Kevin MacLeod - Echoes of Time v2 (CC-BY 4.0)..."
    if command -v wget >/dev/null 2>&1; then
        wget -q -O "$AUDIO_RAW" "$AUDIO_URL" || AUDIO_RAW=""
    elif command -v curl >/dev/null 2>&1; then
        curl -sSL -o "$AUDIO_RAW" "$AUDIO_URL" || AUDIO_RAW=""
    else
        echo "  WARNING: neither wget nor curl found; skipping audio." >&2
        AUDIO_RAW=""
    fi
fi

# Fall back: "Impact Moderato" by Kevin MacLeod -- shorter, still epic.
if [ -z "${AUDIO_RAW:-}" ] || [ ! -s "${AUDIO_RAW:-/dev/null}" ]; then
    FALLBACK_URL="https://incompetech.com/music/royalty-free/mp3-royaltyfree/Impact%20Moderato.mp3"
    AUDIO_RAW="$AUDIO_DIR/impact_moderato.mp3"
    echo "  Primary download failed; trying fallback: Impact Moderato..."
    if command -v wget >/dev/null 2>&1; then
        wget -q -O "$AUDIO_RAW" "$FALLBACK_URL" || AUDIO_RAW=""
    elif command -v curl >/dev/null 2>&1; then
        curl -sSL -o "$AUDIO_RAW" "$FALLBACK_URL" || AUDIO_RAW=""
    fi
fi

# ---- Step 4: Find the best (loudest / most dynamic) segment -----------------

AUDIO_ARGS=""
if [ -n "${AUDIO_RAW:-}" ] && [ -s "${AUDIO_RAW:-/dev/null}" ]; then
    echo "  Finding best $DURATION_S s segment (loudness scan)..."

    # Use ffmpeg to dump loudness samples; pick the window with max mean loudness.
    # This is a shell-based sliding window over per-second LUFS measurements.
    LUFS_FILE="$AUDIO_DIR/loudness.txt"
    ffmpeg -i "$AUDIO_RAW" -af "ebur128=framelog=verbose" -f null - 2>"$LUFS_FILE" || true

    # Identify total audio duration
    AUDIO_DURATION=$(ffprobe -v error -show_entries format=duration \
        -of default=noprint_wrappers=1:nokey=1 "$AUDIO_RAW" 2>/dev/null || echo "180")
    AUDIO_DURATION_INT=$(printf "%.0f" "$AUDIO_DURATION")

    BEST_START=0
    if [ "$AUDIO_DURATION_INT" -gt "$DURATION_S" ] && command -v python3 >/dev/null 2>&1; then
        BEST_START=$(python3 - <<'PYEOF'
import sys, re

# Parse ffmpeg ebur128 momentary loudness lines: "M: -23.4"
lufs_file = "/tmp/bh_audio/loudness.txt"
vals = []
try:
    with open(lufs_file) as f:
        for line in f:
            m = re.search(r'M:\s+([-\d.]+)', line)
            if m:
                v = float(m.group(1))
                if v > -70:   # ignore silence
                    vals.append(v)
except Exception:
    pass

if not vals:
    print(0)
    sys.exit(0)

window = 180   # seconds; each value ~= 1 measurement per 100 ms so scale:
# ffmpeg ebur128 with framelog=verbose emits ~10 measurements/s
fps_meas = 10
W = window * fps_meas
if len(vals) < W:
    print(0)
    sys.exit(0)

best_sum = sum(vals[:W])
best_i   = 0
cur_sum  = best_sum
for i in range(1, len(vals) - W):
    cur_sum += vals[i + W - 1] - vals[i - 1]
    if cur_sum > best_sum:
        best_sum = cur_sum
        best_i   = i

best_start_s = best_i / fps_meas
print(int(best_start_s))
PYEOF
        )
    fi

    echo "  Best start: ${BEST_START} s  (duration: ${DURATION_S} s)"

    # Trim + loudness-normalize to -16 LUFS (cinematic broadcast level)
    ffmpeg -y -i "$AUDIO_RAW" \
        -ss "$BEST_START" -t "$DURATION_S" \
        -af "loudnorm=I=-16:LRA=11:TP=-1.5" \
        "$AUDIO_TRIMMED" 2>/dev/null
    AUDIO_ARGS="-i $AUDIO_TRIMMED"
    echo "  Audio ready: $AUDIO_TRIMMED"
else
    echo "  Audio unavailable; compositing video only (no audio)."
fi

# ---- Step 5: Compose final MP4 with ffmpeg ----------------------------------

echo ""
echo "--- Step 5: Compositing $OUTPUT ---"

# Build ffmpeg command
# Input 0: PNG frame sequence
# Input 1: audio (if available)
# Video: h264_nvenc (NVENC) preferred; fallback to libx264.
# Audio: AAC 320k stereo
# Metadata: attribution for Kevin MacLeod CC-BY

FRAME_PATTERN="$FRAMES_DIR/frame_%06d.png"

# Detect NVENC
NVENC_OK=0
if ffmpeg -hide_banner -encoders 2>/dev/null | grep -q h264_nvenc; then
    if ffmpeg -f lavfi -i "nullsrc=s=16x16:r=1" -t 0.1 -c:v h264_nvenc \
            -f null - >/dev/null 2>&1; then
        NVENC_OK=1
        echo "  Encoder: h264_nvenc (NVENC)"
    fi
fi
if [ "$NVENC_OK" -eq 0 ]; then
    echo "  Encoder: libx264 (NVENC unavailable)"
fi

if [ "$NVENC_OK" -eq 1 ]; then
    VIDEO_FLAGS="-c:v h264_nvenc -preset p7 -rc vbr -cq 18 -b:v 0 -maxrate 50M -bufsize 100M -pix_fmt yuv420p -profile:v high"
else
    VIDEO_FLAGS="-c:v libx264 -profile:v high -crf 18 -preset slow -pix_fmt yuv420p"
fi

if [ -n "$AUDIO_ARGS" ]; then
    # shellcheck disable=SC2086
    ffmpeg -y \
        -framerate "$FPS" -i "$FRAME_PATTERN" \
        $AUDIO_ARGS \
        -map 0:v -map 1:a \
        $VIDEO_FLAGS \
        -c:a aac -b:a 320k -ac 2 \
        -shortest \
        -movflags +faststart \
        -metadata title="Blackhole Cinematic" \
        -metadata artist="Kevin MacLeod (incompetech.com) CC-BY 4.0" \
        -metadata comment="Rendered with Blackhole (github.com/eirikr/Blackhole)" \
        "$OUTPUT"
else
    # shellcheck disable=SC2086
    ffmpeg -y \
        -framerate "$FPS" -i "$FRAME_PATTERN" \
        $VIDEO_FLAGS \
        -movflags +faststart \
        -metadata title="Blackhole Cinematic" \
        -metadata comment="Rendered with Blackhole (github.com/eirikr/Blackhole)" \
        "$OUTPUT"
fi

echo ""
echo "=== Done ==="
echo "  Output : $OUTPUT"
if command -v ffprobe >/dev/null 2>&1; then
    ffprobe -v error -show_entries format=duration,size \
        -of default=noprint_wrappers=1 "$OUTPUT" 2>/dev/null || true
fi
echo ""
echo "  ATTRIBUTION (required by CC-BY 4.0):"
echo "  Music: Kevin MacLeod (incompetech.com)"
echo "  Licensed under Creative Commons: By Attribution 4.0 License"
echo "  http://creativecommons.org/licenses/by/4.0/"
