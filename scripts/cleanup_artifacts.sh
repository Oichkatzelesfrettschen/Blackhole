#!/bin/sh
# cleanup_artifacts.sh - Safe automated cleanup of build artifacts and orphaned files
# WHY: Recover 5-8GB disk space by removing build artifacts, profiling data, and orphaned files
# WHAT: Archives perf.data, removes old builds, prunes logs, converts PPM to PNG
# HOW: Run with --dry-run to preview, without to execute

set -eu

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

DRY_RUN=false
if [ "${1:-}" = "--dry-run" ]; then
    DRY_RUN=true
    echo "DRY RUN MODE - No changes will be made"
    echo "============================================"
fi

# Helper function for dry-run aware operations
safe_rm() {
    if [ "$DRY_RUN" = true ]; then
        echo "[DRY-RUN] Would remove: $*"
    else
        rm -rf "$@"
        echo "Removed: $*"
    fi
}

safe_mv() {
    if [ "$DRY_RUN" = true ]; then
        echo "[DRY-RUN] Would move: $1 -> $2"
    else
        mkdir -p "$(dirname "$2")"
        mv "$1" "$2"
        echo "Moved: $1 -> $2"
    fi
}

echo "Blackhole Repository Cleanup"
echo "============================================"
echo ""

# 1. Archive perf.data to logs/archive/profiling/2026-01/
if [ -f perf.data ]; then
    echo "Step 1: Archiving perf.data (482MB)..."
    ARCHIVE_DIR="logs/archive/profiling/$(date +%Y-%m)"
    safe_mv perf.data "$ARCHIVE_DIR/perf.data"
else
    echo "Step 1: perf.data not found (already archived or removed)"
fi

# 2. Remove perf.data.old, gmon.out, mydatabase.db
echo ""
echo "Step 2: Removing orphaned files..."
for file in perf.data.old gmon.out mydatabase.db; do
    if [ -f "$file" ]; then
        SIZE=$(du -h "$file" | cut -f1)
        safe_rm "$file"
        echo "  Freed: $SIZE"
    else
        echo "  $file not found (already removed)"
    fi
done

# 3. Remove build-asan/ and build_asan/ directories
echo ""
echo "Step 3: Removing old build directories..."
for dir in build-asan build_asan; do
    if [ -d "$dir" ]; then
        SIZE=$(du -sh "$dir" | cut -f1)
        safe_rm "$dir"
        echo "  Freed: $SIZE"
    else
        echo "  $dir not found (already removed)"
    fi
done

# 4. Remove src/physics/physics_test binary
echo ""
echo "Step 4: Removing misplaced test binaries..."
if [ -f src/physics/physics_test ]; then
    safe_rm src/physics/physics_test
else
    echo "  src/physics/physics_test not found"
fi

# 5. Remove duplicate claude.md
echo ""
echo "Step 5: Removing duplicate documentation..."
if [ -f claude.md ]; then
    safe_rm claude.md
else
    echo "  claude.md not found (already removed)"
fi

# 6. Prune logs/archive/ (keep last 5 snapshots)
echo ""
echo "Step 6: Pruning log archives (keeping last 5 snapshots)..."
if [ -d logs/archive ]; then
    # Count snapshots
    SNAPSHOT_COUNT=$(find logs/archive -mindepth 1 -maxdepth 1 -type d | wc -l)
    echo "  Found $SNAPSHOT_COUNT snapshot directories"

    if [ "$SNAPSHOT_COUNT" -gt 5 ]; then
        REMOVE_COUNT=$((SNAPSHOT_COUNT - 5))
        echo "  Will remove $REMOVE_COUNT oldest snapshots"

        if [ "$DRY_RUN" = true ]; then
            find logs/archive -mindepth 1 -maxdepth 1 -type d | sort | head -n "$REMOVE_COUNT" | while read -r dir; do
                SIZE=$(du -sh "$dir" | cut -f1)
                echo "  [DRY-RUN] Would remove: $dir ($SIZE)"
            done
        else
            find logs/archive -mindepth 1 -maxdepth 1 -type d | sort | head -n "$REMOVE_COUNT" | while read -r dir; do
                SIZE=$(du -sh "$dir" | cut -f1)
                rm -rf "$dir"
                echo "  Removed: $dir ($SIZE)"
            done
        fi
    else
        echo "  Snapshot count within limit (5), no pruning needed"
    fi
else
    echo "  logs/archive not found"
fi

# 7. Convert PPM to PNG in logs/compare/ (90% size reduction)
echo ""
echo "Step 7: Converting PPM to PNG in logs/compare/..."
if [ -d logs/compare ]; then
    PPM_COUNT=$(find logs/compare -name "*.ppm" -type f 2>/dev/null | wc -l)

    if [ "$PPM_COUNT" -gt 0 ]; then
        echo "  Found $PPM_COUNT PPM files"

        # Check if ImageMagick convert is available
        if command -v convert >/dev/null 2>&1; then
            if [ "$DRY_RUN" = true ]; then
                find logs/compare -name "*.ppm" -type f | while read -r ppm; do
                    SIZE=$(du -h "$ppm" | cut -f1)
                    echo "  [DRY-RUN] Would convert: $ppm ($SIZE)"
                done
            else
                find logs/compare -name "*.ppm" -type f | while read -r ppm; do
                    png="${ppm%.ppm}.png"
                    SIZE_BEFORE=$(du -h "$ppm" | cut -f1)
                    convert "$ppm" "$png"
                    SIZE_AFTER=$(du -h "$png" | cut -f1)
                    rm -f "$ppm"
                    echo "  Converted: $(basename "$ppm") ($SIZE_BEFORE -> $SIZE_AFTER)"
                done
            fi
        else
            echo "  WARNING: ImageMagick 'convert' not found, skipping conversion"
            echo "  Install with: sudo pacman -S imagemagick"
        fi
    else
        echo "  No PPM files found"
    fi
else
    echo "  logs/compare not found"
fi

# Summary
echo ""
echo "============================================"
echo "Cleanup complete!"
echo ""
echo "Estimated space recovered:"
echo "  perf.data: ~482MB (archived)"
echo "  perf.data.old: ~784MB"
echo "  gmon.out: ~1.7MB"
echo "  build-asan/: ~16MB"
echo "  build_asan/: ~332KB"
echo "  Old log snapshots: ~1-2GB (if applicable)"
echo "  PPM to PNG conversion: ~90% of PPM total"
echo ""
echo "Total estimated recovery: 5-8GB"
echo ""
echo "Verify with: du -sh .conan build logs"
