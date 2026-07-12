#!/usr/bin/env python3
"""Audit background asset provenance.

Walks assets/backgrounds/manifest.json and prints each asset's declared title
beside the image's own EXIF ImageDescription, so a mismatch between the label
and the actual content is visible at a glance. Ground truth is the description
the publishing agency embedded in the file; see
docs/validation/asset-provenance-audit.md for the method and the findings.

Usage: python3 scripts/audit_asset_provenance.py
"""
import json
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST = REPO_ROOT / "assets/backgrounds/manifest.json"


def describe(path: Path) -> str:
    """Return the image's EXIF ImageDescription, or a marker for the cases that
    have none (a pointer that was never fetched, a missing file, no EXIF)."""
    if not path.exists():
        return "<file-missing>"
    if path.read_bytes()[:24] == b"version https://git-lfs\n"[:24]:
        return "<lfs-pointer-unfetched>"
    try:
        result = subprocess.run(
            ["identify", "-format", "%[EXIF:ImageDescription]", str(path)],
            capture_output=True, text=True, timeout=20, check=False,
        )
        return result.stdout.strip()[:100] or "<no-EXIF-description>"
    except (OSError, subprocess.SubprocessError) as exc:
        return f"<identify-error: {exc}>"


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    print(f"{'ID':<32} {'TITLE':<40} CONTENT (EXIF)")
    print("-" * 120)
    for asset in manifest.get("assets", []):
        path_str = asset.get("path", "")
        if not path_str:
            continue
        content = describe(REPO_ROOT / path_str)
        print(f"{asset.get('id', ''):<32} {asset.get('title', ''):<40} {content}")


if __name__ == "__main__":
    main()
