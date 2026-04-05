#!/usr/bin/env python3
"""Package the canonical Blender addon tree into a reproducible zip archive."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import zipfile


FIXED_ZIP_TIMESTAMP = (2020, 1, 1, 0, 0, 0)
BANNED_PARTS = {"__pycache__"}
BANNED_SUFFIXES = {".pyc", ".pyo", ".tmp", ".swp"}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--manifest-out")
    return parser


def should_package(path: pathlib.Path, addon_dir: pathlib.Path) -> bool:
    rel = path.relative_to(addon_dir)
    if any(part in BANNED_PARTS for part in rel.parts):
        return False
    if path.suffix in BANNED_SUFFIXES:
        return False
    return True


def sha256_bytes(data: bytes) -> str:
    digest = hashlib.sha256()
    digest.update(data)
    return digest.hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    addon_dir = source_dir / "blender" / "addon" / "blackhole_physics"
    output_path = pathlib.Path(args.output).resolve()
    manifest_path = pathlib.Path(args.manifest_out).resolve() if args.manifest_out else None

    if not addon_dir.exists():
        raise SystemExit(f"Canonical addon directory not found: {addon_dir}")

    file_entries = []
    for path in sorted(addon_dir.rglob("*")):
        if path.is_dir() or not should_package(path, addon_dir):
            continue
        rel = path.relative_to(addon_dir)
        arcname = pathlib.PurePosixPath("blackhole_physics") / pathlib.PurePosixPath(rel.as_posix())
        data = path.read_bytes()
        file_entries.append(
            {
                "path": arcname.as_posix(),
                "size": len(data),
                "sha256": sha256_bytes(data),
                "data": data,
            }
        )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output_path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for entry in file_entries:
            info = zipfile.ZipInfo(entry["path"], date_time=FIXED_ZIP_TIMESTAMP)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            zf.writestr(info, entry["data"])

    manifest = {
        "addon_root": "blackhole_physics",
        "file_count": len(file_entries),
        "files": [
            {
                "path": entry["path"],
                "size": entry["size"],
                "sha256": entry["sha256"],
            }
            for entry in file_entries
        ],
        "zip_path": str(output_path),
        "zip_sha256": sha256_file(output_path),
    }

    if manifest_path is not None:
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"Packaged Blender addon: {output_path}")
    if manifest_path is not None:
        print(f"Addon manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
