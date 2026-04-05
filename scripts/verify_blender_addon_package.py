#!/usr/bin/env python3
"""Verify the packaged Blender addon zip and emit a machine-readable report."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import pathlib
import zipfile
from typing import Any


REQUIRED_FILES = (
    "blackhole_physics/__init__.py",
    "blackhole_physics/bridge.py",
    "blackhole_physics/operators.py",
    "blackhole_physics/panels.py",
    "blackhole_physics/materials.py",
    "blackhole_physics/render_engine.py",
    "blackhole_physics/asset_library/blender_assets.cats.txt",
)

BANNED_PARTS = {"__pycache__"}
BANNED_SUFFIXES = {".pyc", ".pyo", ".tmp", ".swp"}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--addon-zip", required=True, type=pathlib.Path)
    parser.add_argument("--manifest", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    return parser.parse_args()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def extract_bl_info(source_text: str) -> dict[str, Any]:
    module = ast.parse(source_text)
    for node in module.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == "bl_info":
                    return ast.literal_eval(node.value)
    raise RuntimeError("bl_info not found in addon __init__.py")


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Blender Addon Package Report",
        "",
        f"- Addon zip: `{report['addon_zip']}`",
        f"- Zip sha256: `{report['zip_sha256']}`",
        f"- File count: `{report['file_count']}`",
        f"- Addon name: `{report['bl_info']['name']}`",
        f"- Addon version: `{report['bl_info']['version']}`",
        f"- Blender minimum: `{report['bl_info']['blender']}`",
        "",
        "## Required Files",
        "",
    ]
    for path in REQUIRED_FILES:
        lines.append(f"- `{path}`")
    lines.append("")
    lines.append("## Banned Files")
    lines.append("")
    if report["banned_files"]:
        for path in report["banned_files"]:
            lines.append(f"- `{path}`")
    else:
        lines.append("- None")
    lines.append("")
    return "\n".join(lines).strip() + "\n"


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> int:
    args = parse_args()
    addon_zip = args.addon_zip.resolve()
    manifest_path = args.manifest.resolve() if args.manifest else None
    if not addon_zip.exists():
        raise SystemExit(f"Addon zip not found: {addon_zip}")

    with zipfile.ZipFile(addon_zip) as zf:
        names = sorted(info.filename for info in zf.infolist() if not info.is_dir())
        missing = [path for path in REQUIRED_FILES if path not in names]
        banned = []
        for name in names:
            parts = pathlib.PurePosixPath(name).parts
            suffix = pathlib.PurePosixPath(name).suffix
            if any(part in BANNED_PARTS for part in parts) or suffix in BANNED_SUFFIXES:
                banned.append(name)
        init_text = zf.read("blackhole_physics/__init__.py").decode("utf-8")
        bl_info = extract_bl_info(init_text)

    manifest_data = None
    if manifest_path is not None:
        if not manifest_path.exists():
            raise SystemExit(f"Addon manifest not found: {manifest_path}")
        manifest_data = json.loads(manifest_path.read_text(encoding="utf-8"))

    report = {
        "addon_zip": str(addon_zip),
        "zip_sha256": sha256_file(addon_zip),
        "file_count": len(names),
        "files": names,
        "missing_files": missing,
        "banned_files": banned,
        "bl_info": bl_info,
        "manifest": manifest_data,
    }

    if manifest_data is not None:
        manifest_zip_sha = manifest_data.get("zip_sha256", "")
        if manifest_zip_sha and manifest_zip_sha != report["zip_sha256"]:
            raise SystemExit(
                f"Addon manifest sha256 mismatch: manifest={manifest_zip_sha} zip={report['zip_sha256']}"
            )
        manifest_files = [entry["path"] for entry in manifest_data.get("files", [])]
        if manifest_files and manifest_files != names:
            raise SystemExit("Addon manifest file list does not match packaged zip contents")

    if missing:
        raise SystemExit(f"Addon package is missing required files: {', '.join(missing)}")
    if banned:
        raise SystemExit(f"Addon package contains banned files: {', '.join(banned)}")

    write_text(args.json_out, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
