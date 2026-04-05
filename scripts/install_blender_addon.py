#!/usr/bin/env python3
"""Install the packaged Blender addon zip into a target addon directory."""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import tempfile
import zipfile


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--addon-zip", required=True, type=pathlib.Path)
    parser.add_argument("--manifest", type=pathlib.Path)
    parser.add_argument("--user-scripts", type=pathlib.Path)
    parser.add_argument("--addon-dir", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def resolve_target_dir(args: argparse.Namespace) -> pathlib.Path:
    if args.addon_dir is not None and args.user_scripts is not None:
        raise SystemExit("Use either --addon-dir or --user-scripts, not both")
    if args.addon_dir is not None:
        return args.addon_dir.resolve()
    if args.user_scripts is not None:
        return (args.user_scripts.resolve() / "addons" / "blackhole_physics")
    raise SystemExit("Provide either --addon-dir or --user-scripts")


def validate_manifest(manifest_path: pathlib.Path, addon_zip: pathlib.Path) -> dict:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if pathlib.Path(manifest.get("zip_path", "")).name != addon_zip.name:
        raise SystemExit("Addon manifest zip path does not describe the selected zip")
    return manifest


def write_json(path: pathlib.Path | None, payload: dict) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    addon_zip = args.addon_zip.resolve()
    if not addon_zip.exists():
        raise SystemExit(f"Addon zip not found: {addon_zip}")
    target_dir = resolve_target_dir(args)
    manifest = None
    if args.manifest is not None:
        manifest_path = args.manifest.resolve()
        if not manifest_path.exists():
            raise SystemExit(f"Addon manifest not found: {manifest_path}")
        manifest = validate_manifest(manifest_path, addon_zip)

    if target_dir.exists():
        if not args.force:
            raise SystemExit(f"Target addon directory already exists: {target_dir}")
        shutil.rmtree(target_dir)

    target_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="blackhole_addon_install_") as tmp:
        temp_root = pathlib.Path(tmp)
        with zipfile.ZipFile(addon_zip) as zf:
            zf.extractall(temp_root)
        extracted_root = temp_root / "blackhole_physics"
        if not extracted_root.exists():
            raise SystemExit("Packaged addon zip did not contain blackhole_physics/ root")
        shutil.copytree(extracted_root, target_dir)

    payload = {
        "addon_zip": str(addon_zip),
        "target_dir": str(target_dir),
        "manifest_present": manifest is not None,
        "file_count": sum(1 for path in target_dir.rglob("*") if path.is_file()),
    }
    write_json(args.json_out.resolve() if args.json_out else None, payload)
    print(f"Installed Blender addon to: {target_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
