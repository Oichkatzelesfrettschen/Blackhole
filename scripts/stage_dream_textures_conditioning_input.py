#!/usr/bin/env python3
"""Stage conditioning inputs for future Dream Textures image/depth workflows."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import shutil
import sys


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--staging-dir", type=pathlib.Path, required=True)
    parser.add_argument("--color", type=pathlib.Path)
    parser.add_argument("--depth", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    return parser.parse_args(argv)


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def stage_one(kind: str, src: pathlib.Path, dst_root: pathlib.Path) -> dict[str, object]:
    src = src.resolve()
    dst_root.mkdir(parents=True, exist_ok=True)
    dst = dst_root / f"{kind}{src.suffix.lower()}"
    shutil.copy2(src, dst)
    return {
        "kind": kind,
        "source": str(src),
        "staged": str(dst),
        "sha256": sha256_file(dst),
        "byte_length": dst.stat().st_size,
    }


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    staging_dir = args.staging_dir.resolve()
    payload = {
        "label": args.label,
        "staging_dir": str(staging_dir),
        "artifacts": {},
    }
    if args.color:
        payload["artifacts"]["color"] = stage_one("color", args.color, staging_dir)
    if args.depth:
        payload["artifacts"]["depth"] = stage_one("depth", args.depth, staging_dir)
    if not payload["artifacts"]:
        raise SystemExit("Provide at least one of --color or --depth")
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
