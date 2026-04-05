#!/usr/bin/env python3
"""Verify the Blender ctypes ABI against the exported bridge library."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import subprocess
import sys
from typing import Any


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bridge-python", required=True, type=pathlib.Path)
    parser.add_argument("--bridge-header", required=True, type=pathlib.Path)
    parser.add_argument("--bridge-library", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    return parser.parse_args(argv)


def load_bridge_module(path: pathlib.Path):
    spec = importlib.util.spec_from_file_location("blackhole_bridge_py", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load bridge module from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_nm(library: pathlib.Path) -> set[str]:
    proc = subprocess.run(
        ["nm", "-D", "--defined-only", str(library)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or f"nm failed for {library}")
    exports: set[str] = set()
    for line in proc.stdout.splitlines():
        parts = line.split()
        if parts:
            exports.add(parts[-1])
    return exports


def parse_header_symbols(header_text: str) -> set[str]:
    symbols = set(re.findall(r"\b(bhb[A-Za-z0-9_]+)\s*\(", header_text))
    return {symbol for symbol in symbols if not symbol.startswith("bhb_")}


def parse_python_symbols(source_text: str) -> set[str]:
    return set(re.findall(r"\bbhb_[a-z0-9_]+\b", source_text))


def collect_missing_argtypes(module: Any, python_symbols: set[str]) -> list[str]:
    missing: list[str] = []
    for symbol in sorted(python_symbols):
        if not hasattr(module._lib, symbol):
            continue
        fn = getattr(module._lib, symbol)
        if not hasattr(fn, "argtypes") or fn.argtypes is None:
            missing.append(symbol)
    return missing


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Blender Bridge ABI Report",
        "",
        f"- Bridge Python: `{report['bridge_python']}`",
        f"- Bridge header: `{report['bridge_header']}`",
        f"- Bridge library: `{report['bridge_library']}`",
        f"- Exported symbols: `{report['export_count']}`",
        f"- Python ABI symbols: `{len(report['python_symbols'])}`",
        f"- Header ABI symbols: `{len(report['header_symbols'])}`",
        f"- Python source params size: `{report['python_sizes']['source_params']}`",
        f"- Python disk params size: `{report['python_sizes']['disk_params']}`",
        f"- C source params size: `{report['c_sizes']['source_params']}`",
        f"- C disk params size: `{report['c_sizes']['disk_params']}`",
        "",
    ]
    for key in ("missing_python_exports", "missing_header_exports", "missing_argtypes"):
        values = report[key]
        lines.append(f"## {key.replace('_', ' ').title()}")
        lines.append("")
        if values:
            for value in values:
                lines.append(f"- `{value}`")
        else:
            lines.append("- None")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    bridge_python = args.bridge_python.resolve()
    bridge_header = args.bridge_header.resolve()
    bridge_library = args.bridge_library.resolve()

    source_text = bridge_python.read_text(encoding="utf-8")
    header_text = bridge_header.read_text(encoding="utf-8")
    python_symbols = sorted(parse_python_symbols(source_text))
    header_symbols = sorted(parse_header_symbols(header_text))
    exports = run_nm(bridge_library)

    module = load_bridge_module(bridge_python)
    module._lib = module.ctypes.CDLL(str(bridge_library))
    module._setup_prototypes(module._lib)

    report = {
        "bridge_python": str(bridge_python),
        "bridge_header": str(bridge_header),
        "bridge_library": str(bridge_library),
        "export_count": len(exports),
        "python_symbols": python_symbols,
        "header_symbols": header_symbols,
        "missing_python_exports": [symbol for symbol in python_symbols if symbol not in exports],
        "missing_header_exports": [symbol for symbol in header_symbols if symbol not in exports],
        "missing_argtypes": collect_missing_argtypes(module, set(python_symbols)),
        "python_sizes": {
            "source_params": module.ctypes.sizeof(module.BHB_SourceParams),
            "disk_params": module.ctypes.sizeof(module.BHB_DiskParams),
        },
        "c_sizes": {
            "source_params": module._lib.bhb_sizeof_source_params(),
            "disk_params": module._lib.bhb_sizeof_disk_params(),
        },
    }

    if report["python_sizes"] != report["c_sizes"]:
        raise SystemExit(
            "ctypes struct sizes do not match bridge library sizes: "
            f"{report['python_sizes']} vs {report['c_sizes']}"
        )
    if report["missing_python_exports"]:
        raise SystemExit(f"Missing Python ABI exports: {', '.join(report['missing_python_exports'])}")
    if report["missing_header_exports"]:
        raise SystemExit(f"Missing header exports: {', '.join(report['missing_header_exports'])}")
    if report["missing_argtypes"]:
        raise SystemExit(f"Missing ctypes argtypes: {', '.join(report['missing_argtypes'])}")

    write_text(args.json_out, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
