#!/usr/bin/env python3
"""Compare raw texBlackhole exports between two desktop lanes.

Exports pre-bloom, pre-tonemap HDR frames via --export-raw-frame and reports
basic parity statistics so CUDA-vs-GLSL analysis does not depend on the shared
postprocess stack.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import sys
from typing import Any

import numpy as np


def _read_pfm(path: pathlib.Path) -> np.ndarray:
    with path.open("rb") as handle:
        header = handle.readline().decode("ascii").strip()
        if header != "PF":
            raise ValueError(f"{path} is not an RGB PFM file")
        dims = handle.readline().decode("ascii").strip().split()
        if len(dims) != 2:
            raise ValueError(f"{path} has malformed dimensions")
        width, height = (int(dims[0]), int(dims[1]))
        scale = float(handle.readline().decode("ascii").strip())
        dtype = "<f4" if scale < 0 else ">f4"
        data = np.frombuffer(handle.read(), dtype=dtype)
        expected = width * height * 3
        if data.size != expected:
            raise ValueError(f"{path} expected {expected} floats, found {data.size}")
        image = data.reshape((height, width, 3))
        return np.flipud(image)


def _capture(binary: pathlib.Path, output: pathlib.Path, profile: str, composition: str) -> None:
    env = os.environ.copy()
    env.setdefault("BLACKHOLE_WINDOW_HIDDEN", "1")
    env.setdefault("BLACKHOLE_WIREGRID_ENABLED", "0")
    output.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        str(binary),
        "--record-profile",
        profile,
        "--record-composition",
        composition,
        "--export-raw-frame",
        str(output),
    ]
    subprocess.run(cmd, env=env, check=True)


def _summarize(base: np.ndarray, other: np.ndarray) -> dict[str, Any]:
    h, w, _ = other.shape
    cy0, cy1 = h // 2 - 60, h // 2 + 60
    cx0, cx1 = w // 2 - 60, w // 2 + 60
    center = other[cy0:cy1, cx0:cx1]
    dark = np.all(other < 0.02, axis=2)
    return {
        "mean_abs_vs_base": float(np.mean(np.abs(other - base))),
        "center_mean_rgb": [float(x) for x in center.mean(axis=(0, 1))],
        "full_mean_rgb": [float(x) for x in other.mean(axis=(0, 1))],
        "dark_count": int(dark.sum()),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parents[1])
    parser.add_argument("--glsl-binary", default="build/Release/BlackholeGLSL")
    parser.add_argument("--cuda-binary", default="build/Release/BlackholeCUDA")
    parser.add_argument("--profile", default="showcase-orbit")
    parser.add_argument("--composition", default="wide-right")
    parser.add_argument(
        "--output-dir",
        type=pathlib.Path,
        default=None,
        help="Directory for raw captures and summary JSON (default: .cache/raw_compare/<profile>_<composition>)",
    )
    args = parser.parse_args()

    repo = args.repo.resolve()
    output_dir = (
        args.output_dir.resolve()
        if args.output_dir is not None
        else (repo / ".cache" / "raw_compare" / f"{args.profile}_{args.composition}").resolve()
    )
    glsl_binary = (repo / args.glsl_binary).resolve()
    cuda_binary = (repo / args.cuda_binary).resolve()

    glsl_raw = output_dir / "glsl_raw.pfm"
    cuda_raw = output_dir / "cuda_raw.pfm"
    _capture(glsl_binary, glsl_raw, args.profile, args.composition)
    _capture(cuda_binary, cuda_raw, args.profile, args.composition)

    glsl = _read_pfm(glsl_raw)
    cuda = _read_pfm(cuda_raw)
    if glsl.shape != cuda.shape:
        raise ValueError(f"shape mismatch: GLSL {glsl.shape} vs CUDA {cuda.shape}")

    summary = {
        "profile": args.profile,
        "composition": args.composition,
        "shape": list(glsl.shape),
        "glsl": _summarize(glsl, glsl),
        "cuda": _summarize(glsl, cuda),
    }
    summary_path = output_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    json.dump(summary, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
