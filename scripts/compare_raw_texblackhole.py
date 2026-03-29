#!/usr/bin/env python3
"""Compare raw texBlackhole exports between two desktop lanes.

Exports pre-bloom, pre-tonemap HDR frames via --export-raw-frame and reports
basic parity statistics so CUDA-vs-GLSL analysis does not depend on the shared
postprocess stack.

Important: this script launches each binary in its normal desktop mode. With the
default `BlackholeGLSL` binary that means the legacy `traceColor()` fragment lane,
not the interop parity lane.
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


def _capture(
    binary: pathlib.Path,
    output: pathlib.Path,
    profile: str,
    composition: str,
    stage: str,
) -> None:
    env = os.environ.copy()
    env.setdefault("BLACKHOLE_WINDOW_HIDDEN", "1")
    env.setdefault("BLACKHOLE_WIREGRID_ENABLED", "0")
    env["BLACKHOLE_EXPORT_RAW_STAGE"] = stage
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


def _luminance(image: np.ndarray) -> np.ndarray:
    return 0.2126 * image[:, :, 0] + 0.7152 * image[:, :, 1] + 0.0722 * image[:, :, 2]


def _chroma(image: np.ndarray) -> np.ndarray:
    return np.max(image, axis=2) - np.min(image, axis=2)


def _decode_unit_vector(image: np.ndarray) -> np.ndarray:
    vec = image * 2.0 - 1.0
    norm = np.linalg.norm(vec, axis=2, keepdims=True)
    safe = np.where(norm > 1.0e-8, vec / norm, 0.0)
    return safe


def _dilate(mask: np.ndarray, iterations: int) -> np.ndarray:
    out = mask.copy()
    for _ in range(iterations):
        padded = np.pad(out, 1, mode="constant", constant_values=False)
        out = (
            padded[:-2, :-2]
            | padded[:-2, 1:-1]
            | padded[:-2, 2:]
            | padded[1:-1, :-2]
            | padded[1:-1, 1:-1]
            | padded[1:-1, 2:]
            | padded[2:, :-2]
            | padded[2:, 1:-1]
            | padded[2:, 2:]
        )
    return out


def _erode(mask: np.ndarray, iterations: int) -> np.ndarray:
    out = mask.copy()
    for _ in range(iterations):
        padded = np.pad(out, 1, mode="constant", constant_values=False)
        out = (
            padded[:-2, :-2]
            & padded[:-2, 1:-1]
            & padded[:-2, 2:]
            & padded[1:-1, :-2]
            & padded[1:-1, 1:-1]
            & padded[1:-1, 2:]
            & padded[2:, :-2]
            & padded[2:, 1:-1]
            & padded[2:, 2:]
        )
    return out


def _mask_stats(
    diff: np.ndarray,
    diff_rgb: np.ndarray,
    base: np.ndarray,
    other: np.ndarray,
    base_luma: np.ndarray,
    other_luma: np.ndarray,
    base_chroma: np.ndarray,
    other_chroma: np.ndarray,
    mask: np.ndarray,
    *,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    count = int(mask.sum())
    if count == 0:
        stats = {
            "count": 0,
            "mean_abs": 0.0,
            "channel_mean_abs_rgb": [0.0, 0.0, 0.0],
            "base_mean_rgb": [0.0, 0.0, 0.0],
            "other_mean_rgb": [0.0, 0.0, 0.0],
            "base_luma": 0.0,
            "other_luma": 0.0,
            "base_chroma": 0.0,
            "other_chroma": 0.0,
        }
        if extra:
            stats.update(extra)
        return stats
    stats: dict[str, Any] = {
        "count": count,
        "mean_abs": float(diff[mask].mean()),
        "channel_mean_abs_rgb": [float(x) for x in diff_rgb[mask].mean(axis=0)],
        "base_mean_rgb": [float(x) for x in base[mask].mean(axis=0)],
        "other_mean_rgb": [float(x) for x in other[mask].mean(axis=0)],
        "base_luma": float(base_luma[mask].mean()),
        "other_luma": float(other_luma[mask].mean()),
        "base_chroma": float(base_chroma[mask].mean()),
        "other_chroma": float(other_chroma[mask].mean()),
    }
    if extra:
        stats.update(extra)
    return stats


def _vector_mask_stats(base_vec: np.ndarray, other_vec: np.ndarray, mask: np.ndarray) -> dict[str, Any]:
    base_sel = base_vec[mask]
    other_sel = other_vec[mask]
    if base_sel.shape[0] == 0:
        return {
            "base_mean_vec": [0.0, 0.0, 0.0],
            "other_mean_vec": [0.0, 0.0, 0.0],
            "mean_dot": 0.0,
            "mean_angle_deg": 0.0,
            "max_angle_deg": 0.0,
        }
    dots = np.clip(np.sum(base_sel * other_sel, axis=1), -1.0, 1.0)
    angles = np.degrees(np.arccos(dots))
    return {
        "base_mean_vec": [float(x) for x in base_sel.mean(axis=0)],
        "other_mean_vec": [float(x) for x in other_sel.mean(axis=0)],
        "mean_dot": float(dots.mean()),
        "mean_angle_deg": float(angles.mean()),
        "max_angle_deg": float(angles.max()),
    }


def _safe_eroded_core(mask: np.ndarray, max_iterations: int) -> tuple[np.ndarray, int]:
    for iterations in range(max_iterations, -1, -1):
        candidate = _erode(mask, iterations) if iterations > 0 else mask.copy()
        if candidate.any():
            return candidate, iterations
    return mask.copy(), 0


def _region_summary(base: np.ndarray, other: np.ndarray, *, stage: str) -> dict[str, Any]:
    diff = np.mean(np.abs(other - base), axis=2)
    diff_rgb = np.abs(other - base)
    base_luma = _luminance(base)
    other_luma = _luminance(other)
    base_chroma = _chroma(base)
    other_chroma = _chroma(other)
    vector_stage = stage in {"closest-approach-direction", "escaped-direction"}
    if vector_stage:
        base_vec = _decode_unit_vector(base)
        other_vec = _decode_unit_vector(other)
    else:
        base_vec = None
        other_vec = None

    h, w = diff.shape
    regions = {
        "top_left": (slice(0, h // 2), slice(0, w // 2)),
        "top_right": (slice(0, h // 2), slice(w // 2, w)),
        "bottom_left": (slice(h // 2, h), slice(0, w // 2)),
        "bottom_right": (slice(h // 2, h), slice(w // 2, w)),
        "center_box": (slice(h // 2 - 120, h // 2 + 120), slice(w // 2 - 120, w // 2 + 120)),
        "right_arc_box": (slice(h // 2 - 220, h // 2 + 220), slice(w // 2, min(w, w // 2 + 360))),
    }
    summary: dict[str, Any] = {}
    for name, (ys, xs) in regions.items():
        summary[name] = {
            "mean_abs": float(diff[ys, xs].mean()),
            "channel_mean_abs_rgb": [float(x) for x in diff_rgb[ys, xs].mean(axis=(0, 1))],
            "base_mean_rgb": [float(x) for x in base[ys, xs].mean(axis=(0, 1))],
            "other_mean_rgb": [float(x) for x in other[ys, xs].mean(axis=(0, 1))],
            "base_luma": float(base_luma[ys, xs].mean()),
            "other_luma": float(other_luma[ys, xs].mean()),
            "base_chroma": float(base_chroma[ys, xs].mean()),
            "other_chroma": float(other_chroma[ys, xs].mean()),
        }
        if vector_stage:
            mask = np.zeros_like(diff, dtype=bool)
            mask[ys, xs] = True
            summary[name]["vector"] = _vector_mask_stats(base_vec, other_vec, mask)

    bright_threshold = float(np.percentile(base_luma, 99.5))
    negative_threshold = float(np.percentile(base_luma, 40.0))
    arc_mask = base_luma >= bright_threshold
    arc_core_mask, arc_core_iterations = _safe_eroded_core(arc_mask, 8)
    arc_shell_mask = arc_mask & (~arc_core_mask)
    negative_mask = base_luma <= negative_threshold
    right_half = np.zeros_like(base_luma, dtype=bool)
    right_half[:, w // 2 :] = True
    arc_adjacent_mask = _dilate(arc_mask, 22) & right_half & (~arc_mask)
    broad_right_bg_mask = right_half & (~arc_adjacent_mask) & (~arc_mask)
    summary["masks"] = {
        "bright_arc": _mask_stats(
            diff, diff_rgb, base, other, base_luma, other_luma, base_chroma, other_chroma, arc_mask, extra={"threshold": bright_threshold}
        ),
        "bright_arc_core": _mask_stats(
            diff,
            diff_rgb,
            base,
            other,
            base_luma,
            other_luma,
            base_chroma,
            other_chroma,
            arc_core_mask,
            extra={"erosion_iterations": arc_core_iterations},
        ),
        "bright_arc_shell": _mask_stats(
            diff,
            diff_rgb,
            base,
            other,
            base_luma,
            other_luma,
            base_chroma,
            other_chroma,
            arc_shell_mask,
            extra={"erosion_iterations": arc_core_iterations},
        ),
        "bright_arc_adjacent_right": _mask_stats(
            diff, diff_rgb, base, other, base_luma, other_luma, base_chroma, other_chroma, arc_adjacent_mask
        ),
        "broad_right_background": _mask_stats(
            diff, diff_rgb, base, other, base_luma, other_luma, base_chroma, other_chroma, broad_right_bg_mask
        ),
        "negative_space": _mask_stats(
            diff, diff_rgb, base, other, base_luma, other_luma, base_chroma, other_chroma, negative_mask, extra={"threshold": negative_threshold}
        ),
    }
    if vector_stage:
        for key, mask in (
            ("bright_arc", arc_mask),
            ("bright_arc_core", arc_core_mask),
            ("bright_arc_shell", arc_shell_mask),
            ("bright_arc_adjacent_right", arc_adjacent_mask),
            ("broad_right_background", broad_right_bg_mask),
            ("negative_space", negative_mask),
        ):
            summary["masks"][key]["vector"] = _vector_mask_stats(base_vec, other_vec, mask)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parents[1])
    parser.add_argument(
        "--glsl-binary",
        default="build/Release/BlackholeGLSL",
        help="Desktop GLSL host to capture. The default BlackholeGLSL binary uses the legacy traceColor lane.",
    )
    parser.add_argument("--cuda-binary", default="build/Release/BlackholeCUDA")
    parser.add_argument("--profile", default="showcase-orbit")
    parser.add_argument("--composition", default="wide-right")
    parser.add_argument(
        "--stage",
        default="final",
        choices=[
            "final",
            "pre-redshift-background",
            "pre-shaping-background",
            "post-shaping-background",
            "shaper-inputs",
            "closest-approach-direction",
            "escaped-direction",
        ],
        help="Which raw renderer stage to export.",
    )
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
    _capture(glsl_binary, glsl_raw, args.profile, args.composition, args.stage)
    _capture(cuda_binary, cuda_raw, args.profile, args.composition, args.stage)

    glsl = _read_pfm(glsl_raw)
    cuda = _read_pfm(cuda_raw)
    if glsl.shape != cuda.shape:
        raise ValueError(f"shape mismatch: GLSL {glsl.shape} vs CUDA {cuda.shape}")

    summary = {
        "profile": args.profile,
        "composition": args.composition,
        "stage": args.stage,
        "shape": list(glsl.shape),
        "glsl": _summarize(glsl, glsl),
        "cuda": _summarize(glsl, cuda),
        "regions": _region_summary(glsl, cuda, stage=args.stage),
    }
    summary_path = output_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    json.dump(summary, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
