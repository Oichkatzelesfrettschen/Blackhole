#!/usr/bin/env python3
"""Derive scene policy recommendations from a verified Dream Textures conditioning sweep."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--host-label", required=True)
    parser.add_argument("--scene-profile", choices=("baseline", "harsh_lighting"), required=True)
    parser.add_argument("--min-production-psnr-rgb", type=float, default=20.0)
    parser.add_argument("--min-production-psnr-luma", type=float, default=20.0)
    parser.add_argument("--min-interactive-psnr-rgb", type=float, default=25.0)
    parser.add_argument("--min-interactive-psnr-luma", type=float, default=25.0)
    parser.add_argument("--max-production-latency-ratio", type=float, default=2.5)
    return parser.parse_args(argv)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def comparison_map(report: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    return {
        (entry.get("reference", ""), entry.get("candidate", "")): entry
        for entry in report.get("comparisons", [])
    }


def mode_elapsed(report: dict[str, Any], mode: str) -> float:
    return float(report.get("results", {}).get(mode, {}).get("summary", {}).get("elapsed_seconds", 0.0))


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Dream Textures Conditioning Policy",
        "",
        f"- Host: `{summary.get('host_label', '')}`",
        f"- Scene profile: `{summary.get('scene_profile', '')}`",
        f"- Memory profile: `{summary.get('memory_profile', '')}`",
        f"- Recommended interactive mode: `{summary.get('recommended_interactive_mode', '')}`",
        f"- Recommended production mode: `{summary.get('recommended_production_mode', '')}`",
        "",
        "## Rationale",
        "",
        f"- Image vs image+depth PSNR RGB: `{summary.get('image_depth_vs_image', {}).get('psnr_rgb', 0.0):.3f}`",
        f"- Image vs image+depth PSNR luma: `{summary.get('image_depth_vs_image', {}).get('psnr_luma', 0.0):.3f}`",
        f"- Image latency: `{summary.get('elapsed_seconds', {}).get('image', 0.0):.3f}` s",
        f"- Depth latency: `{summary.get('elapsed_seconds', {}).get('depth', 0.0):.3f}` s",
        f"- Image+depth latency: `{summary.get('elapsed_seconds', {}).get('image_depth', 0.0):.3f}` s",
        "",
        "## Candidate Metrics",
        "",
    ]
    for mode in ("none", "image", "depth", "image_depth"):
        metrics = summary.get("mode_metrics", {}).get(mode, {})
        lines.extend(
            [
                f"### `{mode}`",
                "",
                f"- Mean: `{metrics.get('mean', 0.0):.6f}`",
                f"- Elapsed: `{metrics.get('elapsed_seconds', 0.0):.3f}` s",
                f"- PSNR-to-image-depth RGB: `{metrics.get('psnr_to_image_depth_rgb', 0.0):.3f}`",
                f"- PSNR-to-image-depth luma: `{metrics.get('psnr_to_image_depth_luma', 0.0):.3f}`",
                "",
            ]
        )
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    require(report.get("scene_profile") == args.scene_profile, "Conditioning policy scene profile mismatch")
    comparisons = comparison_map(report)
    results = report.get("results", {})

    require("image" in results and "depth" in results and "image_depth" in results, "Missing conditioning modes")
    image_depth_vs_image = comparisons.get(("image", "image_depth"))
    depth_vs_image_depth = comparisons.get(("depth", "image_depth"))
    none_vs_image_depth = comparisons.get(("none", "image_depth"))
    require(image_depth_vs_image is not None, "Missing image vs image_depth comparison")
    require(depth_vs_image_depth is not None, "Missing depth vs image_depth comparison")
    require(none_vs_image_depth is not None, "Missing none vs image_depth comparison")

    image_psnr_rgb = float(image_depth_vs_image["metrics"].get("psnr_rgb", 0.0))
    image_psnr_luma = float(image_depth_vs_image["metrics"].get("psnr_luma", 0.0))
    image_elapsed = mode_elapsed(report, "image")
    depth_elapsed = mode_elapsed(report, "depth")
    image_depth_elapsed = mode_elapsed(report, "image_depth")
    fastest_conditioned = min(max(image_elapsed, 1.0e-8), max(depth_elapsed, 1.0e-8))

    production_mode = "image_depth"
    if not (
        image_psnr_rgb >= args.min_production_psnr_rgb
        and image_psnr_luma >= args.min_production_psnr_luma
        and image_depth_elapsed <= fastest_conditioned * args.max_production_latency_ratio
    ):
        production_mode = "image"

    interactive_candidates: list[tuple[float, str]] = []
    candidate_metrics = {
        "image": image_depth_vs_image["metrics"],
        "depth": depth_vs_image_depth["metrics"],
        "none": none_vs_image_depth["metrics"],
    }
    for mode in ("image", "depth"):
        metrics = candidate_metrics[mode]
        if (
            float(metrics.get("psnr_rgb", 0.0)) >= args.min_interactive_psnr_rgb
            and float(metrics.get("psnr_luma", 0.0)) >= args.min_interactive_psnr_luma
        ):
            interactive_candidates.append((mode_elapsed(report, mode), mode))
    interactive_mode = min(interactive_candidates)[1] if interactive_candidates else "image"

    mode_metrics: dict[str, dict[str, Any]] = {}
    for mode in ("none", "image", "depth", "image_depth"):
        summary = results[mode]["summary"]
        if mode == "image_depth":
            psnr_rgb = 99.0
            psnr_luma = 99.0
        elif mode == "image":
            psnr_rgb = image_psnr_rgb
            psnr_luma = image_psnr_luma
        elif mode == "depth":
            psnr_rgb = float(depth_vs_image_depth["metrics"].get("psnr_rgb", 0.0))
            psnr_luma = float(depth_vs_image_depth["metrics"].get("psnr_luma", 0.0))
        else:
            psnr_rgb = float(none_vs_image_depth["metrics"].get("psnr_rgb", 0.0))
            psnr_luma = float(none_vs_image_depth["metrics"].get("psnr_luma", 0.0))
        mode_metrics[mode] = {
            "mean": float(summary.get("mean", 0.0)),
            "elapsed_seconds": float(summary.get("elapsed_seconds", 0.0)),
            "psnr_to_image_depth_rgb": psnr_rgb,
            "psnr_to_image_depth_luma": psnr_luma,
        }

    summary = {
        "host_label": args.host_label,
        "scene_profile": report.get("scene_profile", ""),
        "memory_profile": report.get("memory_profile", ""),
        "recommended_interactive_mode": interactive_mode,
        "recommended_production_mode": production_mode,
        "elapsed_seconds": {
            "image": image_elapsed,
            "depth": depth_elapsed,
            "image_depth": image_depth_elapsed,
        },
        "image_depth_vs_image": {
            "psnr_rgb": image_psnr_rgb,
            "psnr_luma": image_psnr_luma,
        },
        "mode_metrics": mode_metrics,
        "thresholds": {
            "min_production_psnr_rgb": args.min_production_psnr_rgb,
            "min_production_psnr_luma": args.min_production_psnr_luma,
            "min_interactive_psnr_rgb": args.min_interactive_psnr_rgb,
            "min_interactive_psnr_luma": args.min_interactive_psnr_luma,
            "max_production_latency_ratio": args.max_production_latency_ratio,
        },
    }
    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
