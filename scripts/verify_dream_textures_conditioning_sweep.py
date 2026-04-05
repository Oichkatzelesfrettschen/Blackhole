#!/usr/bin/env python3
"""Verify a generated Dream Textures conditioning sweep report."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys


EXPECTED_MODES = ("none", "image", "depth", "image_depth")
REQUIRED_COMPARISON_METRICS = (
    "mae_rgb",
    "rmse_rgb",
    "max_abs_diff_rgb",
    "psnr_rgb",
    "mae_luma",
    "rmse_luma",
    "max_abs_diff_luma",
    "psnr_luma",
    "reference_mean_luma",
    "candidate_mean_luma",
    "luma_cosine_similarity",
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--expect-scene-profile", choices=("baseline", "harsh_lighting"))
    parser.add_argument("--min-image-depth-vs-image-psnr-rgb", type=float, default=20.0)
    parser.add_argument("--min-image-depth-vs-image-psnr-luma", type=float, default=20.0)
    return parser.parse_args(argv)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    lines = [
        "# Dream Textures Conditioning Sweep Verification",
        "",
        f"- Scene profile: `{report.get('scene_profile', '')}`",
        f"- Memory profile: `{report.get('memory_profile', '')}`",
        f"- Text/image model: `{report.get('text_model_id', '')}`",
        f"- Depth/image+depth model: `{report.get('depth_model_id', '')}`",
        "",
    ]
    for mode in report.get("modes", []):
        result = report.get("results", {}).get(mode, {})
        summary = result.get("summary", {})
        lines.append(f"## `{mode}`")
        lines.append("")
        lines.append(f"- Return code: `{result.get('returncode', -1)}`")
        lines.append(f"- Mean: `{summary.get('mean', 0.0):.6f}`")
        lines.append(f"- Elapsed: `{summary.get('elapsed_seconds', 0.0):.3f}` s")
        lines.append(f"- Source origin: `{summary.get('conditioning_policy', {}).get('source_origin', '')}`")
        lines.append("")
    for comparison in report.get("comparisons", []):
        metrics = comparison.get("metrics", {})
        lines.append(f"## `{comparison.get('candidate', '')} vs {comparison.get('reference', '')}`")
        lines.append("")
        lines.append(f"- PSNR RGB: `{metrics.get('psnr_rgb', 0.0):.3f}`")
        lines.append(f"- PSNR luma: `{metrics.get('psnr_luma', 0.0):.3f}`")
        lines.append(f"- Luma cosine similarity: `{metrics.get('luma_cosine_similarity', 0.0):.6f}`")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    results = report.get("results", {})
    require(results, "Conditioning sweep report did not contain any results")
    require(bool(report.get("scene_profile")), "Conditioning sweep report missing scene_profile")
    require(bool(report.get("memory_profile")), "Conditioning sweep report missing memory_profile")
    require(bool(report.get("text_model_id")), "Conditioning sweep report missing text_model_id")
    require(bool(report.get("depth_model_id")), "Conditioning sweep report missing depth_model_id")
    if args.expect_scene_profile:
        require(
            report.get("scene_profile") == args.expect_scene_profile,
            f"Conditioning sweep scene profile mismatch: {report.get('scene_profile')}",
        )

    for mode in EXPECTED_MODES:
        require(mode in results, f"Conditioning sweep report missing mode {mode}")
        result = results[mode]
        require(result.get("returncode") == 0, f"Mode {mode} exited non-zero: {result.get('returncode')}")
        summary = result.get("summary", {})
        require(summary.get("status") == "success", f"Mode {mode} inner status was not success")
        require(bool(summary.get("model_id")), f"Mode {mode} missing model_id")
        require(float(summary.get("elapsed_seconds", 0.0)) > 0.0, f"Mode {mode} missing elapsed_seconds")
        artifact_path = pathlib.Path(summary.get("artifact_path", ""))
        require(artifact_path.exists(), f"Mode {mode} artifact missing: {artifact_path}")
        conditioning = summary.get("conditioning_policy", {})
        require(conditioning.get("mode") == mode, f"Mode {mode} summary recorded {conditioning.get('mode')}")
        if mode == "none":
            require(not conditioning.get("has_source_image", False), "Text-only mode unexpectedly used a source image")
            require(not conditioning.get("has_source_depth", False), "Text-only mode unexpectedly used source depth")
        if mode in {"image", "image_depth"}:
            require(conditioning.get("has_source_image", False), f"Mode {mode} missing source image")
            require(bool(conditioning.get("source_image_name", "")), f"Mode {mode} missing source image name")
        if mode in {"depth", "image_depth"}:
            require(conditioning.get("has_source_depth", False), f"Mode {mode} missing source depth")
            require(bool(conditioning.get("source_depth_name", "")), f"Mode {mode} missing source depth name")

    comparisons = report.get("comparisons", [])
    require(comparisons, "Conditioning sweep report did not record any comparisons")
    comparison_keys = {(entry.get("reference", ""), entry.get("candidate", "")) for entry in comparisons}
    for required in {
        ("none", "image"),
        ("none", "depth"),
        ("none", "image_depth"),
        ("image", "image_depth"),
        ("depth", "image_depth"),
    }:
        require(required in comparison_keys, f"Conditioning sweep missing comparison {required}")
    for comparison in comparisons:
        artifact_path = pathlib.Path(comparison.get("artifact_path", ""))
        require(artifact_path.exists(), f"Comparison artifact missing: {artifact_path}")
        metrics = comparison.get("metrics", {})
        for key in REQUIRED_COMPARISON_METRICS:
            require(key in metrics, f"Comparison {comparison.get('candidate')} vs {comparison.get('reference')} missing metric {key}")
        require(metrics.get("psnr_rgb", 0.0) >= 0.0, "Comparison psnr_rgb was invalid")
        require(0.0 <= metrics.get("luma_cosine_similarity", 0.0) <= 1.000001, "Comparison luma cosine similarity was invalid")

    image_depth_vs_image = next(
        (
            entry for entry in comparisons
            if entry.get("reference") == "image" and entry.get("candidate") == "image_depth"
        ),
        None,
    )
    require(image_depth_vs_image is not None, "Conditioning sweep missing image_depth vs image comparison")
    image_depth_metrics = image_depth_vs_image.get("metrics", {})
    require(
        float(image_depth_metrics.get("psnr_rgb", 0.0)) >= args.min_image_depth_vs_image_psnr_rgb,
        "Conditioning sweep image_depth vs image PSNR RGB fell below the configured floor",
    )
    require(
        float(image_depth_metrics.get("psnr_luma", 0.0)) >= args.min_image_depth_vs_image_psnr_luma,
        "Conditioning sweep image_depth vs image PSNR luma fell below the configured floor",
    )

    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
