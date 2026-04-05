#!/usr/bin/env python3
"""Verify that Blender and Octane conditioning sweeps stay within parity bounds."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-report", required=True, type=pathlib.Path)
    parser.add_argument("--octane-report", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--max-mean-delta", type=float, default=0.02)
    parser.add_argument("--max-psnr-delta", type=float, default=0.25)
    parser.add_argument("--max-cosine-delta", type=float, default=0.02)
    return parser.parse_args(argv)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def comparison_map(report: dict) -> dict[tuple[str, str], dict]:
    return {
        (entry.get("reference", ""), entry.get("candidate", "")): entry
        for entry in report.get("comparisons", [])
    }


def render_markdown(summary: dict) -> str:
    lines = [
        "# Dream Textures Conditioning Host Parity",
        "",
        f"- Scene profile: `{summary.get('scene_profile', '')}`",
        f"- Memory profile: `{summary.get('memory_profile', '')}`",
        f"- Max mean delta: `{summary.get('max_mean_delta', 0.0):.6f}`",
        f"- Max PSNR delta: `{summary.get('max_psnr_delta', 0.0):.6f}`",
        f"- Max cosine delta: `{summary.get('max_cosine_delta', 0.0):.6f}`",
        "",
    ]
    for mode_entry in summary.get("mode_parity", []):
        lines.extend(
            [
                f"## Mode `{mode_entry['mode']}`",
                "",
                f"- Blender mean: `{mode_entry['blender_mean']:.6f}`",
                f"- Octane mean: `{mode_entry['octane_mean']:.6f}`",
                f"- Mean delta: `{mode_entry['mean_delta']:.6f}`",
                "",
            ]
        )
    for comp in summary.get("comparison_parity", []):
        lines.extend(
            [
                f"## `{comp['candidate']} vs {comp['reference']}`",
                "",
                f"- PSNR RGB delta: `{comp['psnr_rgb_delta']:.6f}`",
                f"- PSNR luma delta: `{comp['psnr_luma_delta']:.6f}`",
                f"- Luma cosine delta: `{comp['cosine_delta']:.6f}`",
                "",
            ]
        )
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    blender = json.loads(args.blender_report.read_text(encoding="utf-8"))
    octane = json.loads(args.octane_report.read_text(encoding="utf-8"))

    require(blender.get("scene_profile") == octane.get("scene_profile"), "Host parity scene_profile mismatch")
    require(blender.get("memory_profile") == octane.get("memory_profile"), "Host parity memory_profile mismatch")
    require(blender.get("modes") == octane.get("modes"), "Host parity mode list mismatch")
    require(blender.get("text_model_id") == octane.get("text_model_id"), "Host parity text_model_id mismatch")
    require(blender.get("depth_model_id") == octane.get("depth_model_id"), "Host parity depth_model_id mismatch")

    mode_parity: list[dict[str, float | str]] = []
    for mode in blender.get("modes", []):
        b_summary = blender["results"][mode]["summary"]
        o_summary = octane["results"][mode]["summary"]
        mean_delta = abs(float(b_summary.get("mean", 0.0)) - float(o_summary.get("mean", 0.0)))
        require(
            mean_delta <= args.max_mean_delta,
            f"Host parity mean delta for mode {mode} exceeded tolerance: {mean_delta}",
        )
        mode_parity.append(
            {
                "mode": mode,
                "blender_mean": float(b_summary.get("mean", 0.0)),
                "octane_mean": float(o_summary.get("mean", 0.0)),
                "mean_delta": mean_delta,
            }
        )

    blender_comparisons = comparison_map(blender)
    octane_comparisons = comparison_map(octane)
    require(blender_comparisons.keys() == octane_comparisons.keys(), "Host parity comparison-set mismatch")

    comparison_parity: list[dict[str, float | str]] = []
    for key in sorted(blender_comparisons.keys()):
        b_metrics = blender_comparisons[key].get("metrics", {})
        o_metrics = octane_comparisons[key].get("metrics", {})
        psnr_rgb_delta = abs(float(b_metrics.get("psnr_rgb", 0.0)) - float(o_metrics.get("psnr_rgb", 0.0)))
        psnr_luma_delta = abs(float(b_metrics.get("psnr_luma", 0.0)) - float(o_metrics.get("psnr_luma", 0.0)))
        cosine_delta = abs(
            float(b_metrics.get("luma_cosine_similarity", 0.0))
            - float(o_metrics.get("luma_cosine_similarity", 0.0))
        )
        require(
            psnr_rgb_delta <= args.max_psnr_delta,
            f"Host parity PSNR RGB delta for {key} exceeded tolerance: {psnr_rgb_delta}",
        )
        require(
            psnr_luma_delta <= args.max_psnr_delta,
            f"Host parity PSNR luma delta for {key} exceeded tolerance: {psnr_luma_delta}",
        )
        require(
            cosine_delta <= args.max_cosine_delta,
            f"Host parity cosine delta for {key} exceeded tolerance: {cosine_delta}",
        )
        comparison_parity.append(
            {
                "reference": key[0],
                "candidate": key[1],
                "psnr_rgb_delta": psnr_rgb_delta,
                "psnr_luma_delta": psnr_luma_delta,
                "cosine_delta": cosine_delta,
            }
        )

    summary = {
        "scene_profile": blender.get("scene_profile", ""),
        "memory_profile": blender.get("memory_profile", ""),
        "max_mean_delta": args.max_mean_delta,
        "max_psnr_delta": args.max_psnr_delta,
        "max_cosine_delta": args.max_cosine_delta,
        "mode_parity": mode_parity,
        "comparison_parity": comparison_parity,
    }
    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
