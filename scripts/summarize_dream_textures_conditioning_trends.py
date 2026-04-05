#!/usr/bin/env python3
"""Summarize scene-aware Dream Textures conditioning trends across hosts."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-blender-report", required=True, type=pathlib.Path)
    parser.add_argument("--baseline-octane-report", required=True, type=pathlib.Path)
    parser.add_argument("--harsh-blender-report", required=True, type=pathlib.Path)
    parser.add_argument("--harsh-octane-report", required=True, type=pathlib.Path)
    parser.add_argument("--baseline-parity-report", required=True, type=pathlib.Path)
    parser.add_argument("--harsh-parity-report", required=True, type=pathlib.Path)
    parser.add_argument("--baseline-blender-policy", required=True, type=pathlib.Path)
    parser.add_argument("--baseline-octane-policy", required=True, type=pathlib.Path)
    parser.add_argument("--harsh-blender-policy", required=True, type=pathlib.Path)
    parser.add_argument("--harsh-octane-policy", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    return parser.parse_args(argv)


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def load_json(path: pathlib.Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def mode_latency_ranking(report: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for mode, result in report.get("results", {}).items():
        summary = result.get("summary", {})
        rows.append(
            {
                "mode": mode,
                "elapsed_seconds": float(summary.get("elapsed_seconds", 0.0)),
                "mean": float(summary.get("mean", 0.0)),
            }
        )
    rows.sort(key=lambda row: row["elapsed_seconds"])
    return rows


def mode_delta_map(parity: dict[str, Any]) -> dict[str, float]:
    return {entry.get("mode", ""): float(entry.get("mean_delta", 0.0)) for entry in parity.get("mode_parity", [])}


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Dream Textures Conditioning Trends",
        "",
    ]
    for scene_name, scene in summary.get("scenes", {}).items():
        lines.extend(
            [
                f"## `{scene_name}`",
                "",
                f"- Consensus interactive mode: `{scene.get('consensus_interactive_mode', '')}`",
                f"- Consensus production mode: `{scene.get('consensus_production_mode', '')}`",
                f"- Max mean delta: `{scene.get('parity', {}).get('max_mode_mean_delta', 0.0):.6f}`",
                f"- Max PSNR RGB delta: `{scene.get('parity', {}).get('max_psnr_rgb_delta', 0.0):.6f}`",
                "",
            ]
        )
        for host_name, host in scene.get("hosts", {}).items():
            lines.extend(
                [
                    f"### `{host_name}`",
                    "",
                    f"- Interactive mode: `{host.get('policy', {}).get('recommended_interactive_mode', '')}`",
                    f"- Production mode: `{host.get('policy', {}).get('recommended_production_mode', '')}`",
                    "",
                ]
            )
            for row in host.get("latency_ranking", []):
                lines.append(
                    f"- `{row.get('mode', '')}` elapsed `{row.get('elapsed_seconds', 0.0):.3f}` s mean `{row.get('mean', 0.0):.6f}`"
                )
            lines.append("")
    return "\n".join(lines).strip() + "\n"


def scene_block(
    blender_report: dict[str, Any],
    octane_report: dict[str, Any],
    parity: dict[str, Any],
    blender_policy: dict[str, Any],
    octane_policy: dict[str, Any],
) -> dict[str, Any]:
    comparison_parity = parity.get("comparison_parity", [])
    mode_parity = parity.get("mode_parity", [])
    consensus_interactive = blender_policy.get("recommended_interactive_mode", "")
    if octane_policy.get("recommended_interactive_mode", "") != consensus_interactive:
        consensus_interactive = "mixed"
    consensus_production = blender_policy.get("recommended_production_mode", "")
    if octane_policy.get("recommended_production_mode", "") != consensus_production:
        consensus_production = "mixed"
    return {
        "scene_profile": blender_report.get("scene_profile", ""),
        "consensus_interactive_mode": consensus_interactive,
        "consensus_production_mode": consensus_production,
        "hosts": {
            "blender": {
                "policy": blender_policy,
                "latency_ranking": mode_latency_ranking(blender_report),
            },
            "octane": {
                "policy": octane_policy,
                "latency_ranking": mode_latency_ranking(octane_report),
            },
        },
        "parity": {
            "max_mode_mean_delta": max((float(entry.get("mean_delta", 0.0)) for entry in mode_parity), default=0.0),
            "max_psnr_rgb_delta": max((float(entry.get("psnr_rgb_delta", 0.0)) for entry in comparison_parity), default=0.0),
            "mode_mean_deltas": mode_delta_map(parity),
        },
    }


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    baseline_blender = load_json(args.baseline_blender_report)
    baseline_octane = load_json(args.baseline_octane_report)
    harsh_blender = load_json(args.harsh_blender_report)
    harsh_octane = load_json(args.harsh_octane_report)
    baseline_parity = load_json(args.baseline_parity_report)
    harsh_parity = load_json(args.harsh_parity_report)
    baseline_blender_policy = load_json(args.baseline_blender_policy)
    baseline_octane_policy = load_json(args.baseline_octane_policy)
    harsh_blender_policy = load_json(args.harsh_blender_policy)
    harsh_octane_policy = load_json(args.harsh_octane_policy)

    summary = {
        "scenes": {
            "baseline": scene_block(
                baseline_blender,
                baseline_octane,
                baseline_parity,
                baseline_blender_policy,
                baseline_octane_policy,
            ),
            "harsh_lighting": scene_block(
                harsh_blender,
                harsh_octane,
                harsh_parity,
                harsh_blender_policy,
                harsh_octane_policy,
            ),
        }
    }
    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
