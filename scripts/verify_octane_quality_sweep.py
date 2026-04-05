#!/usr/bin/env python3
"""Verify the generated Octane quality sweep report."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys


EXPECTED_TIERS = ("interactive", "balanced", "cinematic")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
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
        "# Octane Quality Sweep Verification",
        "",
    ]
    for tier in report.get("tiers", []):
        result = report.get("results", {}).get(tier, {})
        summary = result.get("summary", {})
        octane = summary.get("octane_settings", {})
        final_metrics = summary.get("final_metrics", {})
        comparison = summary.get("preview_to_final_comparison", {})
        lines.append(f"## `{tier}`")
        lines.append("")
        lines.append(f"- Return code: `{result.get('returncode', -1)}`")
        lines.append(f"- Max samples: `{octane.get('max_samples', '')}`")
        lines.append(f"- Adaptive threshold: `{octane.get('adaptive_noise_threshold', '')}`")
        if final_metrics:
            lines.append(f"- Final median ms: `{final_metrics.get('median_ms', 0.0):.3f}`")
        if comparison:
            lines.append(f"- Preview->final PSNR RGB: `{comparison.get('psnr_rgb', 0.0):.3f}`")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    results = report.get("results", {})
    require(results, "Quality sweep report did not contain any tier results")
    for tier in EXPECTED_TIERS:
        require(tier in results, f"Quality sweep report missing tier {tier}")

    max_samples = []
    thresholds = []
    for tier in EXPECTED_TIERS:
        result = results[tier]
        require(result.get("returncode") == 0, f"Tier {tier} exited non-zero: {result.get('returncode')}")
        inner_report = result.get("report", {}).get("inner_report", {})
        require(inner_report.get("status") == "success", f"Tier {tier} inner report was not success")
        summary = result.get("summary", {})
        octane = summary.get("octane_settings", {})
        require(summary.get("quality_tier") == tier, f"Tier {tier} summary recorded {summary.get('quality_tier')}")
        require(int(octane.get("max_samples", 0)) > 0, f"Tier {tier} missing max_samples")
        require(float(octane.get("adaptive_noise_threshold", 0.0)) > 0.0, f"Tier {tier} missing adaptive threshold")
        require(octane.get("kernel_type") == "path_tracing", f"Tier {tier} kernel is not path tracing")
        require(bool(octane.get("ai_light_enable")), f"Tier {tier} did not enable AI light")
        comparisons = summary.get("preview_to_final_comparison", {})
        if summary.get("final_metrics"):
            require(bool(comparisons), f"Tier {tier} missing preview/final comparison metrics")
            require(comparisons.get("psnr_rgb", -1.0) >= 0.0, f"Tier {tier} invalid psnr_rgb")
        max_samples.append(int(octane["max_samples"]))
        thresholds.append(float(octane["adaptive_noise_threshold"]))

    require(max_samples == sorted(max_samples), f"Tier max_samples are not non-decreasing: {max_samples}")
    require(thresholds == sorted(thresholds, reverse=True), f"Tier noise thresholds are not non-increasing: {thresholds}")

    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
