#!/usr/bin/env python3
"""Run the Octane benchmark lane across a small set of named quality tiers."""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import tempfile


DEFAULT_TIERS = ("interactive", "balanced", "cinematic")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--addon-zip", required=True)
    parser.add_argument("--bridge-lib", required=True)
    parser.add_argument("--octane-readiness-report")
    parser.add_argument("--json-out", required=True)
    parser.add_argument("--md-out")
    parser.add_argument("--log-out")
    parser.add_argument("--width", type=int, default=640)
    parser.add_argument("--height", type=int, default=360)
    parser.add_argument("--measured-frames", type=int, default=2)
    parser.add_argument("--warmup-frames", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=240)
    parser.add_argument("--tiers", nargs="+", default=list(DEFAULT_TIERS))
    return parser


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def load_json(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def find_benchmark(report: dict, name: str) -> dict:
    inner = report.get("inner_report", {})
    for benchmark in inner.get("benchmarks", []):
        if benchmark.get("name") == name:
            return benchmark
    return {}


def find_comparison(report: dict, reference: str, candidate: str) -> dict:
    inner = report.get("inner_report", {})
    for comparison in inner.get("comparisons", []):
        if comparison.get("reference") == reference and comparison.get("candidate") == candidate:
            return comparison
    return {}


def summarize_tier(report: dict) -> dict:
    studio_quality = report.get("inner_report", {}).get("studio_quality", {})
    octane = studio_quality.get("octane", {})
    final_benchmark = find_benchmark(report, "render_engine_final")
    preview_benchmark = find_benchmark(report, "bridge_cuda_preview")
    comparison = find_comparison(report, "bridge_cuda_preview", "render_engine_final")
    return {
        "quality_tier": report.get("quality_tier", ""),
        "studio_profile": studio_quality.get("profile", ""),
        "octane_settings": octane,
        "preview_metrics": preview_benchmark.get("metrics", {}),
        "final_metrics": final_benchmark.get("metrics", {}),
        "preview_quality": preview_benchmark.get("quality_metrics", {}),
        "final_quality": final_benchmark.get("quality_metrics", {}),
        "preview_to_final_comparison": comparison.get("metrics", {}),
        "preview_to_final_diff_artifact": comparison.get("artifact_path", ""),
        "skipped_benchmarks": report.get("inner_report", {}).get("skipped_benchmarks", []),
    }


def render_markdown(report: dict) -> str:
    lines = [
        "# Octane Quality Sweep",
        "",
        f"- Report: `{report.get('json_out', '')}`",
        f"- Width x height: `{report.get('width', 0)}x{report.get('height', 0)}`",
        f"- Measured frames: `{report.get('measured_frames', 0)}`",
        "",
    ]
    for tier in report.get("tiers", []):
        tier_report = report["results"].get(tier, {})
        summary = tier_report.get("summary", {})
        final_metrics = summary.get("final_metrics", {})
        comparison = summary.get("preview_to_final_comparison", {})
        octane_settings = summary.get("octane_settings", {})
        lines.append(f"## `{tier}`")
        lines.append("")
        lines.append(f"- Return code: `{tier_report.get('returncode', -1)}`")
        lines.append(f"- Max samples: `{octane_settings.get('max_samples', '')}`")
        lines.append(f"- Adaptive threshold: `{octane_settings.get('adaptive_noise_threshold', '')}`")
        lines.append(f"- AI light: `{octane_settings.get('ai_light_enable', '')}`")
        lines.append(f"- Coherent ratio: `{octane_settings.get('coherent_ratio', '')}`")
        if final_metrics:
            lines.append(f"- Final median ms: `{final_metrics.get('median_ms', 0.0):.3f}`")
            lines.append(f"- Final median FPS: `{final_metrics.get('median_fps', 0.0):.3f}`")
        if comparison:
            lines.append(f"- Preview->final PSNR RGB: `{comparison.get('psnr_rgb', 0.0):.3f}`")
            lines.append(f"- Preview->final PSNR luma: `{comparison.get('psnr_luma', 0.0):.3f}`")
        skipped = summary.get("skipped_benchmarks", [])
        if skipped:
            lines.append(f"- Skipped: `{skipped}`")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    benchmark_script = source_dir / "scripts" / "run_blender_interactive_benchmark.py"
    if not benchmark_script.exists():
        raise SystemExit(f"Benchmark script not found: {benchmark_script}")
    json_out = pathlib.Path(args.json_out).resolve()
    md_out = pathlib.Path(args.md_out).resolve() if args.md_out else None
    log_out = pathlib.Path(args.log_out).resolve() if args.log_out else None
    readiness_report = (
        pathlib.Path(args.octane_readiness_report).resolve()
        if args.octane_readiness_report
        else None
    )

    report = {
        "json_out": str(json_out),
        "width": args.width,
        "height": args.height,
        "measured_frames": args.measured_frames,
        "warmup_frames": args.warmup_frames,
        "tiers": args.tiers,
        "results": {},
    }
    logs = []
    python = shutil.which("python3") or "python3"

    with tempfile.TemporaryDirectory(prefix="blackhole_octane_quality_sweep_") as tmp:
        temp_root = pathlib.Path(tmp)
        for tier in args.tiers:
            tier_json = temp_root / f"{tier}.json"
            tier_log = temp_root / f"{tier}.log"
            command = [
                python,
                str(benchmark_script),
                "--blender-executable",
                args.blender_executable,
                "--source-dir",
                str(source_dir),
                "--addon-zip",
                args.addon_zip,
                "--bridge-lib",
                args.bridge_lib,
                "--label",
                f"octane-{tier}",
                "--expect-engine",
                "octane",
                "--quality-tier",
                tier,
                "--width",
                str(args.width),
                "--height",
                str(args.height),
                "--measured-frames",
                str(args.measured_frames),
                "--warmup-frames",
                str(args.warmup_frames),
                "--scenario",
                "all",
                "--json-out",
                str(tier_json),
                "--log-out",
                str(tier_log),
                "--timeout-seconds",
                str(args.timeout_seconds),
            ]
            if readiness_report is not None:
                command.extend(["--octane-readiness-report", str(readiness_report)])
            proc = subprocess.run(command, capture_output=True, text=True, check=False)
            logs.append(f"== {tier} ==\n{proc.stdout}{proc.stderr}")
            tier_report = load_json(tier_json) if tier_json.exists() else {}
            report["results"][tier] = {
                "returncode": proc.returncode,
                "report_path": str(tier_json),
                "log_path": str(tier_log),
                "report": tier_report,
                "summary": summarize_tier(tier_report) if tier_report else {},
            }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_text(md_out, render_markdown(report))
    write_text(log_out, "\n\n".join(logs))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
