#!/usr/bin/env python3
"""Verify a generated Blender interactive benchmark report."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys


REQUIRED_METRICS = (
    "sample_count",
    "mean_ms",
    "median_ms",
    "min_ms",
    "max_ms",
    "p95_ms",
    "p99_ms",
    "mean_fps",
    "median_fps",
    "one_percent_low_fps",
    "hitch_threshold_ms",
    "hitch_count",
)

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
    parser.add_argument("--expect-engine", choices=["blackhole", "octane", "cycles"])
    parser.add_argument("--expect-scene-profile")
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    return parser.parse_args(argv)


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    inner = report.get("inner_report", {})
    mcp_scene = report.get("mcp_scene_report", {})
    lines = [
        "# Blender Interactive Benchmark Verification",
        "",
        f"- Report: `{report.get('report_path', '')}`",
        f"- Label: `{report.get('label', '')}`",
        f"- Return code: `{report.get('returncode', -1)}`",
        f"- Status: `{inner.get('status', '')}`",
        f"- Resolution: `{inner.get('width', 0)}x{inner.get('height', 0)}`",
        f"- Scenario: `{inner.get('scenario', '')}`",
        f"- Expected engine: `{report.get('expect_engine', '')}`",
        f"- Quality tier: `{report.get('quality_tier', inner.get('quality_tier', ''))}`",
        f"- Scene profile: `{report.get('scene_profile', inner.get('scene_profile', ''))}`",
        f"- MCP scene enabled: `{bool(report.get('mcp_scene_enabled', False))}`",
        "",
    ]
    if mcp_scene:
        final_scene = mcp_scene.get("final_scene_info", {}).get("result", {})
        lines.append("## `mcp_scene`")
        lines.append("")
        lines.append(f"- Blend exists: `{bool(mcp_scene.get('blend_exists', False))}`")
        lines.append(f"- Port: `{mcp_scene.get('port', 0)}`")
        lines.append(f"- Final object count: `{final_scene.get('object_count', 0)}`")
        lines.append("")
    octane_server = report.get("octane_server", {})
    octane_readiness = report.get("octane_readiness", {})
    if octane_server:
        lines.append("## `octane_server`")
        lines.append("")
        lines.append(f"- Running: `{bool(octane_server.get('running', False))}`")
        lines.append(f"- Binary: `{octane_server.get('binary', '')}`")
        lines.append("")
    if octane_readiness:
        lines.append("## `octane_readiness`")
        lines.append("")
        lines.append(f"- Classification: `{octane_readiness.get('readiness', '')}`")
        lines.append(f"- Ready for automation: `{bool(octane_readiness.get('ready_for_automation', False))}`")
        lines.append(f"- Reason: `{octane_readiness.get('reason', '')}`")
        lines.append("")
    for benchmark in inner.get("benchmarks", []):
        metrics = benchmark.get("metrics", {})
        lines.append(f"## `{benchmark.get('name', '')}`")
        lines.append("")
        lines.append(f"- Backend: `{benchmark.get('backend', '')}`")
        lines.append(f"- Samples: `{metrics.get('sample_count', 0)}`")
        lines.append(f"- Median ms: `{metrics.get('median_ms', 0.0):.3f}`")
        lines.append(f"- Median FPS: `{metrics.get('median_fps', 0.0):.3f}`")
        lines.append(f"- Artifact: `{benchmark.get('artifact_path', '')}`")
        lines.append("")
    for comparison in inner.get("comparisons", []):
        metrics = comparison.get("metrics", {})
        lines.append(f"## `{comparison.get('candidate', '')} vs {comparison.get('reference', '')}`")
        lines.append("")
        lines.append(f"- Diff artifact: `{comparison.get('artifact_path', '')}`")
        lines.append(f"- PSNR RGB: `{metrics.get('psnr_rgb', 0.0):.3f}`")
        lines.append(f"- PSNR luma: `{metrics.get('psnr_luma', 0.0):.3f}`")
        lines.append(f"- MAE luma: `{metrics.get('mae_luma', 0.0):.6f}`")
        lines.append(f"- Luma cosine similarity: `{metrics.get('luma_cosine_similarity', 0.0):.6f}`")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report_path = args.report.resolve()
    if not report_path.exists():
        raise SystemExit(f"Benchmark report not found: {report_path}")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    report["report_path"] = str(report_path)
    inner = report.get("inner_report", {})

    require(report.get("returncode") == 0, f"Benchmark report return code was non-zero: {report.get('returncode')}")
    require(inner.get("status") == "success", f"Benchmark inner status was not success: {inner.get('status')}")
    if args.expect_engine:
        require(
            report.get("expect_engine") == args.expect_engine,
            f"Benchmark report expected engine {args.expect_engine} but recorded {report.get('expect_engine')}",
        )
    if args.expect_scene_profile:
        actual_scene_profile = report.get("scene_profile") or inner.get("scene_profile")
        require(
            actual_scene_profile == args.expect_scene_profile,
            f"Benchmark report expected scene profile {args.expect_scene_profile} but recorded {actual_scene_profile}",
        )
    if report.get("expect_engine") == "octane":
        octane_server = report.get("octane_server", {})
        require(bool(octane_server), "Octane benchmark report did not record Octane server status")
        octane_readiness = report.get("octane_readiness", {})
        require(bool(octane_readiness), "Octane benchmark report did not record Octane readiness state")
        require(
            octane_readiness.get("readiness") in {"ready", "setup_required", "server_unavailable", "probe_failed", "not_ready"},
            f"Octane readiness classification was unexpected: {octane_readiness.get('readiness')}",
        )

    if report.get("mcp_scene_enabled"):
        mcp_scene = report.get("mcp_scene_report", {})
        require(bool(mcp_scene), "Benchmark report enabled MCP scene setup but did not record its report")
        require(mcp_scene.get("status") == "success", f"MCP scene report status was not success: {mcp_scene.get('status')}")
        require(bool(mcp_scene.get("blend_exists")), "MCP scene report did not confirm benchmark scene blend output")
        final_scene = mcp_scene.get("final_scene_info", {}).get("result", {})
        object_names = {obj.get("name", "") for obj in final_scene.get("objects", [])}
        require("EventHorizon" in object_names, "MCP scene report did not include EventHorizon")
        require("AccretionDisk" in object_names, "MCP scene report did not include AccretionDisk")
        if report.get("expect_engine") == "octane":
            setup_output = mcp_scene.get("setup_response", {}).get("result", {}).get("result", "")
            require("Octane materials configured" in setup_output, "MCP scene report did not confirm Octane material setup")

    bridge_path = pathlib.Path(inner.get("bridge_library_path", ""))
    require(bridge_path.exists(), f"Bridge library path recorded in benchmark report does not exist: {bridge_path}")

    capabilities = inner.get("bridge_capabilities", {})
    require(int(capabilities.get("source_params_size", 0)) > 0, "Benchmark report missing source_params_size")
    require(int(capabilities.get("disk_params_size", 0)) > 0, "Benchmark report missing disk_params_size")
    studio_quality = inner.get("studio_quality", {})
    require(bool(studio_quality), "Benchmark report did not record studio_quality settings")
    require(bool(studio_quality.get("engine")), "Benchmark report studio_quality missing engine")
    require(bool(studio_quality.get("view_transform")), "Benchmark report studio_quality missing view transform")
    require(bool(report.get("quality_tier") or inner.get("quality_tier")), "Benchmark report missing quality tier")
    require(bool(report.get("scene_profile") or inner.get("scene_profile")), "Benchmark report missing scene profile")
    require(
        bool(studio_quality.get("quality_tier")),
        "Benchmark report studio_quality missing applied quality tier",
    )

    benchmarks = inner.get("benchmarks", [])
    require(bool(benchmarks), "Benchmark report did not record any benchmark entries")

    names = {benchmark.get("name", "") for benchmark in benchmarks}
    require("bridge_lensing_preview" in names, "Benchmark report did not include bridge_lensing_preview")

    if capabilities.get("cuda"):
        require(
            bool({"bridge_cuda_preview", "render_engine_final"} & names),
            "CUDA-capable benchmark report did not include a CUDA-backed benchmark",
        )
    if report.get("expect_engine") == "octane" and "render_engine_final" not in names:
        skipped = {entry.get("name", ""): entry.get("reason", "") for entry in inner.get("skipped_benchmarks", [])}
        require(
            "render_engine_final" in skipped,
            "Octane benchmark omitted render_engine_final without recording a skip reason",
        )
        readiness_reason = report.get("octane_readiness", {}).get("reason", "")
        if readiness_reason:
            require(
                skipped.get("render_engine_final", "") == readiness_reason,
                "Octane benchmark skip reason did not match the Octane readiness probe",
            )

    for benchmark in benchmarks:
        frame_times = benchmark.get("frame_times_ms", [])
        metrics = benchmark.get("metrics", {})
        require(bool(frame_times), f"Benchmark {benchmark.get('name', '')} did not record frame times")
        require(int(metrics.get("sample_count", 0)) == len(frame_times), f"Benchmark {benchmark.get('name', '')} sample count mismatch")
        for key in REQUIRED_METRICS:
            require(key in metrics, f"Benchmark {benchmark.get('name', '')} missing metric {key}")
        signature = benchmark.get("result_signature", {})
        shape = signature.get("shape", [])
        require(len(shape) == 3 and shape[2] == 4, f"Benchmark {benchmark.get('name', '')} recorded invalid result shape {shape}")
        artifact_path = pathlib.Path(benchmark.get("artifact_path", ""))
        require(artifact_path.exists(), f"Benchmark {benchmark.get('name', '')} did not write an artifact image: {artifact_path}")
        quality_metrics = benchmark.get("quality_metrics", {})
        require(bool(quality_metrics), f"Benchmark {benchmark.get('name', '')} missing quality metrics")
        require(quality_metrics.get("nonzero_rgb_fraction", 0.0) > 0.0, f"Benchmark {benchmark.get('name', '')} appears blank")
        require(quality_metrics.get("max_luma", 0.0) > 0.0, f"Benchmark {benchmark.get('name', '')} has zero luminance")

    comparisons = inner.get("comparisons", [])
    if report.get("expect_engine") == "octane" and "bridge_cuda_preview" in names and "render_engine_final" in names:
        expected = ("bridge_cuda_preview", "render_engine_final")
        comparison_keys = {(entry.get("reference", ""), entry.get("candidate", "")) for entry in comparisons}
        require(
            expected in comparison_keys,
            "Octane benchmark report did not include comparison evidence between bridge_cuda_preview and render_engine_final",
        )
    for comparison in comparisons:
        reference = comparison.get("reference", "")
        candidate = comparison.get("candidate", "")
        require(reference in names, f"Comparison referenced missing benchmark {reference}")
        require(candidate in names, f"Comparison referenced missing benchmark {candidate}")
        artifact_path = pathlib.Path(comparison.get("artifact_path", ""))
        require(artifact_path.exists(), f"Comparison artifact missing: {artifact_path}")
        metrics = comparison.get("metrics", {})
        for key in REQUIRED_COMPARISON_METRICS:
            require(key in metrics, f"Comparison {candidate} vs {reference} missing metric {key}")
        require(metrics.get("psnr_rgb", 0.0) >= 0.0, f"Comparison {candidate} vs {reference} invalid psnr_rgb")
        require(
            0.0 <= metrics.get("luma_cosine_similarity", 0.0) <= 1.000001,
            f"Comparison {candidate} vs {reference} invalid luma cosine similarity",
        )

    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
