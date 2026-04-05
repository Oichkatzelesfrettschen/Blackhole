#!/usr/bin/env python3
"""Assemble a stable Blackhole showcase gallery from verified benchmark renders."""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--host-label", required=True)
    parser.add_argument("--baseline-report", type=pathlib.Path, required=True)
    parser.add_argument("--harsh-report", type=pathlib.Path, required=True)
    parser.add_argument("--artifact-dir", type=pathlib.Path, required=True)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--md-out", type=pathlib.Path)
    return parser.parse_args()


def load_json(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def benchmark_by_name(inner_report: dict, name: str) -> dict:
    for item in inner_report.get("benchmarks", []):
        if item.get("name") == name:
            return item
    raise RuntimeError(f"Benchmark '{name}' not found")


def comparison_by_pair(inner_report: dict, reference: str, candidate: str) -> dict:
    for item in inner_report.get("comparisons", []):
        if item.get("reference") == reference and item.get("candidate") == candidate:
            return item
    raise RuntimeError(f"Comparison '{reference}' vs '{candidate}' not found")


def copy_required(src_path: str, dst_path: pathlib.Path) -> str:
    src = pathlib.Path(src_path)
    if not src.exists():
        raise RuntimeError(f"Required showcase artifact missing: {src}")
    dst_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst_path)
    return str(dst_path)


def scene_entry(scene_profile: str, report_path: pathlib.Path, payload: dict, artifact_dir: pathlib.Path) -> dict:
    inner = payload.get("inner_report", {})
    final_render = benchmark_by_name(inner, "render_engine_final")
    bridge_preview = benchmark_by_name(inner, "bridge_cuda_preview")
    final_diff = comparison_by_pair(inner, "bridge_cuda_preview", "render_engine_final")
    native_render = None
    native_diff = None
    native_to_hybrid_diff = None
    benchmark_names = {item.get("name", "") for item in inner.get("benchmarks", [])}
    if "render_engine_native_final" in benchmark_names:
        native_render = benchmark_by_name(inner, "render_engine_native_final")
        native_diff = comparison_by_pair(inner, "bridge_cuda_preview", "render_engine_native_final")
        native_to_hybrid_diff = comparison_by_pair(inner, "render_engine_native_final", "render_engine_final")
    prefix = "baseline" if scene_profile == "baseline" else "harsh_lighting"
    final_target = artifact_dir / f"{prefix}_final.png"
    preview_target = artifact_dir / f"{prefix}_bridge_cuda_preview.png"
    diff_target = artifact_dir / f"{prefix}_final_vs_bridge_cuda_diff.png"
    scene = {
        "scene_profile": scene_profile,
        "source_report": str(report_path),
        "selected_engine": inner.get("selected_engine", ""),
        "mcp_scene_status": payload.get("mcp_scene_report", {}).get("status", ""),
        "measured_frames": payload.get("measured_frames", 0),
        "render_path": copy_required(final_render.get("artifact_path", ""), final_target),
        "bridge_preview_path": copy_required(bridge_preview.get("artifact_path", ""), preview_target),
        "comparison_diff_path": copy_required(final_diff.get("artifact_path", ""), diff_target),
        "render_metrics": final_render.get("metrics", {}),
        "render_quality_metrics": final_render.get("quality_metrics", {}),
        "bridge_preview_metrics": bridge_preview.get("metrics", {}),
        "comparison_metrics": final_diff.get("metrics", {}),
        "render_mode": "hybrid" if native_render is not None else "native",
    }
    if native_render is not None and native_diff is not None:
        native_target = artifact_dir / f"{prefix}_native_proxy_final.png"
        native_diff_target = artifact_dir / f"{prefix}_native_proxy_vs_bridge_cuda_diff.png"
        native_to_hybrid_target = artifact_dir / f"{prefix}_hybrid_vs_native_proxy_diff.png"
        scene.update(
            {
                "native_render_path": copy_required(native_render.get("artifact_path", ""), native_target),
                "native_comparison_diff_path": copy_required(native_diff.get("artifact_path", ""), native_diff_target),
                "native_comparison_metrics": native_diff.get("metrics", {}),
                "native_render_metrics": native_render.get("metrics", {}),
                "native_render_quality_metrics": native_render.get("quality_metrics", {}),
                "hybrid_vs_native_diff_path": copy_required(
                    native_to_hybrid_diff.get("artifact_path", ""), native_to_hybrid_target
                ) if native_to_hybrid_diff is not None else "",
                "hybrid_vs_native_metrics": native_to_hybrid_diff.get("metrics", {}) if native_to_hybrid_diff else {},
            }
        )
    return scene


def build_markdown(report: dict) -> str:
    lines = [
        f"# {report['label']}",
        "",
        f"- Host: `{report['host_label']}`",
        f"- Status: `{report['status']}`",
        f"- Engine: `{report['selected_engine']}`",
        "",
    ]
    for scene in report.get("scenes", []):
        render_metrics = scene.get("render_metrics", {})
        comparison_metrics = scene.get("comparison_metrics", {})
        lines.extend(
            [
                f"## {scene.get('scene_profile', '')}",
                "",
                f"- Render mode: `{scene.get('render_mode', 'native')}`",
                f"- Final render: `{scene.get('render_path', '')}`",
                f"- CUDA preview: `{scene.get('bridge_preview_path', '')}`",
                f"- Diff heatmap: `{scene.get('comparison_diff_path', '')}`",
                f"- Median final frame time: `{render_metrics.get('median_ms', 0.0):.3f} ms`",
                f"- Mean final FPS: `{render_metrics.get('mean_fps', 0.0):.3f}`",
                f"- Preview/final PSNR RGB: `{comparison_metrics.get('psnr_rgb', 0.0):.3f}`",
                f"- Preview/final PSNR luma: `{comparison_metrics.get('psnr_luma', 0.0):.3f}`",
                "",
            ]
        )
        if scene.get("native_render_path"):
            native_metrics = scene.get("native_render_metrics", {})
            native_compare = scene.get("native_comparison_metrics", {})
            lines.extend(
                [
                    f"- Native proxy render: `{scene.get('native_render_path', '')}`",
                    f"- Native proxy diff: `{scene.get('native_comparison_diff_path', '')}`",
                    f"- Native median frame time: `{native_metrics.get('median_ms', 0.0):.3f} ms`",
                    f"- Preview/native PSNR RGB: `{native_compare.get('psnr_rgb', 0.0):.3f}`",
                    "",
                ]
            )
    return "\n".join(lines).strip() + "\n"


def main() -> int:
    args = parse_args()
    baseline_payload = load_json(args.baseline_report)
    harsh_payload = load_json(args.harsh_report)
    args.artifact_dir.mkdir(parents=True, exist_ok=True)

    baseline_scene = scene_entry("baseline", args.baseline_report, baseline_payload, args.artifact_dir)
    harsh_scene = scene_entry("harsh_lighting", args.harsh_report, harsh_payload, args.artifact_dir)
    selected_engine = baseline_scene.get("selected_engine") or harsh_scene.get("selected_engine", "")
    report = {
        "label": args.label,
        "host_label": args.host_label,
        "status": "success",
        "selected_engine": selected_engine,
        "artifact_dir": str(args.artifact_dir.resolve()),
        "scenes": [baseline_scene, harsh_scene],
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.md_out is not None:
        args.md_out.parent.mkdir(parents=True, exist_ok=True)
        args.md_out.write_text(build_markdown(report), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
