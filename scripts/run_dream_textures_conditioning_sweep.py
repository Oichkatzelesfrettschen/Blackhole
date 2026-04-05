#!/usr/bin/env python3
"""Run Dream Textures conditioning modes and compare the resulting artifacts."""

from __future__ import annotations

import argparse
import json
import math
import pathlib
import shutil
import subprocess
import tempfile
import time
from typing import Any

import numpy as np
from PIL import Image


DEFAULT_MODES = ("none", "image", "depth", "image_depth")
DEFAULT_TEXT_MODEL_ID = "stabilityai/sdxl-turbo"
DEFAULT_DEPTH_MODEL_ID = "carsonkatri/stable-diffusion-2-depth-diffusers"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--user-scripts", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--width", type=int, default=64)
    parser.add_argument("--height", type=int, default=64)
    parser.add_argument("--scene-profile", choices=("baseline", "harsh_lighting"), default="baseline")
    parser.add_argument("--steps", type=int, default=8)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--timeout-seconds", type=float, default=180.0)
    parser.add_argument("--prompt-style", choices=("scientific", "hybrid", "cinematic"), default="scientific")
    parser.add_argument("--text-model-id", default=DEFAULT_TEXT_MODEL_ID)
    parser.add_argument("--depth-model-id", default=DEFAULT_DEPTH_MODEL_ID)
    parser.add_argument("--modes", nargs="+", default=list(DEFAULT_MODES))
    parser.add_argument("--sanitize-ocio", action="store_true")
    parser.add_argument(
        "--memory-profile",
        choices=("default", "conditioning_sweep", "low_vram"),
        default="conditioning_sweep",
    )
    return parser.parse_args()


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def load_png(path: pathlib.Path) -> np.ndarray[Any, np.dtype[np.float32]]:
    image = Image.open(path).convert("RGBA")
    return np.asarray(image, dtype=np.float32) / 255.0


def save_png(path: pathlib.Path, array: np.ndarray[Any, np.dtype[np.float32]]) -> None:
    rgba = np.clip(np.asarray(array, dtype=np.float32), 0.0, 1.0)
    path.parent.mkdir(parents=True, exist_ok=True)
    Image.fromarray((rgba * 255.0).round().astype(np.uint8), mode="RGBA").save(path)


def compute_comparison_metrics(
    reference: np.ndarray[Any, np.dtype[np.float32]],
    candidate: np.ndarray[Any, np.dtype[np.float32]],
) -> tuple[dict[str, float], np.ndarray[Any, np.dtype[np.float32]]]:
    ref = np.clip(np.asarray(reference, dtype=np.float64), 0.0, 1.0)
    cur = np.clip(np.asarray(candidate, dtype=np.float64), 0.0, 1.0)
    if ref.shape != cur.shape:
        raise RuntimeError(f"Conditioning sweep requires equal shapes, got {ref.shape} vs {cur.shape}")
    ref_rgb = ref[..., :3]
    cur_rgb = cur[..., :3]
    diff_rgb = cur_rgb - ref_rgb
    abs_diff_rgb = np.abs(diff_rgb)
    mae_rgb = float(np.mean(abs_diff_rgb))
    rmse_rgb = float(np.sqrt(np.mean(np.square(diff_rgb))))
    max_abs_diff_rgb = float(np.max(abs_diff_rgb))

    ref_luma = 0.2126 * ref_rgb[..., 0] + 0.7152 * ref_rgb[..., 1] + 0.0722 * ref_rgb[..., 2]
    cur_luma = 0.2126 * cur_rgb[..., 0] + 0.7152 * cur_rgb[..., 1] + 0.0722 * cur_rgb[..., 2]
    diff_luma = cur_luma - ref_luma
    abs_diff_luma = np.abs(diff_luma)
    mae_luma = float(np.mean(abs_diff_luma))
    rmse_luma = float(np.sqrt(np.mean(np.square(diff_luma))))
    max_abs_diff_luma = float(np.max(abs_diff_luma))
    ref_mean = float(np.mean(ref_luma))
    cur_mean = float(np.mean(cur_luma))
    denom = float(np.sqrt(np.sum(np.square(ref_luma))) * np.sqrt(np.sum(np.square(cur_luma))))
    cosine_similarity = float(np.sum(ref_luma * cur_luma) / denom) if denom > 0.0 else 0.0
    psnr_rgb = float(20.0 * math.log10(1.0 / max(rmse_rgb, 1.0e-8)))
    psnr_luma = float(20.0 * math.log10(1.0 / max(rmse_luma, 1.0e-8)))

    diff_norm = abs_diff_luma / max(max_abs_diff_luma, 1.0e-8)
    heatmap = np.zeros(ref.shape, dtype=np.float32)
    heatmap[..., 0] = diff_norm.astype(np.float32)
    heatmap[..., 1] = np.sqrt(diff_norm).astype(np.float32) * 0.35
    heatmap[..., 2] = (1.0 - diff_norm).astype(np.float32) * 0.15
    heatmap[..., 3] = 1.0
    return (
        {
            "mae_rgb": mae_rgb,
            "rmse_rgb": rmse_rgb,
            "max_abs_diff_rgb": max_abs_diff_rgb,
            "psnr_rgb": psnr_rgb,
            "mae_luma": mae_luma,
            "rmse_luma": rmse_luma,
            "max_abs_diff_luma": max_abs_diff_luma,
            "psnr_luma": psnr_luma,
            "reference_mean_luma": ref_mean,
            "candidate_mean_luma": cur_mean,
            "luma_cosine_similarity": cosine_similarity,
        },
        heatmap,
    )


def summarize_mode(mode: str, report: dict[str, Any]) -> dict[str, Any]:
    inner = report.get("inner_report", {})
    conditioning = inner.get("conditioning_policy", {})
    return {
        "mode": mode,
        "returncode": report.get("returncode", -1),
        "status": inner.get("status", ""),
        "artifact_path": inner.get("artifact_path", ""),
        "mean": inner.get("mean", 0.0),
        "elapsed_seconds": report.get("elapsed_seconds", 0.0),
        "model_id": inner.get("model_id", ""),
        "conditioning_policy": conditioning,
        "asset_digest": inner.get("asset_digest", {}),
    }


def model_for_mode(mode: str, text_model_id: str, depth_model_id: str) -> str:
    if mode in {"depth", "image_depth"}:
        return depth_model_id
    return text_model_id


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Dream Textures Conditioning Sweep",
        "",
        f"- Label: `{report.get('label', '')}`",
        f"- Modes: `{report.get('modes', [])}`",
        f"- Scene profile: `{report.get('scene_profile', '')}`",
        f"- Memory profile: `{report.get('memory_profile', '')}`",
        f"- Text/image model: `{report.get('text_model_id', '')}`",
        f"- Depth/image+depth model: `{report.get('depth_model_id', '')}`",
        "",
    ]
    for mode in report.get("modes", []):
        result = report.get("results", {}).get(mode, {})
        summary = result.get("summary", {})
        conditioning = summary.get("conditioning_policy", {})
        lines.append(f"## `{mode}`")
        lines.append("")
        lines.append(f"- Return code: `{result.get('returncode', -1)}`")
        lines.append(f"- Model: `{summary.get('model_id', '')}`")
        lines.append(f"- Status: `{summary.get('status', '')}`")
        lines.append(f"- Artifact: `{summary.get('artifact_path', '')}`")
        lines.append(f"- Mean: `{summary.get('mean', 0.0):.6f}`")
        lines.append(f"- Elapsed: `{summary.get('elapsed_seconds', 0.0):.3f}` s")
        lines.append(f"- Effective mode: `{conditioning.get('effective_mode', '')}`")
        lines.append(f"- Source origin: `{conditioning.get('source_origin', '')}`")
        lines.append("")
    for comparison in report.get("comparisons", []):
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


def main() -> int:
    args = parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    verify_script = source_dir / "scripts" / "verify_dream_textures_direct_pipeline.py"
    python = shutil.which("python3") or "python3"
    json_out = args.json_out.resolve()
    md_out = args.md_out.resolve() if args.md_out else None
    log_out = args.log_out.resolve() if args.log_out else None
    artifact_root = json_out.parent / f"{json_out.stem}_artifacts"
    shutil.rmtree(artifact_root, ignore_errors=True)
    artifact_root.mkdir(parents=True, exist_ok=True)

    report: dict[str, Any] = {
        "label": args.label,
        "text_model_id": args.text_model_id,
        "depth_model_id": args.depth_model_id,
        "modes": args.modes,
        "width": args.width,
        "height": args.height,
        "scene_profile": args.scene_profile,
        "steps": args.steps,
        "seed": args.seed,
        "memory_profile": args.memory_profile,
        "results": {},
        "comparisons": [],
    }
    logs: list[str] = []
    mode_failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="blackhole_dream_conditioning_sweep_") as tmp:
        temp_root = pathlib.Path(tmp)
        for mode in args.modes:
            mode_json = temp_root / f"{mode}.json"
            mode_md = temp_root / f"{mode}.md"
            mode_log = temp_root / f"{mode}.log"
            mode_artifact = artifact_root / f"{mode}.png"
            model_id = model_for_mode(mode, args.text_model_id, args.depth_model_id)
            command = [
                python,
                str(verify_script),
                "--label",
                f"{args.label}-{mode}",
                "--blender-executable",
                args.blender_executable,
                "--source-dir",
                str(source_dir),
                "--model-id",
                model_id,
                "--prompt-style",
                args.prompt_style,
                "--conditioning-mode",
                mode,
                "--scene-profile",
                args.scene_profile,
                "--width",
                str(args.width),
                "--height",
                str(args.height),
                "--steps",
                str(args.steps),
                "--seed",
                str(args.seed),
                "--timeout-seconds",
                str(args.timeout_seconds),
                "--memory-profile",
                args.memory_profile,
                "--json-out",
                str(mode_json),
                "--md-out",
                str(mode_md),
                "--log-out",
                str(mode_log),
                "--artifact-out",
                str(mode_artifact),
            ]
            if args.user_scripts is not None:
                command.extend(["--user-scripts", str(args.user_scripts.resolve())])
            if args.sanitize_ocio:
                command.append("--sanitize-ocio")
            start = time.perf_counter()
            proc = subprocess.run(command, capture_output=True, text=True, check=False)
            elapsed_seconds = time.perf_counter() - start
            logs.append(f"== {mode} ==\n{proc.stdout}{proc.stderr}")
            mode_report = json.loads(mode_json.read_text(encoding="utf-8")) if mode_json.exists() else {}
            mode_report["elapsed_seconds"] = elapsed_seconds
            report["results"][mode] = {
                "returncode": proc.returncode,
                "elapsed_seconds": elapsed_seconds,
                "report_path": str(mode_json),
                "log_path": str(mode_log),
                "artifact_path": str(mode_artifact),
                "model_id": model_id,
                "report": mode_report,
                "summary": summarize_mode(mode, mode_report),
            }
            summary = report["results"][mode]["summary"]
            if proc.returncode != 0:
                mode_failures.append(
                    f"{mode}: returncode={proc.returncode} log={mode_log}"
                )
                continue
            if summary.get("status") != "success":
                error = mode_report.get("inner_report", {}).get("error", "")
                mode_failures.append(
                    f"{mode}: status={summary.get('status')} error={error}"
                )
                continue
            if not mode_artifact.exists():
                mode_failures.append(
                    f"{mode}: artifact_missing path={mode_artifact}"
                )

        if mode_failures:
            report["mode_failures"] = mode_failures
            json_out.parent.mkdir(parents=True, exist_ok=True)
            json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            write_text(md_out, render_markdown(report))
            write_text(log_out, "\n\n".join(logs))
            raise SystemExit(
                "Dream Textures conditioning sweep failed before comparisons: "
                + "; ".join(mode_failures)
            )

        artifact_arrays = {
            mode: load_png(pathlib.Path(report["results"][mode]["artifact_path"]))
            for mode in args.modes
        }
        comparison_pairs = [
            ("none", "image"),
            ("none", "depth"),
            ("none", "image_depth"),
            ("image", "depth"),
            ("image", "image_depth"),
            ("depth", "image_depth"),
        ]
        for reference, candidate in comparison_pairs:
            if reference not in artifact_arrays or candidate not in artifact_arrays:
                continue
            metrics, heatmap = compute_comparison_metrics(
                artifact_arrays[reference],
                artifact_arrays[candidate],
            )
            diff_path = temp_root / f"{candidate}_vs_{reference}_diff.png"
            persistent_diff_path = artifact_root / f"{candidate}_vs_{reference}_diff.png"
            save_png(diff_path, heatmap)
            shutil.copy2(diff_path, persistent_diff_path)
            report["comparisons"].append(
                {
                    "reference": reference,
                    "candidate": candidate,
                    "artifact_path": str(persistent_diff_path),
                    "metrics": metrics,
                }
            )

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_text(md_out, render_markdown(report))
    write_text(log_out, "\n\n".join(logs))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
