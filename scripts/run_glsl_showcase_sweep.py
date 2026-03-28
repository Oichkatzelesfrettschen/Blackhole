#!/usr/bin/env python3
"""Sweep the GLSL showcase-orbit profile and keep the strongest stills."""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import shutil
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path

from PIL import Image, ImageDraw, ImageStat


@dataclass(frozen=True)
class SweepCase:
    distance: float
    pitch: float
    fov: float
    exposure: float
    yaw: float
    sweep_deg: float
    composition: str


@dataclass
class SweepResult:
    params: SweepCase
    frame_path: str
    brightness_mean: float
    brightness_std: float
    center_mean: float
    highlight_fraction: float
    score: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-dir",
        type=Path,
        default=Path("/home/eirikr/Github/Blackhole"),
    )
    parser.add_argument(
        "--runner",
        type=Path,
        default=Path("/home/eirikr/Github/Blackhole/scripts/run_glsl_headless.py"),
    )
    parser.add_argument("--backend", choices=("hidden", "xvfb"), default="hidden")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/home/eirikr/Github/Blackhole/.cache/showcase_glsl_sweep"),
    )
    parser.add_argument("--width", type=int, default=2560)
    parser.add_argument("--height", type=int, default=1004)
    parser.add_argument("--frames", type=int, default=1)
    parser.add_argument("--yaw", type=float, default=-90.0)
    parser.add_argument("--sweep-deg", type=float, default=0.0)
    parser.add_argument(
        "--record-composition",
        default="wide-right",
        choices=("centered", "left-third", "right-third", "wide-left", "wide-right"),
    )
    parser.add_argument("--record-background-id")
    parser.add_argument("--top-k", type=int, default=6)
    return parser.parse_args()


def run_case(
    repo_root: Path,
    runner: Path,
    backend: str,
    record_background_id: str | None,
    output_root: Path,
    index: int,
    width: int,
    height: int,
    frames: int,
    case: SweepCase,
) -> Path:
    case_dir = output_root / f"case_{index:02d}"
    if case_dir.exists():
        shutil.rmtree(case_dir)
    case_dir.mkdir(parents=True, exist_ok=True)
    log_path = case_dir / "run.log"
    command = [
        "python3",
        str(runner),
        "--backend",
        backend,
        "--record-dir",
        str(case_dir),
        "--record-frames",
        str(frames),
        "--width",
        str(width),
        "--height",
        str(height),
        "--record-profile",
        "showcase-orbit",
        "--record-composition",
        case.composition,
        "--record-yaw",
        f"{case.yaw:.3f}",
        "--record-pitch",
        f"{case.pitch:.3f}",
        "--record-distance",
        f"{case.distance:.3f}",
        "--record-fov",
        f"{case.fov:.3f}",
        "--record-exposure",
        f"{case.exposure:.5f}",
        "--record-sweep-deg",
        f"{case.sweep_deg:.3f}",
    ]
    if record_background_id:
        command.extend(["--record-background-id", record_background_id])
    with log_path.open("w", encoding="utf-8") as log_file:
        subprocess.run(
            command,
            check=True,
            cwd=repo_root,
            stdout=log_file,
            stderr=subprocess.STDOUT,
        )
    frame_path = case_dir / "frame_000000.png"
    if not frame_path.exists():
        raise FileNotFoundError(f"expected frame missing: {frame_path}")
    return frame_path


def image_metrics(frame_path: Path) -> tuple[float, float, float, float]:
    image = Image.open(frame_path).convert("RGB")
    total = max(image.size[0] * image.size[1], 1)
    luminance = image.convert("L")
    luminance_stats = ImageStat.Stat(luminance)
    brightness_mean = luminance_stats.mean[0] / 255.0
    brightness_std = luminance_stats.stddev[0] / 255.0
    width, height = image.size
    crop = image.crop(
        (
            int(width * 0.35),
            int(height * 0.3),
            int(width * 0.65),
            int(height * 0.7),
        )
    )
    center_mean = ImageStat.Stat(crop.convert("L")).mean[0] / 255.0
    rgb_hist = image.histogram()
    highlight_count = 0
    for channel in range(3):
        start = channel * 256
        highlight_count += sum(rgb_hist[start + 245 : start + 256])
    highlight_fraction = highlight_count / float(total * 3)
    return brightness_mean, brightness_std, center_mean, highlight_fraction


def score_frame(
    brightness_mean: float,
    brightness_std: float,
    center_mean: float,
    highlight_fraction: float,
) -> float:
    target_mean = 0.22
    target_center = 0.08
    score = 0.0
    score += max(0.0, 1.0 - abs(brightness_mean - target_mean) / 0.15) * 2.0
    score += min(brightness_std / 0.18, 1.0) * 2.5
    score += max(0.0, 1.0 - abs(center_mean - target_center) / 0.12) * 1.5
    score += max(0.0, 1.0 - abs(highlight_fraction - 0.008) / 0.02) * 1.0
    return score


def write_contact_sheet(results: list[SweepResult], destination: Path) -> None:
    thumbs = []
    for result in results:
        image = Image.open(result.frame_path).convert("RGB")
        image.thumbnail((360, 202))
        canvas = Image.new("RGB", (380, 260), (12, 12, 12))
        canvas.paste(image, ((380 - image.width) // 2, 10))
        draw = ImageDraw.Draw(canvas)
        params = result.params
        lines = [
            f"score {result.score:.2f}",
            f"d={params.distance:.1f} p={params.pitch:.1f} fov={params.fov:.1f}",
            f"exp={params.exposure:.3f} yaw={params.yaw:.1f}",
            params.composition,
            Path(result.frame_path).parent.name,
        ]
        y = 208
        for line in lines:
            draw.text((12, y), line, fill=(230, 230, 230))
            y += 12
        thumbs.append(canvas)
    if not thumbs:
        return
    columns = 3
    rows = math.ceil(len(thumbs) / columns)
    sheet = Image.new("RGB", (columns * 380, rows * 260), (0, 0, 0))
    for index, thumb in enumerate(thumbs):
        x = (index % columns) * 380
        y = (index // columns) * 260
        sheet.paste(thumb, (x, y))
    destination.parent.mkdir(parents=True, exist_ok=True)
    sheet.save(destination)


def main() -> int:
    args = parse_args()
    repo_root = args.source_dir.resolve()
    runner = args.runner.resolve()
    output_root = args.output_dir.resolve()
    output_root.mkdir(parents=True, exist_ok=True)

    distances = [13.0, 14.0, 15.5]
    pitches = [-8.0, -6.0, -3.0]
    fovs = [62.0, 68.0, 74.0]
    exposures = [2.8, 3.4, 4.2]

    cases = [
        SweepCase(
            distance=distance,
            pitch=pitch,
            fov=fov,
            exposure=exposure,
            yaw=args.yaw,
            sweep_deg=args.sweep_deg,
            composition=args.record_composition,
        )
        for distance, pitch, fov, exposure in itertools.product(
            distances, pitches, fovs, exposures
        )
    ]

    results: list[SweepResult] = []
    for index, case in enumerate(cases):
        print(
            f"[{index + 1:02d}/{len(cases):02d}] "
            f"{case.composition} d={case.distance:.1f} "
            f"p={case.pitch:.1f} fov={case.fov:.1f} exp={case.exposure:.3f}"
        )
        frame_path = run_case(
            repo_root=repo_root,
            runner=runner,
            backend=args.backend,
            record_background_id=args.record_background_id,
            output_root=output_root,
            index=index,
            width=args.width,
            height=args.height,
            frames=args.frames,
            case=case,
        )
        brightness_mean, brightness_std, center_mean, highlight_fraction = image_metrics(frame_path)
        results.append(
            SweepResult(
                params=case,
                frame_path=str(frame_path),
                brightness_mean=brightness_mean,
                brightness_std=brightness_std,
                center_mean=center_mean,
                highlight_fraction=highlight_fraction,
                score=score_frame(
                    brightness_mean=brightness_mean,
                    brightness_std=brightness_std,
                    center_mean=center_mean,
                    highlight_fraction=highlight_fraction,
                ),
            )
        )

    results.sort(key=lambda item: item.score, reverse=True)
    top_results = results[: args.top_k]
    best_dir = output_root / "best"
    if best_dir.exists():
        shutil.rmtree(best_dir)
    best_dir.mkdir(parents=True, exist_ok=True)
    for rank, result in enumerate(top_results, start=1):
        source = Path(result.frame_path)
        destination = best_dir / f"{rank:02d}_{source.parent.name}.png"
        shutil.copy2(source, destination)

    manifest = {
        "runner": str(runner),
        "backend": args.backend,
        "source_dir": str(repo_root),
        "cases": [asdict(result) for result in results],
        "top_cases": [asdict(result) for result in top_results],
    }
    (output_root / "sweep_results.json").write_text(
        json.dumps(manifest, indent=2),
        encoding="utf-8",
    )
    write_contact_sheet(top_results, output_root / "best_contact_sheet.png")
    if top_results:
        best = top_results[0]
        print(
            "best:",
            f"score={best.score:.2f}",
            f"frame={best.frame_path}",
            f"d={best.params.distance:.1f}",
            f"p={best.params.pitch:.1f}",
            f"fov={best.params.fov:.1f}",
            f"exp={best.params.exposure:.3f}",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
