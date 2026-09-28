"""Verify capture identities and summarize paired raw/display luminance."""

from __future__ import annotations

import json
import pathlib
import sys

import numpy as np
from PIL import Image


def luminance(image: np.ndarray) -> np.ndarray:
    return (0.2126 * image[..., 0]) + (0.7152 * image[..., 1]) + (0.0722 * image[..., 2])


def read_pfm(path: pathlib.Path) -> np.ndarray:
    with path.open("rb") as source:
        if source.readline().strip() != b"PF":
            raise ValueError(f"{path} is not an RGB PFM")
        width, height = map(int, source.readline().split())
        scale = float(source.readline())
        dtype = "<f4" if scale < 0 else ">f4"
        pixels = np.frombuffer(source.read(), dtype=dtype)
    if pixels.size != width * height * 3:
        raise ValueError(f"{path} has the wrong pixel count")
    return pixels.reshape((height, width, 3))


def require_close(actual: float, expected: float, field: str) -> None:
    if abs(actual - expected) > 1.0e-5:
        raise ValueError(f"{field}: expected {expected}, found {actual}")


def checked_tile(output: pathlib.Path, name: str) -> tuple[dict, str]:
    png = output / f"{name}.png"
    pfm = output / f"{name}.pfm"
    display_metadata = json.loads((output / f"{name}.png.json").read_text())
    raw_metadata = json.loads((output / f"{name}.pfm.json").read_text())
    if display_metadata != raw_metadata:
        raise ValueError(f"{name}: raw and display sidecars differ")
    display = np.asarray(Image.open(png).convert("RGB"), dtype=np.float64) / 255.0
    raw = read_pfm(pfm)
    if display.shape != raw.shape:
        raise ValueError(f"{name}: raw and display dimensions differ")
    if (display.shape[1], display.shape[0]) != (
        display_metadata["width"],
        display_metadata["height"],
    ):
        raise ValueError(f"{name}: sidecar dimensions differ from pixels")
    raw_values = luminance(raw)
    display_values = luminance(display)
    if not np.isfinite(raw_values).all():
        raise ValueError(f"{name}: raw luminance contains non-finite values")
    values = (
        float(np.mean(raw_values)),
        float(np.percentile(raw_values, 99)),
        float(np.mean(display_values)),
        float(np.percentile(display_values, 99)),
    )
    metrics = " | ".join(f"{value:.6g}" for value in values)
    return display_metadata, metrics


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in {"display", "observer"}:
        raise SystemExit("Usage: capture_comparison_index.py display|observer OUT")
    mode = sys.argv[1]
    output = pathlib.Path(sys.argv[2])
    if mode == "display":
        tiles = (
            ("bloom_off", "bloom", "off", 1.0, 0.0, True),
            ("bloom_on", "bloom", "on", 1.0, 0.1, True),
            ("exposure_0p5", "exposure", "0.5", 0.5, 0.0, True),
            ("exposure_1", "exposure", "1", 1.0, 0.0, True),
            ("exposure_2", "exposure", "2", 2.0, 0.0, True),
            ("tone_mapping_off", "tone mapping", "off", 1.0, 0.0, False),
            ("tone_mapping_on", "tone mapping", "on", 1.0, 0.0, True),
        )
    else:
        tiles = (
            ("resolution_640x480", "resolution", "640 x 480", None, None, None),
            ("resolution_1280x960", "resolution", "1280 x 960", None, None, None),
        )
    rows = []
    baseline = None
    for name, variable, value, exposure, bloom, tone in tiles:
        metadata, metrics = checked_tile(output, name)
        if metadata["scene_mode"] != ("blackhole" if mode == "display" else "observer-sky"):
            raise ValueError(f"{name}: wrong scene mode")
        if mode == "display":
            require_close(metadata["exposure"], exposure, "exposure")
            require_close(metadata["bloom_strength"], bloom, "bloom strength")
            if metadata["tone_mapping_enabled"] is not tone:
                raise ValueError(f"{name}: tone mapping override failed")
            fixed = tuple(
                metadata[field]
                for field in (
                    "source_revision",
                    "scene_mode",
                    "camera_distance",
                    "camera_yaw_degrees",
                    "camera_pitch_degrees",
                    "camera_fov_degrees",
                    "tracer_spin",
                    "disk_transfer_mode",
                    "width",
                    "height",
                )
            )
        else:
            require_close(metadata["observer_fov_degrees"], 0.1, "observer FOV")
            expected_size = (640, 480) if "640x480" in name else (1280, 960)
            if (metadata["width"], metadata["height"]) != expected_size:
                raise ValueError(f"{name}: resolution override failed")
            fixed = tuple(
                metadata[field]
                for field in (
                    "source_revision",
                    "scene_mode",
                    "observer_spin_deficit",
                    "observer_radius_offset",
                    "observer_fov_degrees",
                    "observer_look_longitude_degrees",
                    "observer_look_latitude_degrees",
                )
            )
        if baseline is not None and fixed != baseline:
            raise ValueError(f"{name}: fixed capture identity changed")
        baseline = fixed
        rows.append(f"| [{name}.png]({name}.png) | {variable} | {value} | {metrics} |")
    title = "Display transform comparison" if mode == "display" else "Observer sampling comparison"
    lines = [
        f"# {title}",
        "",
        "Raw luminance is linear RGB from the pre-postprocess PFM. Display luminance",
        "uses the normalized PNG code values. P99 uses NumPy linear interpolation.",
        "",
        "| Tile | Controlled variable | Value | Raw mean | Raw P99 | Display mean | Display P99 |",
        "| --- | --- | --- | ---: | ---: | ---: | ---: |",
        *rows,
        "",
    ]
    if mode == "observer":
        lines.extend(
            (
                "Frozen export time disables motion blur; the observer shader uses one sample",
                "per pixel. The renderer exposes no independent sample-count control.",
                "",
            )
        )
    (output / "index.md").write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
