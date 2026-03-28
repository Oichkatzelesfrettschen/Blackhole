#!/usr/bin/env python3
"""Render a beauty still directly from the Blackhole bridge without Blender."""

from __future__ import annotations

import argparse
import ctypes as ct
import json
import os
from pathlib import Path

import numpy as np
from PIL import Image


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--width", type=int, default=1920)
    parser.add_argument("--height", type=int, default=1080)
    parser.add_argument("--spin", type=float, default=0.0)
    parser.add_argument("--observer-r", type=float, default=8.0)
    parser.add_argument("--inclination-deg", type=float, default=88.0)
    parser.add_argument("--fov-scale", type=float, default=0.7)
    parser.add_argument("--background-intensity", type=float, default=0.8)
    parser.add_argument("--background-yaw-deg", type=float, default=0.0)
    parser.add_argument("--background-pitch-deg", type=float, default=0.0)
    parser.add_argument("--background-filter-radius", type=float, default=0.006)
    parser.add_argument("--background-equirect-file", type=Path)
    parser.add_argument("--adisk-enabled", action="store_true")
    parser.add_argument("--adisk-lit", type=float, default=0.18)
    parser.add_argument("--frame-shift-x", type=float, default=0.0)
    parser.add_argument("--frame-shift-y", type=float, default=0.0)
    parser.add_argument("--exposure", type=float, default=24.0)
    parser.add_argument("--photon-glow", type=float, default=0.06)
    parser.add_argument("--max-steps", type=int, default=1000)
    parser.add_argument("--step-size", type=float, default=0.02)
    parser.add_argument("--max-dist", type=float, default=160.0)
    parser.add_argument("--oversample-factor", type=int, default=1)
    parser.add_argument("--camera-yaw-deg", type=float)
    parser.add_argument("--camera-pitch-deg", type=float)
    parser.add_argument("--camera-roll-deg", type=float, default=0.0)
    parser.add_argument("--camera-distance", type=float)
    return parser.parse_args()


def load_bridge_module(source_dir: Path):
    import importlib.util

    bridge_path = source_dir / "blender" / "addon" / "blackhole_physics" / "bridge.py"
    spec = importlib.util.spec_from_file_location("blackhole_bridge_module", bridge_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load bridge module from {bridge_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def camera_position_from_yaw_pitch(yaw_deg: float, pitch_deg: float, radius: float) -> tuple[float, float, float]:
    yaw_rad = np.deg2rad(yaw_deg)
    pitch_rad = np.deg2rad(pitch_deg)
    return (
        float(radius * np.cos(pitch_rad) * np.sin(yaw_rad)),
        float(radius * np.sin(pitch_rad)),
        float(radius * np.cos(pitch_rad) * np.cos(yaw_rad)),
    )


def _normalize3(vec: tuple[float, float, float]) -> tuple[float, float, float]:
    x, y, z = vec
    length = float(np.sqrt((x * x) + (y * y) + (z * z)))
    if length <= 1.0e-12:
        return (0.0, 0.0, 0.0)
    return (x / length, y / length, z / length)


def _cross3(a: tuple[float, float, float], b: tuple[float, float, float]) -> tuple[float, float, float]:
    ax, ay, az = a
    bx, by, bz = b
    return (
        ay * bz - az * by,
        az * bx - ax * bz,
        ax * by - ay * bx,
    )


def build_camera_basis(
    camera_pos: tuple[float, float, float],
    target: tuple[float, float, float] = (0.0, 0.0, 0.0),
    roll_deg: float = 0.0,
) -> tuple[float, ...]:
    forward = _normalize3(
        (
            target[0] - camera_pos[0],
            target[1] - camera_pos[1],
            target[2] - camera_pos[2],
        )
    )
    world_up = (0.0, 1.0, 0.0)
    dot = forward[0] * world_up[0] + forward[1] * world_up[1] + forward[2] * world_up[2]
    if abs(dot) > 0.99:
        world_up = (0.0, 0.0, 1.0)

    right = _normalize3(_cross3(forward, world_up))
    up = _normalize3(_cross3(right, forward))

    if abs(roll_deg) > 0.001:
        roll_rad = np.deg2rad(roll_deg)
        cos_roll = float(np.cos(roll_rad))
        sin_roll = float(np.sin(roll_rad))
        right = (
            right[0] * cos_roll + up[0] * sin_roll,
            right[1] * cos_roll + up[1] * sin_roll,
            right[2] * cos_roll + up[2] * sin_roll,
        )
        up = (
            -right[0] * sin_roll + up[0] * cos_roll,
            -right[1] * sin_roll + up[1] * cos_roll,
            -right[2] * sin_roll + up[2] * cos_roll,
        )

    return (
        right[0], right[1], right[2],
        up[0], up[1], up[2],
        forward[0], forward[1], forward[2],
    )


def desktop_view_camera(yaw_deg: float, pitch_deg: float, roll_deg: float, distance: float) -> tuple[tuple[float, float, float], tuple[float, ...]]:
    camera_pos = camera_position_from_yaw_pitch(yaw_deg, pitch_deg, distance)
    camera_basis = build_camera_basis(camera_pos, (0.0, 0.0, 0.0), roll_deg)
    return camera_pos, camera_basis


def main() -> int:
    args = parse_args()
    source_dir = args.source_dir.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
    oversample_factor = max(args.oversample_factor, 1)
    render_width = int(args.width) * oversample_factor
    render_height = int(args.height) * oversample_factor

    default_equirect = source_dir / "assets" / "backgrounds" / "equirect" / "eso_milkyway_brunier.jpg"

    os.environ["BLACKHOLE_SOURCE_DIR"] = str(source_dir)
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR"] = str(
        source_dir / "assets" / "skybox_nebula_dark"
    )
    if args.background_equirect_file is not None:
        os.environ["BLACKHOLE_BRIDGE_BACKGROUND_EQUIRECT_FILE"] = str(args.background_equirect_file.resolve())
    elif default_equirect.exists():
        os.environ["BLACKHOLE_BRIDGE_BACKGROUND_EQUIRECT_FILE"] = str(default_equirect)
    else:
        os.environ.pop("BLACKHOLE_BRIDGE_BACKGROUND_EQUIRECT_FILE", None)
    os.environ["BLACKHOLE_BRIDGE_ADISK_ENABLED"] = "1" if args.adisk_enabled else "0"
    os.environ["BLACKHOLE_BRIDGE_ADISK_LIT"] = str(args.adisk_lit)
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_ENABLED"] = "1"
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_INTENSITY"] = str(args.background_intensity)
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_YAW_DEG"] = str(args.background_yaw_deg)
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_PITCH_DEG"] = str(args.background_pitch_deg)
    os.environ["BLACKHOLE_BRIDGE_BACKGROUND_FILTER_RADIUS"] = str(args.background_filter_radius)
    os.environ["BLACKHOLE_BRIDGE_FRAME_SHIFT_X"] = str(args.frame_shift_x)
    os.environ["BLACKHOLE_BRIDGE_FRAME_SHIFT_Y"] = str(args.frame_shift_y)
    os.environ["BLACKHOLE_BRIDGE_EXPOSURE"] = str(args.exposure)
    os.environ["BLACKHOLE_BRIDGE_PHOTON_GLOW_STRENGTH"] = str(args.photon_glow)
    os.environ["BLACKHOLE_BRIDGE_MAX_STEPS"] = str(args.max_steps)
    os.environ["BLACKHOLE_BRIDGE_STEP_SIZE"] = str(args.step_size)
    os.environ["BLACKHOLE_BRIDGE_MAX_DIST"] = str(args.max_dist)
    os.environ["BLACKHOLE_BRIDGE_BLOOM_STRENGTH"] = "0.0"
    os.environ.setdefault(
        "BLACKHOLE_BRIDGE_LIB",
        str(source_dir / "build" / "Release" / "src" / "blender_bridge" / "libblackhole_bridge.so"),
    )

    bridge = load_bridge_module(source_dir)
    if not bridge.try_load_library():
        raise RuntimeError("Failed to load libblackhole_bridge.so")
    lib = bridge.get_lib()
    if hasattr(lib, "bhb_cuda_render_raytraced_view"):
        lib.bhb_cuda_render_raytraced_view.restype = ct.c_int
        lib.bhb_cuda_render_raytraced_view.argtypes = [
            ct.c_float,
            ct.POINTER(ct.c_float),
            ct.POINTER(ct.c_float),
            ct.c_float,
            ct.c_int,
            ct.c_int,
            ct.POINTER(ct.c_float),
        ]

    host = np.zeros((render_height, render_width, 4), dtype=np.float32)
    use_exact_camera = (
        hasattr(lib, "bhb_cuda_render_raytraced_view")
        and args.camera_yaw_deg is not None
        and args.camera_pitch_deg is not None
        and args.camera_distance is not None
    )
    if use_exact_camera:
        cam_pos, cam_basis = desktop_view_camera(
            float(args.camera_yaw_deg),
            float(args.camera_pitch_deg),
            float(args.camera_roll_deg),
            float(args.camera_distance),
        )
        cam_pos_arr = np.asarray(cam_pos, dtype=np.float32)
        cam_basis_arr = np.asarray(cam_basis, dtype=np.float32)
        result = lib.bhb_cuda_render_raytraced_view(
            float(args.spin),
            cam_pos_arr.ctypes.data_as(ct.POINTER(ct.c_float)),
            cam_basis_arr.ctypes.data_as(ct.POINTER(ct.c_float)),
            float(args.fov_scale),
            int(render_width),
            int(render_height),
            host.ctypes.data_as(ct.POINTER(ct.c_float)),
        )
    else:
        result = lib.bhb_cuda_render_raytraced_camera(
            float(args.spin),
            float(args.observer_r),
            float(np.deg2rad(args.inclination_deg)),
            float(args.fov_scale),
            int(render_width),
            int(render_height),
            host.ctypes.data_as(ct.POINTER(ct.c_float)),
        )
    if result != 0:
        raise RuntimeError(f"bhb_cuda_render_raytraced_camera failed with code {result}")

    rgb = np.nan_to_num(host[:, :, :3], nan=0.0, posinf=1.0, neginf=0.0)
    rgb = np.clip(rgb, 0.0, 1.0)
    image = Image.fromarray((rgb * 255.0).astype(np.uint8), mode="RGB")
    if oversample_factor > 1:
        image = image.resize((args.width, args.height), Image.Resampling.LANCZOS)
        rgb = np.asarray(image, dtype=np.float32) / 255.0
    image.save(args.output)

    report = {
        "source_dir": str(source_dir),
        "output": str(args.output),
        "width": args.width,
        "height": args.height,
        "render_width": render_width,
        "render_height": render_height,
        "spin": args.spin,
        "observer_r": args.observer_r,
        "inclination_deg": args.inclination_deg,
        "fov_scale": args.fov_scale,
        "use_exact_camera": use_exact_camera,
        "camera_yaw_deg": args.camera_yaw_deg,
        "camera_pitch_deg": args.camera_pitch_deg,
        "camera_roll_deg": args.camera_roll_deg,
        "camera_distance": args.camera_distance,
        "background_intensity": args.background_intensity,
        "background_yaw_deg": args.background_yaw_deg,
        "background_pitch_deg": args.background_pitch_deg,
        "background_filter_radius": args.background_filter_radius,
        "background_equirect_file": str(args.background_equirect_file.resolve()) if args.background_equirect_file else None,
        "adisk_enabled": args.adisk_enabled,
        "adisk_lit": args.adisk_lit,
        "frame_shift_x": args.frame_shift_x,
        "frame_shift_y": args.frame_shift_y,
        "exposure": args.exposure,
        "photon_glow": args.photon_glow,
        "max_steps": args.max_steps,
        "step_size": args.step_size,
        "max_dist": args.max_dist,
        "oversample_factor": oversample_factor,
        "mean_rgb": [float(rgb[:, :, channel].mean()) for channel in range(3)],
        "max_rgb": [float(rgb[:, :, channel].max()) for channel in range(3)],
    }
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    else:
        print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
