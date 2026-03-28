#!/usr/bin/env python3
"""Run BlackholeGLSL under Xvfb with quiet logs and optional tmux detachment."""

from __future__ import annotations

import argparse
import os
import shutil
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-dir",
        type=Path,
        default=Path("/home/eirikr/Github/Blackhole"),
    )
    parser.add_argument(
        "--binary",
        type=Path,
        default=Path("/home/eirikr/Github/Blackhole/build/Release/BlackholeGLSL"),
    )
    parser.add_argument("--display", type=int, default=99)
    parser.add_argument(
        "--backend",
        choices=("hidden", "xvfb"),
        default="hidden",
    )
    parser.add_argument("--width", type=int, default=1920)
    parser.add_argument("--height", type=int, default=1080)
    parser.add_argument("--screen-depth", type=int, default=24)
    parser.add_argument("--record-dir", type=Path, required=True)
    parser.add_argument("--record-frames", type=int, default=1)
    parser.add_argument(
        "--record-profile",
        default="showcase-orbit",
        choices=("showcase-orbit", "compare-orbit-near", "cinematic"),
    )
    parser.add_argument("--record-yaw", type=float)
    parser.add_argument("--record-pitch", type=float)
    parser.add_argument("--record-distance", type=float)
    parser.add_argument("--record-fov", type=float)
    parser.add_argument("--record-exposure", type=float)
    parser.add_argument("--record-sweep-deg", type=float, default=0.0)
    parser.add_argument("--start-frame", type=int)
    parser.add_argument("--log-path", type=Path)
    parser.add_argument("--detach-tmux", action="store_true")
    parser.add_argument("--tmux-session", default="blackhole-glsl-headless")
    return parser.parse_args()


def build_command(args: argparse.Namespace) -> list[str]:
    command = [
        str(args.binary.resolve()),
        "--record-frames",
        str(args.record_dir.resolve()),
        str(args.record_frames),
        "--record-profile",
        args.record_profile,
    ]
    optional_pairs = [
        ("--record-yaw", args.record_yaw),
        ("--record-pitch", args.record_pitch),
        ("--record-distance", args.record_distance),
        ("--record-fov", args.record_fov),
        ("--record-exposure", args.record_exposure),
        ("--record-sweep-deg", args.record_sweep_deg),
        ("--start-frame", args.start_frame),
    ]
    for flag, value in optional_pairs:
        if value is not None:
            command.extend([flag, str(value)])
    return command


def wait_for_xvfb(display: int, timeout: float = 5.0) -> None:
    end = time.time() + timeout
    while time.time() < end:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
            try:
                sock.connect(f"/tmp/.X11-unix/X{display}")
                return
            except OSError:
                time.sleep(0.1)
    raise RuntimeError(f"Xvfb on :{display} did not become ready")


def run_hidden(args: argparse.Namespace) -> int:
    repo_root = args.source_dir.resolve()
    args.record_dir.mkdir(parents=True, exist_ok=True)
    log_path = args.log_path or (args.record_dir / "headless_run.log")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["BLACKHOLE_RECORD_WIDTH"] = str(args.width)
    env["BLACKHOLE_RECORD_HEIGHT"] = str(args.height)
    env["BLACKHOLE_WINDOW_HIDDEN"] = "1"
    command = build_command(args)
    with log_path.open("w", encoding="utf-8") as log_file:
        subprocess.run(
            command,
            check=True,
            cwd=repo_root,
            env=env,
            stdout=log_file,
            stderr=subprocess.STDOUT,
        )
    print(f"hidden-window record complete: {args.record_dir}")
    print(f"log: {log_path}")
    return 0


def run_xvfb(args: argparse.Namespace) -> int:
    if shutil.which("Xvfb") is None:
        raise RuntimeError("Xvfb is required but was not found in PATH")

    xvfb_command = [
        "Xvfb",
        f":{args.display}",
        "-screen",
        "0",
        f"{args.width}x{args.height}x{args.screen_depth}",
        "+extension",
        "GLX",
        "+render",
        "-noreset",
        "-nolisten",
        "tcp",
    ]
    with log_path.open("w", encoding="utf-8") as log_file:
        xvfb = subprocess.Popen(
            xvfb_command,
            stdout=log_file,
            stderr=subprocess.STDOUT,
            cwd=repo_root,
        )
        try:
            wait_for_xvfb(args.display)
            env = dict(os.environ)
            env["DISPLAY"] = f":{args.display}"
            env["BLACKHOLE_RECORD_WIDTH"] = str(args.width)
            env["BLACKHOLE_RECORD_HEIGHT"] = str(args.height)
            env["BLACKHOLE_WINDOW_HIDDEN"] = "1"
            env.setdefault("LIBGL_ALWAYS_SOFTWARE", "1")
            env.setdefault("MESA_LOADER_DRIVER_OVERRIDE", "llvmpipe")
            env.setdefault("__GLX_VENDOR_LIBRARY_NAME", "mesa")
            command = build_command(args)
            subprocess.run(
                command,
                check=True,
                cwd=repo_root,
                env=env,
                stdout=log_file,
                stderr=subprocess.STDOUT,
            )
        finally:
            xvfb.terminate()
            try:
                xvfb.wait(timeout=5)
            except subprocess.TimeoutExpired:
                xvfb.kill()
                xvfb.wait(timeout=5)
    print(f"xvfb record complete: {args.record_dir}")
    print(f"log: {log_path}")
    return 0


def run_detached_tmux(args: argparse.Namespace) -> int:
    if shutil.which("tmux") is None:
        raise RuntimeError("tmux is required for --detach-tmux")
    session = args.tmux_session
    script_path = Path(__file__).resolve()
    command = [
        "tmux",
        "new-session",
        "-d",
        "-s",
        session,
        sys.executable,
        str(script_path),
        "--source-dir",
        str(args.source_dir.resolve()),
        "--binary",
        str(args.binary.resolve()),
        "--display",
        str(args.display),
        "--backend",
        args.backend,
        "--width",
        str(args.width),
        "--height",
        str(args.height),
        "--screen-depth",
        str(args.screen_depth),
        "--record-dir",
        str(args.record_dir.resolve()),
        "--record-frames",
        str(args.record_frames),
        "--record-profile",
        args.record_profile,
    ]
    optional_pairs = [
        ("--record-yaw", args.record_yaw),
        ("--record-pitch", args.record_pitch),
        ("--record-distance", args.record_distance),
        ("--record-fov", args.record_fov),
        ("--record-exposure", args.record_exposure),
        ("--record-sweep-deg", args.record_sweep_deg),
        ("--start-frame", args.start_frame),
        ("--log-path", args.log_path),
    ]
    for flag, value in optional_pairs:
        if value is not None:
            command.extend([flag, str(value)])
    subprocess.run(command, check=True)
    print(f"tmux session started: {session}")
    print(f"attach with: tmux attach -t {session}")
    return 0


def main() -> int:
    args = parse_args()
    if args.detach_tmux:
        return run_detached_tmux(args)
    if args.backend == "xvfb":
        return run_xvfb(args)
    return run_hidden(args)


if __name__ == "__main__":
    raise SystemExit(main())
