#!/usr/bin/env python3
"""Launch an isolated Blender plus BlenderMCP session on a nondefault port."""

from __future__ import annotations

import argparse
import json
import datetime as dt
import os
import pathlib
import shutil
import signal
import socket
import subprocess
import sys
import time


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", default="blender")
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--addon-zip", required=True)
    parser.add_argument("--bridge-lib", required=True)
    parser.add_argument("--session-root", type=pathlib.Path)
    parser.add_argument("--port", type=int, default=19876)
    parser.add_argument("--port-range", type=int, default=64)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--startup-timeout", type=float, default=45.0)
    parser.add_argument("--probe-timeout", type=float, default=10.0)
    parser.add_argument("--engine", default="BLACKHOLE_RT")
    parser.add_argument("--engine-mode", choices=("blackhole", "octane", "cycles"))
    parser.add_argument("--mode", choices=("headless", "gui"), default="headless")
    return parser.parse_args(argv)


def is_port_free(host: str, port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.bind((host, port))
        except OSError:
            return False
    return True


def choose_port(host: str, start_port: int, port_range: int) -> int:
    for port in range(start_port, start_port + max(port_range, 1)):
        if is_port_free(host, port):
            return port
    raise SystemExit(
        f"No free TCP port found in range {start_port}-{start_port + max(port_range, 1) - 1}"
    )


def wait_for_file(path: pathlib.Path, timeout: float, proc: subprocess.Popen[str] | None = None) -> bool:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if path.exists():
            return True
        if proc is not None and proc.poll() is not None:
            return path.exists()
        time.sleep(0.25)
    return path.exists()


def probe_scene(host: str, port: int, timeout: float) -> dict:
    deadline = time.monotonic() + timeout
    last_error = ""
    payload = json.dumps({"type": "get_scene_info", "params": {}}).encode("utf-8")
    while time.monotonic() < deadline:
        try:
            with socket.create_connection((host, port), timeout=2.0) as sock:
                sock.sendall(payload)
                sock.shutdown(socket.SHUT_WR)
                chunks: list[bytes] = []
                while True:
                    data = sock.recv(8192)
                    if not data:
                        break
                    chunks.append(data)
            response = json.loads(b"".join(chunks).decode("utf-8"))
            if response.get("status") == "success":
                return response
            last_error = response.get("message", "unknown blender-mcp error")
        except Exception as exc:  # pragma: no cover - best effort launcher
            last_error = str(exc)
        time.sleep(0.5)
    raise SystemExit(f"Timed out probing isolated BlenderMCP session on {host}:{port}: {last_error}")


def terminate_process(proc: subprocess.Popen[str]) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    except PermissionError:
        proc.terminate()


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    source_dir = pathlib.Path(args.source_dir).resolve()
    addon_zip = pathlib.Path(args.addon_zip).resolve()
    bridge_lib = pathlib.Path(args.bridge_lib).resolve()
    bootstrap_script = (
        source_dir / "scripts" / "blender_mcp_headless_session.py"
        if args.mode == "headless"
        else source_dir / "scripts" / "blender_mcp_enable_studio.py"
    )
    blender_path = shutil.which(args.blender_executable) or args.blender_executable

    if not source_dir.exists():
        raise SystemExit(f"Source directory not found: {source_dir}")
    if not addon_zip.exists():
        raise SystemExit(f"Addon zip not found: {addon_zip}")
    if not bridge_lib.exists():
        raise SystemExit(f"Bridge library not found: {bridge_lib}")
    if not bootstrap_script.exists():
        raise SystemExit(f"Bootstrap script not found: {bootstrap_script}")

    session_root = (
        args.session_root.resolve()
        if args.session_root is not None
        else pathlib.Path("/tmp") / f"blackhole_blender_mcp_session_{dt.datetime.now().strftime('%Y%m%d_%H%M%S')}"
    )
    session_root.mkdir(parents=True, exist_ok=True)
    user_config = session_root / "config"
    user_scripts = session_root / "scripts"
    user_scripts.mkdir(parents=True, exist_ok=True)
    user_config.mkdir(parents=True, exist_ok=True)
    status_json = session_root / "bootstrap_status.json"
    launch_log = session_root / "blender_stdout.log"
    port = choose_port(args.host, args.port, args.port_range)
    if status_json.exists():
        status_json.unlink()
    if launch_log.exists():
        launch_log.unlink()

    env = os.environ.copy()
    env["BLENDER_USER_CONFIG"] = str(user_config)
    env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
    env["BLACKHOLE_BRIDGE_LIB"] = str(bridge_lib)
    env["BLACKHOLE_ADDON_ZIP"] = str(addon_zip)
    env["BLENDER_MCP_ADDON_PY"] = "/usr/share/blender-mcp/addon.py"
    env["BLENDER_MCP_PORT"] = str(port)
    env["BLENDER_MCP_STATUS_JSON"] = str(status_json)
    env["BLENDER_MCP_SAVE_USERPREF"] = "0"
    env["BLENDER_MCP_TARGET_ENGINE"] = args.engine
    if args.engine_mode:
        env["BLENDER_MCP_ENGINE_MODE"] = args.engine_mode
    env.pop("OCIO", None)

    command = [
        blender_path,
        "--factory-startup",
        "--python-exit-code",
        "1",
        "--python",
        str(bootstrap_script),
    ]
    if args.mode == "headless":
        command.insert(1, "--background")

    launch_log.parent.mkdir(parents=True, exist_ok=True)
    with launch_log.open("w", encoding="utf-8") as handle:
        proc = subprocess.Popen(
            command,
            env=env,
            stdout=handle,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )

    try:
        if not wait_for_file(status_json, args.startup_timeout, proc):
            if proc.poll() is not None:
                launch_text = launch_log.read_text(encoding="utf-8", errors="replace") if launch_log.exists() else ""
                raise SystemExit(
                    f"Blender process exited before bootstrap status was written; see {launch_log}\n{launch_text}"
                )
            raise SystemExit(
                f"Timed out waiting for Blender bootstrap status at {status_json}; see {launch_log}"
            )
        probe = probe_scene(args.host, port, args.probe_timeout)
    except BaseException:
        terminate_process(proc)
        raise

    status = json.loads(status_json.read_text(encoding="utf-8"))
    report = {
        "blender_executable": blender_path,
        "bridge_lib": str(bridge_lib),
        "host": args.host,
        "pid": proc.pid,
        "port": port,
        "session_root": str(session_root),
        "status_json": str(status_json),
        "log_path": str(launch_log),
        "command": command,
        "engine_mode": args.engine_mode or "",
        "bootstrap_status": status,
        "probe": probe,
    }

    if args.log_out is not None:
        args.log_out.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.log_out.resolve().write_text(launch_log.read_text(encoding="utf-8"), encoding="utf-8")
    if args.json_out is not None:
        args.json_out.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.json_out.resolve().write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
