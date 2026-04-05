#!/usr/bin/env python3
"""Build a reproducible studio scene through an isolated BlenderMCP session."""

from __future__ import annotations

import argparse
import json
import pathlib
import socket
import subprocess
import sys
import time


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", default="blender")
    parser.add_argument("--source-dir", required=True, type=pathlib.Path)
    parser.add_argument("--addon-zip", required=True, type=pathlib.Path)
    parser.add_argument("--bridge-lib", required=True, type=pathlib.Path)
    parser.add_argument("--blend-out", required=True, type=pathlib.Path)
    parser.add_argument("--session-root", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=19876)
    parser.add_argument("--port-range", type=int, default=32)
    parser.add_argument("--width", type=int, default=640)
    parser.add_argument("--height", type=int, default=360)
    parser.add_argument("--engine-mode", choices=("blackhole", "octane", "cycles"), default="blackhole")
    parser.add_argument("--keep-alive", action="store_true")
    parser.add_argument("--startup-timeout", type=float, default=120.0)
    parser.add_argument("--probe-timeout", type=float, default=20.0)
    return parser.parse_args(argv)


def send_command(host: str, port: int, payload: dict, timeout: float) -> dict:
    deadline = time.monotonic() + max(timeout, 0.1)
    last_error = ""
    encoded = json.dumps(payload).encode("utf-8")
    while True:
        try:
            with socket.create_connection((host, port), timeout=2.0) as sock:
                sock.sendall(encoded)
                sock.shutdown(socket.SHUT_WR)
                chunks: list[bytes] = []
                while True:
                    data = sock.recv(8192)
                    if not data:
                        break
                    chunks.append(data)
            return json.loads(b"".join(chunks).decode("utf-8"))
        except Exception as exc:
            last_error = str(exc)
            if time.monotonic() >= deadline:
                raise SystemExit(f"Timed out sending command to BlenderMCP on {host}:{port}: {last_error}") from exc
            time.sleep(0.5)


def build_scene_code(blend_out: pathlib.Path, width: int, height: int, engine_mode: str) -> str:
    blend_posix = blend_out.as_posix()
    lines = [
        "import bpy",
        "def _resolve_engine(mode):",
        "    engines = [cls.bl_idname for cls in bpy.types.RenderEngine.__subclasses__() if getattr(cls, 'bl_idname', None)]",
        "    lowered = {engine.lower(): engine for engine in engines}",
        "    if mode == 'blackhole':",
        "        if 'BLACKHOLE_RT' in engines:",
        "            return 'BLACKHOLE_RT'",
        "        raise RuntimeError('BLACKHOLE_RT engine unavailable in this Blender session')",
        "    if mode == 'cycles':",
        "        if 'cycles' in lowered:",
        "            return lowered['cycles']",
        "        raise RuntimeError('Cycles engine unavailable in this Blender session')",
        "    if mode == 'octane':",
        "        for engine in engines:",
        "            if 'octane' in engine.lower():",
        "                return engine",
        "        raise RuntimeError('Octane engine unavailable in this Blender session')",
        "    raise RuntimeError(f'Unknown engine mode: {mode}')",
        "scene = bpy.context.scene",
        "props = scene.blackhole",
        f"props.texture_width = {int(width)}",
        f"props.texture_height = {int(height)}",
        f"scene.render.resolution_x = {int(width)}",
        f"scene.render.resolution_y = {int(height)}",
        "scene.render.resolution_percentage = 100",
        "scene.render.film_transparent = True",
        "bpy.ops.blackhole.preset_m87()",
        "bpy.ops.blackhole.apply_studio_quality()",
        "cube = bpy.data.objects.get('Cube')",
        "if cube is not None:",
        "    bpy.data.objects.remove(cube, do_unlink=True)",
        "light = bpy.data.objects.get('Light')",
        "if light is not None:",
        "    bpy.data.objects.remove(light, do_unlink=True)",
        "bpy.ops.blackhole.generate_horizon()",
        "bpy.ops.blackhole.generate_disk()",
        "bpy.ops.blackhole.render_disk_texture()",
        "bpy.ops.blackhole.render_lensing_map()",
        f"engine_mode = {engine_mode!r}",
        "desired_engine = _resolve_engine(engine_mode)",
        "if engine_mode == 'octane':",
        "    bpy.ops.blackhole.setup_octane_materials()",
        "save_engine = 'CYCLES' if engine_mode == 'blackhole' else desired_engine",
        "scene.render.engine = save_engine",
        f"bpy.ops.wm.save_as_mainfile(filepath={blend_posix!r}, copy=False)",
        "print('engine_mode', engine_mode)",
        "print('desired_engine', desired_engine)",
        "print('save_engine', save_engine)",
        "print('saved_blend', bpy.data.filepath)",
        "print('scene_objects', [obj.name for obj in bpy.context.scene.objects])",
    ]
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    source_dir = args.source_dir.resolve()
    addon_zip = args.addon_zip.resolve()
    bridge_lib = args.bridge_lib.resolve()
    blend_out = args.blend_out.resolve()
    json_out = args.json_out.resolve() if args.json_out else None
    log_out = args.log_out.resolve() if args.log_out else None
    launcher = source_dir / "scripts" / "run_blender_mcp_isolated_session.py"

    if not launcher.exists():
        raise SystemExit(f"Isolated BlenderMCP launcher not found: {launcher}")

    launch_command = [
        sys.executable,
        str(launcher),
        "--blender-executable",
        args.blender_executable,
        "--source-dir",
        str(source_dir),
        "--addon-zip",
        str(addon_zip),
        "--bridge-lib",
        str(bridge_lib),
        "--port",
        str(args.port),
        "--port-range",
        str(args.port_range),
        "--engine-mode",
        args.engine_mode,
        "--startup-timeout",
        str(args.startup_timeout),
        "--probe-timeout",
        str(args.probe_timeout),
    ]
    if args.session_root is not None:
        launch_command.extend(["--session-root", str(args.session_root.resolve())])
    launch = subprocess.run(
        launch_command,
        check=False,
        capture_output=True,
        text=True,
        cwd=source_dir,
    )
    if launch.returncode != 0:
        raise SystemExit(launch.stderr or launch.stdout or f"Failed to launch isolated BlenderMCP session ({launch.returncode})")

    launch_report = json.loads(launch.stdout)
    host = launch_report["host"]
    port = int(launch_report["port"])
    initial_scene = send_command(host, port, {"type": "get_scene_info", "params": {}}, args.probe_timeout)

    blend_out.parent.mkdir(parents=True, exist_ok=True)
    setup_timeout = max(args.probe_timeout, 30.0)
    if args.engine_mode == "octane":
        setup_timeout = max(setup_timeout, 120.0)

    setup_response = send_command(
        host,
        port,
        {
            "type": "execute_code",
            "params": {
                "code": build_scene_code(blend_out, args.width, args.height, args.engine_mode),
            },
        },
        setup_timeout,
    )
    final_scene = send_command(host, port, {"type": "get_scene_info", "params": {}}, args.probe_timeout)

    shutdown_response = None
    if not args.keep_alive:
        shutdown_response = send_command(host, port, {"type": "shutdown", "params": {}}, args.probe_timeout)

    report = {
        "engine_mode": args.engine_mode,
        "status": "success",
        "launch_report": launch_report,
        "initial_scene_info": initial_scene,
        "setup_response": setup_response,
        "final_scene_info": final_scene,
        "blend_out": str(blend_out),
        "blend_exists": blend_out.exists(),
        "host": host,
        "port": port,
        "shutdown_response": shutdown_response,
    }
    if log_out is not None:
        log_out.parent.mkdir(parents=True, exist_ok=True)
        combined = launch.stdout
        session_log = pathlib.Path(launch_report["log_path"])
        if session_log.exists():
            combined += "\n[isolated-session-log]\n" + session_log.read_text(encoding="utf-8")
        log_out.write_text(combined, encoding="utf-8")
    if json_out is not None:
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
