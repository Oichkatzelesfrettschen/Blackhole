#!/usr/bin/env python3
"""Run a headless BlenderMCP-compatible command loop on a dedicated port."""

from __future__ import annotations

import addon_utils
import json
import os
from pathlib import Path
import socket
import traceback

import bpy


def resolve_target_engine(mode: str, fallback: str) -> str:
    engines = [cls.bl_idname for cls in bpy.types.RenderEngine.__subclasses__() if getattr(cls, "bl_idname", None)]
    lowered = {engine.lower(): engine for engine in engines}
    if mode == "blackhole":
        if "BLACKHOLE_RT" in engines:
            return "BLACKHOLE_RT"
    elif mode == "cycles":
        if "cycles" in lowered:
            return lowered["cycles"]
    elif mode == "octane":
        for engine in engines:
            if "octane" in engine.lower():
                return engine
    return fallback


def find_module_name(expected_name: str, expected_path_suffix: str | None = None) -> str | None:
    for module in addon_utils.modules():
        bl_info = getattr(module, "bl_info", {})
        module_name = getattr(module, "__name__", "")
        module_file = str(Path(getattr(module, "__file__", "")))
        if bl_info.get("name") == expected_name:
            return module_name
        if expected_path_suffix and module_file.endswith(expected_path_suffix):
            return module_name
    return None


def enable_addon(module_name: str) -> None:
    addon_utils.enable(module_name, default_set=False, persistent=False)


def load_handlers():
    blackhole_zip = os.environ.get("BLACKHOLE_ADDON_ZIP", "")
    blender_mcp_addon = os.environ.get("BLENDER_MCP_ADDON_PY", "/usr/share/blender-mcp/addon.py")
    status_json = os.environ.get("BLENDER_MCP_STATUS_JSON", "")
    target_engine = os.environ.get("BLENDER_MCP_TARGET_ENGINE", "BLACKHOLE_RT")
    engine_mode = os.environ.get("BLENDER_MCP_ENGINE_MODE", "")

    if blackhole_zip:
        bpy.ops.preferences.addon_install(filepath=blackhole_zip, overwrite=True)
    if blender_mcp_addon:
        bpy.ops.preferences.addon_install(filepath=blender_mcp_addon, overwrite=True)

    blackhole_module = find_module_name("Blackhole Physics", "blackhole_physics/__init__.py") or "blackhole_physics"
    blender_mcp_module = find_module_name("Blender MCP", "addon.py")
    if blender_mcp_module is None:
        raise RuntimeError("Unable to resolve installed Blender MCP addon module name")

    enable_addon(blackhole_module)
    enable_addon(blender_mcp_module)

    from blackhole_physics import quality
    import addon as blender_mcp_addon_module

    scene = bpy.context.scene
    resolved_engine = resolve_target_engine(engine_mode, target_engine)
    quality_report = quality.apply_studio_quality(scene, target_engine=resolved_engine)
    port = int(os.environ.get("BLENDER_MCP_PORT", "9876"))
    scene.blendermcp_port = port
    server = blender_mcp_addon_module.BlenderMCPServer(host="127.0.0.1", port=port)

    status = {
        "blackhole_module": blackhole_module,
        "blender_mcp_module": blender_mcp_module,
        "engine": resolved_engine,
        "engine_mode": engine_mode,
        "port": port,
        "server_running": True,
        "studio_quality": quality_report,
    }
    if status_json:
        Path(status_json).write_text(json.dumps(status, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return port, server


def read_command(client: socket.socket) -> dict:
    chunks: list[bytes] = []
    while True:
        data = client.recv(8192)
        if not data:
            break
        chunks.append(data)
    if not chunks:
        raise RuntimeError("Client disconnected before sending a command")
    return json.loads(b"".join(chunks).decode("utf-8"))


def main() -> int:
    port, server = load_handlers()
    host = "127.0.0.1"
    shutdown_requested = False

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.bind((host, port))
        sock.listen(4)
        sock.settimeout(0.5)
        print(f"[blender-mcp-headless] Listening on {host}:{port}", flush=True)

        while not shutdown_requested:
            try:
                client, _addr = sock.accept()
            except socket.timeout:
                continue

            with client:
                try:
                    command = read_command(client)
                    if command.get("type") == "shutdown":
                        response = {"status": "success", "result": {"shutdown": True}}
                        shutdown_requested = True
                    else:
                        response = server.execute_command(command)
                except Exception as exc:
                    traceback.print_exc()
                    response = {"status": "error", "message": str(exc)}
                client.sendall(json.dumps(response).encode("utf-8"))

    print("[blender-mcp-headless] Shutdown complete", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
