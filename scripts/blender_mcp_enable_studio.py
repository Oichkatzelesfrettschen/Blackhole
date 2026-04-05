#!/usr/bin/env python3
"""Enable BlenderMCP and Blackhole addons, then apply the studio-quality profile."""

from __future__ import annotations

import addon_utils
import json
import os
from pathlib import Path

import bpy


def resolve_target_engine(scene: bpy.types.Scene, mode: str, fallback: str) -> str:
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
    if fallback:
        return fallback
    return scene.render.engine


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
    addon_utils.enable(module_name, default_set=True, persistent=True)


def main() -> int:
    blackhole_zip = os.environ.get("BLACKHOLE_ADDON_ZIP", "")
    blender_mcp_addon = os.environ.get("BLENDER_MCP_ADDON_PY", "/usr/share/blender-mcp/addon.py")
    save_userpref = os.environ.get("BLENDER_MCP_SAVE_USERPREF", "0") == "1"
    status_json = os.environ.get("BLENDER_MCP_STATUS_JSON", "")
    target_engine = os.environ.get("BLENDER_MCP_TARGET_ENGINE", "BLACKHOLE_RT")
    engine_mode = os.environ.get("BLENDER_MCP_ENGINE_MODE", "")

    if blackhole_zip:
        bpy.ops.preferences.addon_install(filepath=blackhole_zip, overwrite=True)
    if blender_mcp_addon:
        bpy.ops.preferences.addon_install(filepath=blender_mcp_addon, overwrite=True)

    blackhole_module = find_module_name("Blackhole Physics", "blackhole_physics/__init__.py") or "blackhole_physics"
    blender_mcp_module = find_module_name("Blender MCP", "addon.py")

    enable_addon(blackhole_module)
    if blender_mcp_module is None:
        raise RuntimeError("Unable to resolve installed Blender MCP addon module name")
    enable_addon(blender_mcp_module)

    from blackhole_physics import quality

    scene = bpy.context.scene
    resolved_engine = resolve_target_engine(scene, engine_mode, target_engine)
    quality_report = quality.apply_studio_quality(scene, target_engine=resolved_engine)
    scene.blendermcp_port = int(os.environ.get("BLENDER_MCP_PORT", "9876"))
    bpy.ops.blendermcp.start_server()
    if save_userpref:
        bpy.ops.wm.save_userpref()

    status = {
        "blackhole_module": blackhole_module,
        "blender_mcp_module": blender_mcp_module,
        "engine": resolved_engine,
        "engine_mode": engine_mode,
        "port": int(scene.blendermcp_port),
        "save_userpref": save_userpref,
        "server_running": bool(getattr(scene, "blendermcp_server_running", False)),
        "studio_quality": quality_report,
    }
    if status_json:
        Path(status_json).write_text(json.dumps(status, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "[blender-mcp-bootstrap] "
        f"Studio quality applied and BlenderMCP server started on port {scene.blendermcp_port}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
