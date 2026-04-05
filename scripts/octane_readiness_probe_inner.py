#!/usr/bin/env python3
"""Run inside OctaneBlender to classify Octane render readiness."""

from __future__ import annotations

import json
import os
import traceback

import addon_utils
import bpy
import numpy as np


def find_octane_engine() -> str | None:
    for cls in bpy.types.RenderEngine.__subclasses__():
        bl_idname = getattr(cls, "bl_idname", None)
        if bl_idname and "octane" in bl_idname.lower():
            return bl_idname
    return None


def compute_quality_metrics(image_path: str) -> dict[str, float]:
    image = bpy.data.images.load(image_path, check_existing=False)
    try:
        width, height = image.size
        pixels = np.array(image.pixels[:], dtype=np.float32).reshape(height, width, 4)
        rgb = pixels[..., :3]
        alpha = pixels[..., 3]
        luma = 0.2126 * rgb[..., 0] + 0.7152 * rgb[..., 1] + 0.0722 * rgb[..., 2]
        nonzero_rgb = np.any(rgb > 1.0e-6, axis=-1)
        return {
            "mean_luma": float(np.mean(luma)),
            "max_luma": float(np.max(luma)),
            "nonzero_rgb_fraction": float(np.mean(nonzero_rgb)),
            "alpha_mean": float(np.mean(alpha)),
        }
    finally:
        bpy.data.images.remove(image)


def main() -> int:
    report_path = os.environ.get("BLACKHOLE_OCTANE_PROBE_REPORT_JSON", "")
    image_path = os.environ.get("BLACKHOLE_OCTANE_PROBE_IMAGE_PATH", "")
    width = int(os.environ.get("BLACKHOLE_OCTANE_PROBE_WIDTH", "96"))
    height = int(os.environ.get("BLACKHOLE_OCTANE_PROBE_HEIGHT", "54"))
    report = {
        "available_render_engines": [],
        "selected_engine": "",
        "bridge_library_path": "",
        "bridge_version": [],
        "bridge_capabilities": {},
        "studio_quality": {},
        "render_operator_result": [],
        "render_output_exists": False,
        "render_output_size": 0,
        "render_quality_metrics": {},
        "render_ready": False,
        "status": "started",
    }

    try:
        addon_utils.enable("blackhole_physics", default_set=False, persistent=False)

        from blackhole_physics import bridge, materials, quality

        report["available_render_engines"] = sorted(
            [
                cls.bl_idname
                for cls in bpy.types.RenderEngine.__subclasses__()
                if getattr(cls, "bl_idname", None)
            ]
        )
        engine_id = find_octane_engine()
        if engine_id is None:
            raise RuntimeError("Octane render engine is unavailable in this Blender session")

        report["selected_engine"] = engine_id
        report["bridge_library_path"] = bridge.get_library_path() or ""
        report["bridge_version"] = list(bridge.get_version_tuple())
        report["bridge_capabilities"] = bridge.get_capabilities()
        if not bridge.is_loaded():
            raise RuntimeError("Bridge library did not load inside OctaneBlender")

        scene = bpy.context.scene
        report["studio_quality"] = quality.apply_studio_quality(scene, target_engine=engine_id)
        props = scene.blackhole
        props.texture_width = width
        props.texture_height = height
        scene.render.resolution_x = width
        scene.render.resolution_y = height
        scene.render.resolution_percentage = 100
        scene.render.filepath = image_path

        bpy.ops.blackhole.preset_m87()
        horizon_result = bpy.ops.blackhole.generate_horizon()
        disk_result = bpy.ops.blackhole.generate_disk()
        disk_texture_result = bpy.ops.blackhole.render_disk_texture()
        lensing_map_result = bpy.ops.blackhole.render_lensing_map()
        material_result = bpy.ops.blackhole.setup_octane_materials()
        report["horizon_result"] = list(horizon_result)
        report["disk_result"] = list(disk_result)
        report["disk_texture_result"] = list(disk_texture_result)
        report["lensing_map_result"] = list(lensing_map_result)
        report["material_result"] = list(material_result)
        report["disk_material_state"] = materials.inspect_octane_disk_material_state()

        render_result = bpy.ops.render.render(write_still=True)
        report["render_operator_result"] = list(render_result)
        report["render_output_exists"] = bool(image_path and os.path.exists(image_path))
        if report["render_output_exists"]:
            report["render_output_size"] = os.path.getsize(image_path)
            if report["render_output_size"] > 0:
                report["render_quality_metrics"] = compute_quality_metrics(image_path)
                report["render_ready"] = report["render_quality_metrics"].get("nonzero_rgb_fraction", 0.0) > 0.0

        report["status"] = "success"
        return 0
    except Exception as exc:
        report["status"] = "failure"
        report["error"] = str(exc)
        report["traceback"] = traceback.format_exc()
        raise
    finally:
        if report_path:
            with open(report_path, "w", encoding="utf-8") as handle:
                json.dump(report, handle, indent=2, sort_keys=True)
                handle.write("\n")


if __name__ == "__main__":
    raise SystemExit(main())
