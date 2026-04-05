#!/usr/bin/env python3
"""Run inside Blender to smoke-test the packaged Blackhole addon."""

from __future__ import annotations

import ctypes
import json
import os
import traceback

import addon_utils
import bpy
import numpy as np


def find_engine_id(expectation: str) -> str | None:
    engines = []
    for cls in bpy.types.RenderEngine.__subclasses__():
        bl_idname = getattr(cls, "bl_idname", None)
        if bl_idname:
            engines.append(bl_idname)
    lowered = {engine.lower(): engine for engine in engines}
    if expectation == "cycles":
        return lowered.get("cycles")
    if expectation == "octane":
        for engine in engines:
            if "octane" in engine.lower():
                return engine
        return None
    return None


def main() -> int:
    label = os.environ.get("BLACKHOLE_SMOKE_LABEL", "blender")
    expectation = os.environ.get("BLACKHOLE_SMOKE_EXPECT_ENGINE", "")
    report_path = os.environ.get("BLACKHOLE_SMOKE_REPORT_JSON", "")
    report = {
        "label": label,
        "expectation": expectation,
        "available_render_engines": [],
        "selected_engine": "",
        "bridge_library_path": "",
        "bridge_version": [],
        "bridge_capabilities": {},
        "status": "started",
    }

    try:
        addon_utils.enable("blackhole_physics", default_set=False, persistent=False)

        import blackhole_physics  # noqa: F401
        from blackhole_physics import bridge, quality

        report["available_render_engines"] = sorted(
            [
                cls.bl_idname
                for cls in bpy.types.RenderEngine.__subclasses__()
                if getattr(cls, "bl_idname", None)
            ]
        )
        report["bridge_library_path"] = bridge.get_library_path() or ""
        if not hasattr(bpy.context.scene, "blackhole"):
            raise RuntimeError("Addon did not register scene.blackhole")
        if not bridge.is_loaded():
            raise RuntimeError("Bridge library did not load inside Blender")

        report["bridge_version"] = list(bridge.get_version_tuple())
        report["bridge_capabilities"] = bridge.get_capabilities()

        preset = bridge.get_preset_m87()
        if preset.mass_msun <= 0.0:
            raise RuntimeError("Preset M87 parameters were not populated")
        report["preset_mass_msun"] = preset.mass_msun

        engine_id = find_engine_id(expectation) if expectation else None
        if expectation and engine_id is None:
            raise RuntimeError(f"Required render engine '{expectation}' is unavailable")
        if engine_id is not None:
            bpy.context.scene.render.engine = engine_id
            report["selected_engine"] = engine_id
        report["studio_quality"] = quality.apply_studio_quality(bpy.context.scene, target_engine=engine_id)

        result = bpy.ops.blackhole.generate_horizon()
        if "FINISHED" not in result:
            raise RuntimeError(f"generate_horizon operator returned {result}")
        if "EventHorizon" not in bpy.data.objects:
            raise RuntimeError("EventHorizon object was not created")
        report["generated_horizon"] = True

        lensing = bridge.render_lensing_map(
            a_star=0.5,
            observer_r=64.0,
            inclination_rad=0.3,
            width=16,
            height=8,
        )
        if lensing.shape != (8, 16, 4):
            raise RuntimeError(f"Unexpected lensing-map shape: {lensing.shape}")
        report["lensing_shape"] = list(lensing.shape)

        lib = bridge.get_lib()
        if lib.bhb_has_cuda():
            framebuffer = np.zeros((8, 8, 4), dtype=np.float32)
            rc = lib.bhb_cuda_render_raytraced(
                ctypes.c_float(0.5),
                ctypes.c_float(32.0),
                ctypes.c_float(0.3),
                8,
                8,
                framebuffer.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            )
            if rc != 0:
                raise RuntimeError(f"bhb_cuda_render_raytraced failed with rc={rc}")
            report["cuda_smoke_rc"] = rc

        report["status"] = "success"
        print(f"[blackhole-smoke] {label}: success")
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
