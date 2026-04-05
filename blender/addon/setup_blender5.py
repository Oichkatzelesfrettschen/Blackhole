# setup_blender5.py -- Run inside Blender 5.x to configure the addon.
#
# Usage: blender --python setup_blender5.py
#
# Enables the Blackhole Physics addon and configures Cycles for
# black hole visualization.

import bpy
import addon_utils
import sys

def main():
    print("\n" + "=" * 60)
    print("Blackhole Physics - Blender 5.x Setup")
    print("=" * 60)

    # Enable addons
    try:
        addon_utils.enable("blackhole_physics", default_set=True, persistent=True)
        print("[Setup] Enabled blackhole_physics addon")
    except Exception as e:
        raise RuntimeError(
            "Failed to enable blackhole_physics. Install the packaged addon zip first "
            "or set BLENDER_USER_SCRIPTS to a directory containing the addon."
        ) from e
    from blackhole_physics import quality

    # Set Cycles as render engine (Octane not available in stock Blender)
    scene = bpy.context.scene
    scene.render.engine = 'CYCLES'

    # GPU compute if available
    cycles_addon = bpy.context.preferences.addons.get('cycles')
    if cycles_addon is not None and hasattr(cycles_addon, 'preferences'):
        prefs = cycles_addon.preferences
        prefs.compute_device_type = 'CUDA'
        prefs.get_devices()
        for device in prefs.devices:
            device.use = True
        print("[Setup] Cycles GPU compute enabled")

    scene.render.resolution_x = 2048
    scene.render.resolution_y = 2048
    summary = quality.apply_studio_quality(scene, target_engine='CYCLES')
    print(f"[Setup] Studio quality applied: {summary}")

    bpy.ops.wm.save_userpref()
    print("[Setup] Blender 5.x configuration complete")
    print("=" * 60 + "\n")

if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"[Setup] ERROR: {exc}")
        raise SystemExit(1)
