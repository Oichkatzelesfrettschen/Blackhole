# setup_octane.py -- Run inside OctaneBlender to configure everything.
#
# Usage: OctaneBlender --python setup_octane.py
#
# This script:
# 1. Enables the Blackhole Physics addon
# 2. Sets Octane as the render engine
# 3. Configures Octane render settings for black hole visualization
# 4. Saves user preferences

import bpy
import addon_utils
import sys


DEFAULT_OCTANE_QUALITY_TIER = "balanced"

def enable_addon(module_name):
    """Enable a Blender addon by module name."""
    try:
        addon_utils.enable(module_name, default_set=True, persistent=True)
        print(f"[Setup] Enabled addon: {module_name}")
        return True
    except Exception as e:
        raise RuntimeError(
            f"Failed to enable {module_name}. Install the packaged addon zip first "
            "or set BLENDER_USER_SCRIPTS to a directory containing the addon."
        ) from e


def find_octane_engine_id():
    available_engines = [e.bl_idname for e in bpy.types.RenderEngine.__subclasses__()]
    print(f"[Setup] Available render engines: {available_engines}")
    for engine_id in available_engines:
        if "octane" in engine_id.lower():
            return engine_id, available_engines
    return None, available_engines


def setup_octane_render():
    """Configure Octane render engine settings."""
    scene = bpy.context.scene

    # Set render engine to Octane
    # OctaneBlender registers the engine as 'octane'
    octane_engine, available_engines = find_octane_engine_id()

    if octane_engine:
        scene.render.engine = octane_engine
        print(f"[Setup] Render engine set to: {octane_engine}")
    else:
        raise RuntimeError(
            "Octane render engine not found in this build. Use stock Blender with "
            "setup_blender5.py for the primary non-Octane lane."
        )

    scene.render.resolution_x = 2048
    scene.render.resolution_y = 2048

    print("[Setup] Render configuration complete")


def setup_world():
    """Configure world/environment for space scene."""
    world = bpy.data.worlds.get("World")
    if world is None:
        world = bpy.data.worlds.new("World")
    bpy.context.scene.world = world

    world.use_nodes = True
    nodes = world.node_tree.nodes
    links = world.node_tree.links
    nodes.clear()

    output = nodes.new('ShaderNodeOutputWorld')
    output.location = (400, 0)

    bg = nodes.new('ShaderNodeBackground')
    bg.location = (200, 0)
    bg.inputs['Color'].default_value = (0.0, 0.0, 0.0, 1.0)
    bg.inputs['Strength'].default_value = 0.0

    links.new(bg.outputs['Background'], output.inputs['Surface'])
    print("[Setup] World set to black (space)")


def main():
    print("\n" + "=" * 60)
    print("Blackhole Physics - OctaneBlender Setup")
    print("=" * 60)

    # Enable addons
    enable_addon("blackhole_physics")
    from blackhole_physics import quality

    # Configure rendering
    setup_octane_render()
    summary = quality.apply_studio_quality(
        bpy.context.scene,
        quality_tier=DEFAULT_OCTANE_QUALITY_TIER,
    )
    print(f"[Setup] Studio quality applied: {summary}")
    setup_world()

    # Save preferences
    bpy.ops.wm.save_userpref()
    print("[Setup] User preferences saved")

    print("\n[Setup] Configuration complete!")
    print("[Setup] Open the Blackhole tab in the 3D Viewport sidebar (N)")
    print("=" * 60 + "\n")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"[Setup] ERROR: {exc}")
        raise SystemExit(1)
