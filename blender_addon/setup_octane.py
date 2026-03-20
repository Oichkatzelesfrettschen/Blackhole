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

def enable_addon(module_name):
    """Enable a Blender addon by module name."""
    try:
        addon_utils.enable(module_name, default_set=True, persistent=True)
        print(f"[Setup] Enabled addon: {module_name}")
        return True
    except Exception as e:
        print(f"[Setup] Failed to enable {module_name}: {e}")
        return False


def setup_octane_render():
    """Configure Octane render engine settings."""
    scene = bpy.context.scene

    # Set render engine to Octane
    # OctaneBlender registers the engine as 'octane'
    available_engines = [e.bl_idname for e in bpy.types.RenderEngine.__subclasses__()]
    print(f"[Setup] Available render engines: {available_engines}")

    octane_engine = None
    for engine_id in ['octane', 'OCTANE', 'OctaneRender']:
        if engine_id in available_engines:
            octane_engine = engine_id
            break

    if octane_engine:
        scene.render.engine = octane_engine
        print(f"[Setup] Render engine set to: {octane_engine}")
    else:
        print("[Setup] WARNING: Octane render engine not found in this build")
        print("[Setup] Available engines:", available_engines)
        # Fallback to Cycles
        if 'CYCLES' in available_engines:
            scene.render.engine = 'CYCLES'
            print("[Setup] Fell back to Cycles")

    # Render settings for scientific visualization
    scene.render.resolution_x = 2048
    scene.render.resolution_y = 2048
    scene.render.film_transparent = True

    # If Octane settings are available, configure them
    if hasattr(scene, 'octane'):
        oct = scene.octane
        # High quality for black hole rendering
        if hasattr(oct, 'max_samples'):
            oct.max_samples = 4096
        if hasattr(oct, 'kernel_type'):
            oct.kernel_type = 'PATH_TRACING'  # Best for complex lighting
        print("[Setup] Octane settings configured")

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

    # Configure rendering
    setup_octane_render()
    setup_world()

    # Save preferences
    bpy.ops.wm.save_userpref()
    print("[Setup] User preferences saved")

    print("\n[Setup] Configuration complete!")
    print("[Setup] Open the Blackhole tab in the 3D Viewport sidebar (N)")
    print("=" * 60 + "\n")


if __name__ == "__main__":
    main()
