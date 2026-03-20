# setup_blender5.py -- Run inside Blender 5.x to configure the addon.
#
# Usage: blender --python setup_blender5.py
#
# Enables the Blackhole Physics addon and configures Cycles for
# black hole visualization.

import bpy
import addon_utils

def main():
    print("\n" + "=" * 60)
    print("Blackhole Physics - Blender 5.x Setup")
    print("=" * 60)

    # Enable addons
    try:
        addon_utils.enable("blackhole_physics", default_set=True, persistent=True)
        print("[Setup] Enabled blackhole_physics addon")
    except Exception as e:
        print(f"[Setup] Failed: {e}")

    # Set Cycles as render engine (Octane not available in stock Blender)
    scene = bpy.context.scene
    scene.render.engine = 'CYCLES'

    # GPU compute if available
    if hasattr(bpy.context.preferences.addons.get('cycles'), 'preferences'):
        prefs = bpy.context.preferences.addons['cycles'].preferences
        prefs.compute_device_type = 'CUDA'
        prefs.get_devices()
        for device in prefs.devices:
            device.use = True
        print("[Setup] Cycles GPU compute enabled")

    scene.render.resolution_x = 2048
    scene.render.resolution_y = 2048
    scene.render.film_transparent = True

    # Cycles settings
    scene.cycles.samples = 4096
    scene.cycles.use_denoising = True

    # Black world
    world = bpy.data.worlds.get("World") or bpy.data.worlds.new("World")
    scene.world = world
    world.use_nodes = True
    nodes = world.node_tree.nodes
    links = world.node_tree.links
    nodes.clear()
    output = nodes.new('ShaderNodeOutputWorld')
    bg = nodes.new('ShaderNodeBackground')
    bg.inputs['Color'].default_value = (0, 0, 0, 1)
    bg.inputs['Strength'].default_value = 0.0
    links.new(bg.outputs['Background'], output.inputs['Surface'])

    bpy.ops.wm.save_userpref()
    print("[Setup] Blender 5.x configuration complete")
    print("=" * 60 + "\n")

if __name__ == "__main__":
    main()
