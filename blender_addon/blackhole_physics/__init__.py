# Blackhole Physics Blender Addon
# Drives Blender with Kerr geodesics, CUDA kernels, and accretion disk physics
# from the Blackhole repository via libblackhole_bridge.so (ctypes).
#
# Compatible with: Blender 4.3+ (OctaneBlender), Blender 5.0+
# Render engines: Octane (OctaneBlender), Cycles, EEVEE

bl_info = {
    "name": "Blackhole Physics",
    "author": "Blackhole Project",
    "version": (1, 0, 0),
    "blender": (4, 3, 0),
    "location": "View3D > Sidebar > Blackhole",
    "description": "Kerr geodesics, accretion disk, and gravitational lensing from libblackhole_bridge",
    "category": "Physics",
}

import bpy
from bpy.props import (
    FloatProperty, IntProperty, BoolProperty,
    EnumProperty, StringProperty, PointerProperty,
)

from . import bridge
from . import operators
from . import panels
from . import materials
from . import assets
from . import render_engine
from . import quality
from . import sd_textures  # noqa: F401 -- imported for side-effects (clear_pipeline_cache on unregister)


classes = (
    operators.BH_OT_LoadLibrary,
    operators.BH_OT_GenerateGeodesics,
    operators.BH_OT_GenerateDisk,
    operators.BH_OT_GenerateHorizon,
    operators.BH_OT_GenerateErgosphere,
    operators.BH_OT_RenderLensingMap,
    operators.BH_OT_RenderDiskTexture,
    operators.BH_OT_ApplyPresetM87,
    operators.BH_OT_ApplyPresetSgrA,
    operators.BH_OT_SetupOctaneMaterials,
    operators.BH_OT_ApplyStudioQuality,
    operators.BH_OT_BuildAssets,
    operators.BH_OT_GenerateSDTexture,
    operators.BH_OT_ClearSDCache,
    operators.BH_OT_ExportGWWaveform,
    panels.BH_PT_MainPanel,
    panels.BH_PT_MetricPanel,
    panels.BH_PT_GeodesicsPanel,
    panels.BH_PT_DiskPanel,
    panels.BH_PT_TexturesPanel,
    panels.BH_PT_PresetsPanel,
    panels.BH_PT_SDPanel,
    panels.BH_PT_GWPanel,
    panels.BlackholeProperties,
)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.blackhole = PointerProperty(type=panels.BlackholeProperties)
    bridge.try_load_library()
    render_engine.register()


def unregister():
    render_engine.unregister()
    sd_textures.clear_pipeline_cache()
    bridge.unload_library()
    del bpy.types.Scene.blackhole
    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
