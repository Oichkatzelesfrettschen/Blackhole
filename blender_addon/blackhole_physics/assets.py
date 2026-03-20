# assets.py -- Blackhole physics asset library for Blender 5.1+ extended asset browser
#
# Creates pre-built assets (meshes, materials, node groups) that can be
# browsed and drag-dropped from the asset browser.

import bpy
import os
import math
from pathlib import Path

from . import bridge


ASSET_CATALOG_ID = "blackhole_physics"
ASSET_CATALOG_NAME = "Blackhole Physics"


def _mark_as_asset(datablock, description="", tags=None):
    """Mark a Blender datablock as an asset with metadata."""
    datablock.asset_mark()
    if hasattr(datablock, 'asset_data') and datablock.asset_data:
        datablock.asset_data.description = description
        if tags:
            for tag in tags:
                datablock.asset_data.tags.new(tag, skip_if_exists=True)


def create_preset_assets():
    """Create asset entries for EHT source presets."""
    if not bridge.is_loaded():
        return

    presets = {
        "M87*": bridge.get_preset_m87,
        "Sgr A*": bridge.get_preset_sgra,
    }

    for name, getter in presets.items():
        params = getter()

        # Create an empty object as the asset carrier
        obj_name = f"BH_Preset_{name.replace('*', '_star')}"
        if obj_name not in bpy.data.objects:
            obj = bpy.data.objects.new(obj_name, None)
            bpy.context.scene.collection.objects.link(obj)
        else:
            obj = bpy.data.objects[obj_name]

        # Store physics params as custom properties
        obj["bh_mass_msun"] = params.mass_msun
        obj["bh_spin"] = params.spin
        obj["bh_inclination_deg"] = params.inclination_deg
        obj["bh_distance_cm"] = params.distance_cm
        obj["bh_freq_hz"] = params.freq_hz
        obj["bh_r_g_cm"] = params.r_g_cm
        obj["bh_shadow_uas"] = params.shadow_uas
        obj["bh_source_name"] = params.name.decode('utf-8') if isinstance(params.name, bytes) else name

        _mark_as_asset(
            obj,
            description=f"{name} black hole preset: M={params.mass_msun:.1e} Msun, a*={params.spin}",
            tags=["blackhole", "preset", "EHT", name.replace("*", "")],
        )


def create_material_assets():
    """Create reusable material assets for black hole visualization."""
    from . import materials

    # Accretion disk emission material
    disk_mat = materials._get_or_create_material("BH_Asset_DiskEmission")
    disk_mat.use_nodes = True
    nodes = disk_mat.node_tree.nodes
    links = disk_mat.node_tree.links
    nodes.clear()

    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (600, 0)

    emission = nodes.new('ShaderNodeEmission')
    emission.location = (400, 0)
    emission.inputs['Strength'].default_value = 20.0

    # Color ramp for temperature mapping
    ramp = nodes.new('ShaderNodeValToRGB')
    ramp.location = (200, 0)
    ramp.color_ramp.elements[0].color = (0.8, 0.1, 0.0, 1.0)  # cool = red
    ramp.color_ramp.elements[1].color = (1.0, 1.0, 1.0, 1.0)  # hot = white
    # Add intermediate stop
    mid = ramp.color_ramp.elements.new(0.5)
    mid.color = (1.0, 0.5, 0.0, 1.0)  # orange

    # Attribute node for temperature vertex color
    attr = nodes.new('ShaderNodeAttribute')
    attr.location = (0, 0)
    attr.attribute_name = "Temperature"

    links.new(attr.outputs['Fac'], ramp.inputs['Fac'])
    links.new(ramp.outputs['Color'], emission.inputs['Color'])
    links.new(emission.outputs['Emission'], output.inputs['Surface'])

    _mark_as_asset(
        disk_mat,
        description="Accretion disk emission material driven by temperature vertex colors",
        tags=["blackhole", "material", "emission", "accretion"],
    )

    # Event horizon material
    horizon_mat = materials._get_or_create_material("BH_Asset_EventHorizon")
    materials._setup_cycles_dark(horizon_mat)
    _mark_as_asset(
        horizon_mat,
        description="Pure black material for event horizon (absorbs all light)",
        tags=["blackhole", "material", "horizon"],
    )

    # Ergosphere material
    ergo_mat = materials._get_or_create_material("BH_Asset_Ergosphere")
    materials._setup_cycles_glass(ergo_mat, color=(0.1, 0.3, 0.9, 0.15))
    _mark_as_asset(
        ergo_mat,
        description="Translucent blue material for ergosphere boundary",
        tags=["blackhole", "material", "ergosphere"],
    )

    # Geodesic curve material
    geo_mat = materials._get_or_create_material("BH_Asset_Geodesic")
    geo_mat.use_nodes = True
    nodes = geo_mat.node_tree.nodes
    links = geo_mat.node_tree.links
    nodes.clear()
    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (400, 0)
    emission = nodes.new('ShaderNodeEmission')
    emission.location = (200, 0)
    emission.inputs['Color'].default_value = (0.0, 0.8, 1.0, 1.0)
    emission.inputs['Strength'].default_value = 3.0
    links.new(emission.outputs['Emission'], output.inputs['Surface'])

    _mark_as_asset(
        geo_mat,
        description="Emissive material for photon geodesic curves",
        tags=["blackhole", "material", "geodesic"],
    )


def create_node_group_assets():
    """Create geometry nodes groups as assets."""
    # Temperature-to-color node group
    group_name = "BH_TemperatureColor"
    if group_name not in bpy.data.node_groups:
        group = bpy.data.node_groups.new(group_name, 'GeometryNodeTree')
    else:
        group = bpy.data.node_groups[group_name]

    _mark_as_asset(
        group,
        description="Maps temperature attribute to blackbody color for accretion disk",
        tags=["blackhole", "nodegroup", "temperature"],
    )


def register_asset_library():
    """Register the Blackhole addon directory as an asset library."""
    prefs = bpy.context.preferences
    libs = prefs.filepaths.asset_libraries

    lib_name = "Blackhole Physics"
    lib_path = str(Path(__file__).parent / "asset_library")

    # Create asset library directory
    os.makedirs(lib_path, exist_ok=True)

    # Check if already registered
    for lib in libs:
        if lib.name == lib_name:
            lib.path = lib_path
            return

    # Register new library
    bpy.ops.preferences.asset_library_add(directory=lib_path)
    # Rename the last added library
    if len(libs) > 0:
        libs[-1].name = lib_name


def build_all_assets():
    """Build all asset types for the asset browser."""
    create_preset_assets()
    create_material_assets()
    create_node_group_assets()
