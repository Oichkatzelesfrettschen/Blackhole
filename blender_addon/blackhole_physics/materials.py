# materials.py -- Octane and Cycles material setup for Blackhole objects
#
# Creates render-engine-aware materials:
# - Octane: OctaneDiffuseMat / OctaneGlossyMat with emission nodes
# - Cycles/EEVEE: Principled BSDF with emission

import bpy


def _is_octane():
    """Check if the current render engine is Octane."""
    return bpy.context.scene.render.engine in ('octane', 'OCTANE')


def _get_or_create_material(name):
    if name in bpy.data.materials:
        return bpy.data.materials[name]
    mat = bpy.data.materials.new(name)
    mat.use_nodes = True
    return mat


def _setup_cycles_emission(mat, image_name, strength=10.0):
    """Set up a Cycles/EEVEE emission material using an image texture."""
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (400, 0)

    emission = nodes.new('ShaderNodeEmission')
    emission.location = (200, 0)
    emission.inputs['Strength'].default_value = strength

    if image_name in bpy.data.images:
        tex = nodes.new('ShaderNodeTexImage')
        tex.location = (0, 0)
        tex.image = bpy.data.images[image_name]
        links.new(tex.outputs['Color'], emission.inputs['Color'])
    else:
        emission.inputs['Color'].default_value = (1.0, 0.5, 0.1, 1.0)

    links.new(emission.outputs['Emission'], output.inputs['Surface'])


def _setup_cycles_dark(mat):
    """Set up a pure black material for the event horizon."""
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (400, 0)

    diffuse = nodes.new('ShaderNodeBsdfDiffuse')
    diffuse.location = (200, 0)
    diffuse.inputs['Color'].default_value = (0.0, 0.0, 0.0, 1.0)
    diffuse.inputs['Roughness'].default_value = 1.0

    links.new(diffuse.outputs['BSDF'], output.inputs['Surface'])


def _setup_cycles_glass(mat, color=(0.2, 0.4, 1.0, 0.3)):
    """Set up a translucent material for the ergosphere."""
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (600, 0)

    glass = nodes.new('ShaderNodeBsdfGlass')
    glass.location = (200, 0)
    glass.inputs['Color'].default_value = color
    glass.inputs['Roughness'].default_value = 0.1
    glass.inputs['IOR'].default_value = 1.05

    links.new(glass.outputs['BSDF'], output.inputs['Surface'])

    mat.blend_method = 'BLEND' if hasattr(mat, 'blend_method') else 'OPAQUE'


def _setup_octane_emission(mat, image_name, power=10.0):
    """Set up an Octane emission material.

    Octane materials use custom node types when available.
    Falls back to Cycles nodes if Octane nodes aren't registered.
    """
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    # Check if Octane node types are available
    try:
        output = nodes.new('ShaderNodeOutputMaterial')
        output.location = (600, 0)

        # Try Octane-specific emission node
        if 'OctaneBlackBodyEmission' in dir(bpy.types):
            emission = nodes.new('OctaneBlackBodyEmission')
            emission.location = (200, 0)
            emission.inputs['Power'].default_value = power

            if image_name in bpy.data.images:
                tex = nodes.new('OctaneImageTexture')
                tex.location = (0, 0)
                tex.image = bpy.data.images[image_name]
                links.new(tex.outputs[0], emission.inputs['Texture'])

            links.new(emission.outputs[0], output.inputs['Surface'])
        else:
            # Fallback: use standard nodes (Octane interprets them)
            _setup_cycles_emission(mat, image_name, power)

    except Exception:
        _setup_cycles_emission(mat, image_name, power)


def _setup_octane_dark(mat):
    """Set up an Octane diffuse black material for the horizon."""
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    try:
        output = nodes.new('ShaderNodeOutputMaterial')
        output.location = (400, 0)

        if 'OctaneDiffuseMaterial' in dir(bpy.types):
            diffuse = nodes.new('OctaneDiffuseMaterial')
            diffuse.location = (200, 0)
            diffuse.inputs['Diffuse'].default_value = (0.0, 0.0, 0.0, 1.0)
            links.new(diffuse.outputs[0], output.inputs['Surface'])
        else:
            _setup_cycles_dark(mat)
    except Exception:
        _setup_cycles_dark(mat)


def setup_octane_materials(context):
    """Create and assign materials to all Blackhole objects."""
    is_oct = _is_octane()

    # Accretion disk -- emission from temperature
    disk_mat = _get_or_create_material("BH_AccretionDisk_Mat")
    if is_oct:
        _setup_octane_emission(disk_mat, "BlackholeDiskTexture", power=50.0)
    else:
        _setup_cycles_emission(disk_mat, "BlackholeDiskTexture", strength=50.0)

    if "AccretionDisk" in bpy.data.objects:
        obj = bpy.data.objects["AccretionDisk"]
        if obj.data.materials:
            obj.data.materials[0] = disk_mat
        else:
            obj.data.materials.append(disk_mat)

    # Event horizon -- pure black
    horizon_mat = _get_or_create_material("BH_EventHorizon_Mat")
    if is_oct:
        _setup_octane_dark(horizon_mat)
    else:
        _setup_cycles_dark(horizon_mat)

    if "EventHorizon" in bpy.data.objects:
        obj = bpy.data.objects["EventHorizon"]
        if obj.data.materials:
            obj.data.materials[0] = horizon_mat
        else:
            obj.data.materials.append(horizon_mat)

    # Ergosphere -- translucent blue
    ergo_mat = _get_or_create_material("BH_Ergosphere_Mat")
    _setup_cycles_glass(ergo_mat, color=(0.1, 0.3, 0.9, 0.15))

    if "Ergosphere" in bpy.data.objects:
        obj = bpy.data.objects["Ergosphere"]
        if obj.data.materials:
            obj.data.materials[0] = ergo_mat
        else:
            obj.data.materials.append(ergo_mat)

    # Geodesics -- white emission
    geodesic_mat = _get_or_create_material("BH_Geodesic_Mat")
    geodesic_mat.use_nodes = True
    nodes = geodesic_mat.node_tree.nodes
    links = geodesic_mat.node_tree.links
    nodes.clear()
    output = nodes.new('ShaderNodeOutputMaterial')
    output.location = (400, 0)
    emission = nodes.new('ShaderNodeEmission')
    emission.location = (200, 0)
    emission.inputs['Color'].default_value = (1.0, 1.0, 1.0, 1.0)
    emission.inputs['Strength'].default_value = 5.0
    links.new(emission.outputs['Emission'], output.inputs['Surface'])

    # Apply to all geodesic curves
    if "Blackhole Geodesics" in bpy.data.collections:
        for obj in bpy.data.collections["Blackhole Geodesics"].objects:
            if obj.data.materials:
                obj.data.materials[0] = geodesic_mat
            else:
                obj.data.materials.append(geodesic_mat)
