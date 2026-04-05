# materials.py -- Octane and Cycles material setup for Blackhole objects
#
# Creates render-engine-aware materials:
# - Octane: OctaneDiffuseMat / OctaneGlossyMat with emission nodes
# - Cycles/EEVEE: Principled BSDF with emission

import bpy
import math
import pathlib
import tempfile


def _is_octane():
    """Check if the current render engine is Octane."""
    return bpy.context.scene.render.engine in ('octane', 'OCTANE')


def _get_or_create_material(name):
    if name in bpy.data.materials:
        return bpy.data.materials[name]
    mat = bpy.data.materials.new(name)
    mat.use_nodes = True
    return mat


def _purge_unused_material_variants(base_name):
    """Remove stale unused material variants left behind by Octane conversions."""
    for material in list(bpy.data.materials):
        name = getattr(material, "name", "")
        if not name.startswith(base_name):
            continue
        if name == base_name:
            continue
        if material.users == 0:
            bpy.data.materials.remove(material)


def _link_first_output(links, src_node, dst_socket):
    if src_node is None:
        return False
    if len(src_node.outputs) == 0:
        return False
    links.new(src_node.outputs[0], dst_socket)
    return True


def _set_socket_default(node, socket_name, value):
    if node is None or socket_name not in node.inputs:
        return False
    socket = node.inputs[socket_name]
    if not hasattr(socket, "default_value"):
        return False
    socket.default_value = value
    return True


def _configure_octane_image_node(node, image_name, image_gain=1.0):
    if node is None:
        return None
    image = bpy.data.images.get(image_name)
    octane_image = _ensure_octane_file_backed_image(image_name) if image is not None else None
    image_for_node = octane_image or image
    if image_for_node is not None and hasattr(node, "image"):
        node.image = image_for_node
    if image_for_node is not None:
        filepath = image_for_node.filepath_from_user() if hasattr(image_for_node, "filepath_from_user") else ""
        if filepath:
            if hasattr(node, "a_filename"):
                node.a_filename = filepath
            if hasattr(node, "a_reload"):
                node.a_reload = True
        if hasattr(node, "update_image"):
            try:
                node.update_image(bpy.context)
            except Exception:
                pass
        if hasattr(node, "update_node_tree"):
            try:
                node.update_node_tree(bpy.context)
            except Exception:
                pass
    if "Power" in node.inputs:
        node.inputs["Power"].default_value = image_gain
    if "Legacy gamma" in node.inputs:
        node.inputs["Legacy gamma"].default_value = 1.0
    if "Linear sRGB invert" in node.inputs:
        node.inputs["Linear sRGB invert"].default_value = False
    if "Border mode (U)" in node.inputs:
        node.inputs["Border mode (U)"].default_value = "Clamp value"
    if "Border mode (V)" in node.inputs:
        node.inputs["Border mode (V)"].default_value = "Clamp value"
    return image_for_node


def _clamp01(value):
    return max(0.0, min(1.0, float(value)))


def _sample_image_rgba(image, pixels, u, v):
    width = max(1, int(image.size[0]))
    height = max(1, int(image.size[1]))
    channels = max(1, int(getattr(image, "channels", 4)))
    x = int(_clamp01(u) * float(width - 1) + 0.5)
    y = int(_clamp01(v) * float(height - 1) + 0.5)
    base = (y * width + x) * channels
    r = pixels[base] if base < len(pixels) else 0.0
    g = pixels[base + 1] if base + 1 < len(pixels) else r
    b = pixels[base + 2] if base + 2 < len(pixels) else r
    a = pixels[base + 3] if base + 3 < len(pixels) else 1.0
    return (_clamp01(r), _clamp01(g), _clamp01(b), _clamp01(a))


def _ensure_disk_color_attribute_from_image(obj, image_name, attribute_name="BlackholeDiskColor"):
    if obj is None or getattr(obj, "data", None) is None:
        return False
    mesh = obj.data
    image = bpy.data.images.get(image_name)
    if image is None:
        return False
    if getattr(mesh, "color_attributes", None) is None:
        return False
    if len(mesh.loops) == 0:
        return False

    attribute = mesh.color_attributes.get(attribute_name)
    if attribute is None or attribute.domain != "CORNER":
        if attribute is not None:
            mesh.color_attributes.remove(attribute)
        attribute = mesh.color_attributes.new(
            name=attribute_name,
            type="FLOAT_COLOR",
            domain="CORNER",
        )

    try:
        pixels = list(image.pixels[:])
    except Exception:
        return False
    if not pixels:
        return False

    uv_data = None
    if getattr(mesh, "uv_layers", None) is not None and mesh.uv_layers.active is not None:
        uv_data = mesh.uv_layers.active.data

    max_radius = 1.0
    if len(mesh.vertices) > 0:
        max_radius = max(
            1.0e-6,
            max(math.hypot(vertex.co.x, vertex.co.y) for vertex in mesh.vertices),
        )

    for loop_index, loop in enumerate(mesh.loops):
        if uv_data is not None and loop_index < len(uv_data):
            uv = uv_data[loop_index].uv
            u = float(uv.x)
            v = float(uv.y)
        else:
            co = mesh.vertices[loop.vertex_index].co
            radius = math.hypot(co.x, co.y) / max_radius
            angle = (math.atan2(co.y, co.x) / (2.0 * math.pi)) + 0.5
            u = angle
            v = radius
        rgba = _sample_image_rgba(image, pixels, u, v)
        attribute.data[loop_index].color = rgba

    for index, color_attribute in enumerate(mesh.color_attributes):
        if color_attribute.name == attribute_name:
            if hasattr(mesh.color_attributes, "active_color_index"):
                mesh.color_attributes.active_color_index = index
            if hasattr(mesh.color_attributes, "render_color_index"):
                mesh.color_attributes.render_color_index = index
            break
    mesh.update()
    return True


def _ensure_octane_file_backed_image(image_name):
    image = bpy.data.images.get(image_name)
    if image is None:
        return None
    try:
        filepath = image.filepath_from_user()
    except Exception:
        filepath = ""
    if filepath:
        try:
            image.filepath = str(pathlib.Path(filepath).resolve())
        except Exception:
            pass
        return image

    cache_dir = pathlib.Path(tempfile.gettempdir()) / "blackhole_octane_images"
    cache_dir.mkdir(parents=True, exist_ok=True)
    target_path = cache_dir / f"{image_name}.png"
    reloaded_name = f"{image_name}_OctaneFile"

    existing = bpy.data.images.get(reloaded_name)
    if existing is not None and pathlib.Path(existing.filepath_from_user()).exists():
        try:
            existing.filepath = str(pathlib.Path(existing.filepath_from_user()).resolve())
        except Exception:
            pass
        return existing

    image.filepath_raw = str(target_path)
    image.file_format = "PNG"
    image.save()

    loaded = bpy.data.images.load(str(target_path), check_existing=True)
    loaded.name = reloaded_name
    loaded.filepath = str(target_path.resolve())
    try:
        loaded.reload()
    except Exception:
        pass
    return loaded


def _setup_cycles_emission(mat, image_name, strength=10.0, prefer_file_backed=False):
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
        if prefer_file_backed:
            tex.image = _ensure_octane_file_backed_image(image_name) or bpy.data.images[image_name]
        else:
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
        output.location = (740, 0)

        material = nodes.new('OctaneDiffuseMaterial')
        material.location = (420, 0)
        _set_socket_default(material, 'Diffuse', (0.0, 0.0, 0.0))
        _set_socket_default(material, 'Roughness', 0.0)

        emission = nodes.new('OctaneTextureEmission')
        emission.location = (120, -80)
        _set_socket_default(emission, 'Power', power)
        _set_socket_default(emission, 'Surface brightness', True)
        _set_socket_default(emission, 'Double sided', False)
        _set_socket_default(emission, 'Visible on diffuse', True)
        _set_socket_default(emission, 'Visible on specular', True)
        _set_socket_default(emission, 'Transparent emission', False)
        _set_socket_default(emission, 'Sampling rate', 4.0)

        tex = nodes.new('OctaneRGBImage')
        tex.location = (-160, -80)
        _configure_octane_image_node(tex, image_name, image_gain=1.0)

        _link_first_output(links, tex, emission.inputs['Texture'])
        _link_first_output(links, emission, material.inputs['Emission'])
        _link_first_output(links, material, output.inputs['Surface'])

    except Exception:
        _setup_cycles_emission(mat, image_name, power)


def _setup_octane_emission_via_converter(obj, image_name, power=10.0):
    """Build a converter-friendly Cycles source and let Octane convert it."""
    if obj is None or getattr(obj, "data", None) is None:
        return False

    material_name = "BH_AccretionDisk_Mat"
    _purge_unused_material_variants(material_name)

    source = _get_or_create_material(material_name)
    _setup_cycles_emission(
        source,
        image_name,
        strength=power,
        prefer_file_backed=True,
    )

    if obj.data.materials:
        obj.data.materials[0] = source
    else:
        obj.data.materials.append(source)

    try:
        from octane.utils.converters.common import convert_to_octane_material
        converted = bool(convert_to_octane_material(obj, 0))
    except Exception:
        converted = False

    if converted:
        final_material = obj.material_slots[0].material if obj.material_slots else None
        if final_material is not None:
            if final_material.use_nodes and final_material.node_tree is not None:
                for node in final_material.node_tree.nodes:
                    if getattr(node, "bl_idname", "") == "OctaneRGBImage":
                        _configure_octane_image_node(node, image_name, image_gain=1.0)
            final_material["bh_octane_material_mode"] = "converted_cycles_emission"
            final_material["bh_octane_texture_image"] = image_name
        return True

    if obj.data.materials:
        _setup_octane_emission(obj.data.materials[0], image_name, power=power)
    return False


def _setup_octane_vertex_attribute_emission(obj, attribute_name="BlackholeDiskColor", power=10.0):
    if obj is None or getattr(obj, "data", None) is None:
        return False

    material_name = "BH_AccretionDisk_Mat"
    _purge_unused_material_variants(material_name)
    material = _get_or_create_material(material_name)
    material.use_nodes = True
    nodes = material.node_tree.nodes
    links = material.node_tree.links
    nodes.clear()

    try:
        output = nodes.new("ShaderNodeOutputMaterial")
        output.location = (720, 0)

        octane_material = nodes.new("OctaneUniversalMaterial")
        octane_material.location = (420, 0)
        _set_socket_default(octane_material, "Albedo", (0.0, 0.0, 0.0))
        _set_socket_default(octane_material, "Metallic", 0.0)
        _set_socket_default(octane_material, "Specular", 0.0)
        _set_socket_default(octane_material, "Roughness", 0.0)
        _set_socket_default(octane_material, "Opacity", 1.0)

        emission = nodes.new("OctaneTextureEmission")
        emission.location = (120, -80)
        _set_socket_default(emission, "Power", power)
        _set_socket_default(emission, "Surface brightness", True)
        _set_socket_default(emission, "Double sided", True)
        _set_socket_default(emission, "Visible on diffuse", True)
        _set_socket_default(emission, "Visible on specular", True)

        attribute = nodes.new("OctaneColorVertexAttribute")
        attribute.location = (-180, -80)
        _set_socket_default(attribute, "Name", attribute_name)

        _link_first_output(links, attribute, emission.inputs["Texture"])
        _link_first_output(links, emission, octane_material.inputs["Emission"])
        _link_first_output(links, octane_material, output.inputs["Surface"])

        material["bh_octane_material_mode"] = "vertex_attribute_emission"
        material["bh_octane_color_attribute"] = attribute_name
        if obj.data.materials:
            obj.data.materials[0] = material
        else:
            obj.data.materials.append(material)
        return True
    except Exception:
        return False


def inspect_octane_disk_material_state(obj_name="AccretionDisk", attribute_name="BlackholeDiskColor"):
    report = {
        "object_exists": False,
        "material_name": "",
        "material_mode": "",
        "color_attribute_name": "",
        "color_attribute_exists": False,
        "color_attribute_domain": "",
        "color_attribute_type": "",
        "color_attribute_active": False,
        "node_types": [],
        "emission_power": None,
    }

    obj = bpy.data.objects.get(obj_name)
    if obj is None or getattr(obj, "data", None) is None:
        return report

    report["object_exists"] = True
    mesh = obj.data
    color_attributes = getattr(mesh, "color_attributes", None)
    if color_attributes is not None:
        attribute = color_attributes.get(attribute_name)
        if attribute is not None:
            report["color_attribute_exists"] = True
            report["color_attribute_name"] = attribute.name
            report["color_attribute_domain"] = getattr(attribute, "domain", "")
            report["color_attribute_type"] = getattr(attribute, "data_type", "")
            active = getattr(color_attributes, "active_color", None)
            report["color_attribute_active"] = active is not None and getattr(active, "name", "") == attribute.name

    material = obj.material_slots[0].material if obj.material_slots else None
    if material is None:
        return report

    report["material_name"] = material.name
    report["material_mode"] = str(material.get("bh_octane_material_mode", ""))
    report["color_attribute_name"] = str(material.get("bh_octane_color_attribute", report["color_attribute_name"]))
    if material.use_nodes and material.node_tree is not None:
        report["node_types"] = [getattr(node, "bl_idname", type(node).__name__) for node in material.node_tree.nodes]
        for node in material.node_tree.nodes:
            if getattr(node, "bl_idname", "") == "OctaneTextureEmission" and "Power" in node.inputs:
                try:
                    report["emission_power"] = float(node.inputs["Power"].default_value)
                except Exception:
                    report["emission_power"] = None
                break
    return report


def _setup_octane_dark(mat):
    """Set up an Octane diffuse black material for the horizon."""
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()

    try:
        output = nodes.new('ShaderNodeOutputMaterial')
        output.location = (400, 0)

        diffuse = nodes.new('OctaneDiffuseMaterial')
        diffuse.location = (200, 0)
        _set_socket_default(diffuse, 'Diffuse', (0.0, 0.0, 0.0))
        _set_socket_default(diffuse, 'Roughness', 0.0)
        links.new(diffuse.outputs[0], output.inputs['Surface'])
    except Exception:
        _setup_cycles_dark(mat)


def setup_octane_materials(context):
    """Create and assign materials to all Blackhole objects."""
    is_oct = _is_octane()

    # Accretion disk -- emission from temperature
    if "AccretionDisk" in bpy.data.objects:
        obj = bpy.data.objects["AccretionDisk"]
        if is_oct:
            attribute_name = "BlackholeDiskColor"
            used_vertex_attribute = _ensure_disk_color_attribute_from_image(
                obj,
                "BlackholeDiskTexture",
                attribute_name=attribute_name,
            ) and _setup_octane_vertex_attribute_emission(
                obj,
                attribute_name=attribute_name,
                power=1.5,
            )
            if not used_vertex_attribute and not _setup_octane_emission_via_converter(obj, "BlackholeDiskTexture", power=12.0):
                disk_mat = _get_or_create_material("BH_AccretionDisk_Mat")
                _setup_octane_emission(disk_mat, "BlackholeDiskTexture", power=12.0)
                if obj.data.materials:
                    obj.data.materials[0] = disk_mat
                else:
                    obj.data.materials.append(disk_mat)
        else:
            disk_mat = _get_or_create_material("BH_AccretionDisk_Mat")
            _setup_cycles_emission(disk_mat, "BlackholeDiskTexture", strength=50.0)
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
