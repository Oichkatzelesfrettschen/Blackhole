# quality.py -- shared "studio-grade" quality configuration for Blender lanes

from __future__ import annotations

import bpy


def _set_enum_if_available(owner, property_name, preferred_values):
    prop = owner.bl_rna.properties.get(property_name)
    if prop is None:
        return None
    available = {item.identifier for item in prop.enum_items}
    for value in preferred_values:
        if value in available:
            setattr(owner, property_name, value)
            return value
    return None


def _ensure_world(scene):
    world = scene.world or bpy.data.worlds.new("World")
    scene.world = world
    world.use_nodes = True
    nodes = world.node_tree.nodes
    links = world.node_tree.links
    nodes.clear()

    output = nodes.new("ShaderNodeOutputWorld")
    output.location = (300, 0)
    background = nodes.new("ShaderNodeBackground")
    background.location = (80, 0)
    background.inputs["Color"].default_value = (0.0, 0.0, 0.0, 1.0)
    background.inputs["Strength"].default_value = 0.0
    links.new(background.outputs["Background"], output.inputs["Surface"])
    return world


def _ensure_camera(scene):
    if scene.camera is None:
        camera_data = bpy.data.cameras.new("BlackholeStudioCamera")
        camera_obj = bpy.data.objects.new("BlackholeStudioCamera", camera_data)
        scene.collection.objects.link(camera_obj)
        scene.camera = camera_obj
    camera = scene.camera
    camera.data.lens = 65.0
    camera.data.sensor_width = 36.0
    camera.data.clip_start = 0.01
    camera.data.clip_end = 100000.0
    camera.data.passepartout_alpha = 0.85
    if hasattr(camera.data, "dof"):
        camera.data.dof.use_dof = False
    return camera


def _configure_color_management(scene):
    display_settings = getattr(scene, "display_settings", None)
    if display_settings is not None:
        _set_enum_if_available(display_settings, "display_device", ("sRGB",))

    view_settings = scene.view_settings
    _set_enum_if_available(view_settings, "view_transform", ("AgX", "Filmic", "Standard"))
    _set_enum_if_available(view_settings, "look", ("None", "Medium High Contrast", "High Contrast"))
    view_settings.exposure = 0.0
    view_settings.gamma = 1.0
    if hasattr(scene, "sequencer_colorspace_settings"):
        _set_enum_if_available(scene.sequencer_colorspace_settings, "name", ("Linear", "Linear Rec.709"))


def _configure_cycles(scene):
    if not hasattr(scene, "cycles"):
        return
    cycles = scene.cycles
    _set_enum_if_available(cycles, "device", ("GPU", "CPU"))
    if hasattr(cycles, "samples"):
        cycles.samples = 2048
    if hasattr(cycles, "preview_samples"):
        cycles.preview_samples = 128
    if hasattr(cycles, "use_adaptive_sampling"):
        cycles.use_adaptive_sampling = True
    if hasattr(cycles, "adaptive_threshold"):
        cycles.adaptive_threshold = 0.003
    if hasattr(cycles, "use_denoising"):
        cycles.use_denoising = True
    if hasattr(cycles, "use_preview_denoising"):
        cycles.use_preview_denoising = True
    _set_enum_if_available(cycles, "denoiser", ("OPTIX", "OPENIMAGEDENOISE", "AUTO"))
    if hasattr(cycles, "max_bounces"):
        cycles.max_bounces = 12
    if hasattr(cycles, "diffuse_bounces"):
        cycles.diffuse_bounces = 6
    if hasattr(cycles, "glossy_bounces"):
        cycles.glossy_bounces = 6
    if hasattr(cycles, "transmission_bounces"):
        cycles.transmission_bounces = 12
    if hasattr(cycles, "transparent_max_bounces"):
        cycles.transparent_max_bounces = 8
    if hasattr(cycles, "filter_width"):
        cycles.filter_width = 1.5


def _configure_octane(scene):
    octane = getattr(scene, "octane", None)
    if octane is None:
        return
    if hasattr(octane, "max_samples"):
        octane.max_samples = 4096
    if hasattr(octane, "adaptive_sampling"):
        octane.adaptive_sampling = True
    if hasattr(octane, "noise_threshold"):
        octane.noise_threshold = 0.0025
    _set_enum_if_available(octane, "kernel_type", ("PATH_TRACING",))


def _configure_compositor(scene):
    scene.use_nodes = True
    node_tree = getattr(scene, "node_tree", None)
    if node_tree is None:
        return False
    nodes = node_tree.nodes
    links = node_tree.links
    nodes.clear()

    render_layers = nodes.new("CompositorNodeRLayers")
    render_layers.location = (0, 0)

    composite = nodes.new("CompositorNodeComposite")
    composite.location = (900, 0)

    viewer = nodes.new("CompositorNodeViewer")
    viewer.location = (900, -180)

    engine_name = scene.render.engine
    if engine_name == "BLACKHOLE_RT":
        color_balance = nodes.new("CompositorNodeColorBalance")
        color_balance.location = (320, 0)
        color_balance.correction_method = "LIFT_GAMMA_GAIN"
        color_balance.gain = (1.02, 1.01, 1.0)
        links.new(render_layers.outputs["Image"], color_balance.inputs["Image"])
        links.new(color_balance.outputs["Image"], composite.inputs["Image"])
        links.new(color_balance.outputs["Image"], viewer.inputs["Image"])
        return True

    glare = nodes.new("CompositorNodeGlare")
    glare.location = (260, 0)
    glare.glare_type = "FOG_GLOW"
    glare.quality = "HIGH"
    glare.threshold = 0.7
    glare.size = 6

    lens = nodes.new("CompositorNodeLensdist")
    lens.location = (520, 0)
    lens.inputs["Distort"].default_value = 0.0125
    lens.inputs["Dispersion"].default_value = 0.006
    if hasattr(lens, "use_fit"):
        lens.use_fit = True

    color_balance = nodes.new("CompositorNodeColorBalance")
    color_balance.location = (720, 0)
    color_balance.correction_method = "LIFT_GAMMA_GAIN"
    color_balance.gain = (1.03, 1.02, 1.0)

    links.new(render_layers.outputs["Image"], glare.inputs["Image"])
    links.new(glare.outputs["Image"], lens.inputs["Image"])
    links.new(lens.outputs["Image"], color_balance.inputs["Image"])
    links.new(color_balance.outputs["Image"], composite.inputs["Image"])
    links.new(color_balance.outputs["Image"], viewer.inputs["Image"])
    return True


def apply_studio_quality(scene, target_engine=None):
    if target_engine:
        scene.render.engine = target_engine
    scene.render.film_transparent = True
    scene.render.use_compositing = True
    scene.render.use_sequencer = False
    scene.render.image_settings.file_format = "PNG"
    scene.render.image_settings.color_mode = "RGBA"
    _ensure_world(scene)
    _ensure_camera(scene)
    _configure_color_management(scene)
    _configure_cycles(scene)
    _configure_octane(scene)
    compositor_configured = _configure_compositor(scene)
    return {
        "engine": scene.render.engine,
        "view_transform": getattr(scene.view_settings, "view_transform", ""),
        "look": getattr(scene.view_settings, "look", ""),
        "use_nodes": bool(scene.use_nodes),
        "compositor_configured": bool(compositor_configured),
        "film_transparent": bool(scene.render.film_transparent),
    }
