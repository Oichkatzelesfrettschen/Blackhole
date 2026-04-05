# quality.py -- shared "studio-grade" quality configuration for Blender lanes

from __future__ import annotations

import bpy


OCTANE_KERNEL_TYPES = {
    "default": "0",
    "direct_light": "1",
    "path_tracing": "2",
    "pmc": "3",
    "info_channel": "4",
    "photon_tracing": "5",
}

OCTANE_KERNEL_LABELS = {value: key for key, value in OCTANE_KERNEL_TYPES.items()}

OCTANE_QUALITY_PROFILES = {
    "interactive": {
        "kernel_type": OCTANE_KERNEL_TYPES["path_tracing"],
        "max_samples": 768,
        "max_preview_samples": 96,
        "adaptive_sampling": True,
        "adaptive_min_samples": 64,
        "adaptive_noise_threshold": 0.035,
        "ai_light_enable": True,
        "ai_light_update": True,
        "ai_light_strength": 0.65,
        "filter_size": 1.0,
        "max_tile_samples": 24,
        "parallel_samples": 12,
        "coherent_ratio": 0.35,
        "max_diffuse_depth": 4,
        "max_glossy_depth": 8,
        "max_scatter_depth": 4,
        "gi_clamp": 12.0,
        "static_noise": False,
        "subsample_mode": "2x2 subsampling",
    },
    "balanced": {
        "kernel_type": OCTANE_KERNEL_TYPES["path_tracing"],
        "max_samples": 2048,
        "max_preview_samples": 144,
        "adaptive_sampling": True,
        "adaptive_min_samples": 128,
        "adaptive_noise_threshold": 0.015,
        "ai_light_enable": True,
        "ai_light_update": True,
        "ai_light_strength": 0.8,
        "filter_size": 1.2,
        "max_tile_samples": 40,
        "parallel_samples": 16,
        "coherent_ratio": 0.22,
        "max_diffuse_depth": 6,
        "max_glossy_depth": 12,
        "max_scatter_depth": 6,
        "gi_clamp": 24.0,
        "static_noise": True,
        "subsample_mode": "2x2 subsampling",
    },
    "cinematic": {
        "kernel_type": OCTANE_KERNEL_TYPES["path_tracing"],
        "max_samples": 4096,
        "max_preview_samples": 192,
        "adaptive_sampling": True,
        "adaptive_min_samples": 256,
        "adaptive_noise_threshold": 0.0075,
        "ai_light_enable": True,
        "ai_light_update": True,
        "ai_light_strength": 0.9,
        "filter_size": 1.35,
        "max_tile_samples": 56,
        "parallel_samples": 20,
        "coherent_ratio": 0.12,
        "max_diffuse_depth": 8,
        "max_glossy_depth": 16,
        "max_scatter_depth": 8,
        "gi_clamp": 48.0,
        "static_noise": True,
        "subsample_mode": "No subsampling",
    },
}

SHARED_QUALITY_PROFILES = {
    "interactive": {
        "view_transform": ("AgX", "Filmic", "Standard"),
        "look": ("None", "Medium High Contrast"),
        "exposure": 0.0,
        "gamma": 1.0,
        "cycles_samples": 1024,
        "cycles_preview_samples": 64,
        "cycles_adaptive_threshold": 0.006,
        "cycles_filter_width": 1.0,
        "use_compositor": False,
        "glare_threshold": 1.2,
        "glare_size": 4,
        "lens_distort": 0.004,
        "lens_dispersion": 0.001,
        "color_gain": (1.0, 1.0, 1.0),
    },
    "balanced": {
        "view_transform": ("AgX", "Filmic", "Standard"),
        "look": ("None", "Medium High Contrast", "High Contrast"),
        "exposure": 0.0,
        "gamma": 1.0,
        "cycles_samples": 2048,
        "cycles_preview_samples": 128,
        "cycles_adaptive_threshold": 0.003,
        "cycles_filter_width": 1.5,
        "use_compositor": True,
        "glare_threshold": 0.85,
        "glare_size": 5,
        "lens_distort": 0.008,
        "lens_dispersion": 0.003,
        "color_gain": (1.01, 1.005, 1.0),
    },
    "cinematic": {
        "view_transform": ("AgX", "Filmic", "Standard"),
        "look": ("Medium High Contrast", "High Contrast", "None"),
        "exposure": 0.0,
        "gamma": 1.0,
        "cycles_samples": 4096,
        "cycles_preview_samples": 192,
        "cycles_adaptive_threshold": 0.0015,
        "cycles_filter_width": 1.75,
        "use_compositor": True,
        "glare_threshold": 0.7,
        "glare_size": 6,
        "lens_distort": 0.0125,
        "lens_dispersion": 0.006,
        "color_gain": (1.03, 1.02, 1.0),
    },
}


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


def _set_value_if_available(owner, property_name, value):
    if not hasattr(owner, property_name):
        return None
    setattr(owner, property_name, value)
    return getattr(owner, property_name)


def _set_node_input_if_available(node, preferred_names, value):
    for name in preferred_names:
        if name in node.inputs:
            node.inputs[name].default_value = value
            return name
    for socket in node.inputs:
        if socket.name in preferred_names or socket.identifier in preferred_names:
            socket.default_value = value
            return socket.name
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
    if scene.render.engine in {"octane", "OCTANE"}:
        try:
            environment = nodes.new("OctaneTextureEnvironment")
            environment.location = (60, 0)
            _set_socket_default(environment, "Texture", (0.012, 0.016, 0.030))
            _set_socket_default(environment, "Power", 0.35)
            _set_socket_default(environment, "Visible environment (backplate)", True)
            _set_socket_default(environment, "Visible environment (reflections)", True)
            _set_socket_default(environment, "Visible environment (refractions)", True)
            output_socket = None
            for socket_name in ("Octane Environment", "Environment"):
                if socket_name in output.inputs:
                    output_socket = output.inputs[socket_name]
                    break
            if output_socket is None and len(output.inputs) > 0:
                output_socket = output.inputs[0]
            if output_socket is not None and len(environment.outputs) > 0:
                links.new(environment.outputs[0], output_socket)
                return world
        except Exception:
            nodes.clear()
            output = nodes.new("ShaderNodeOutputWorld")
            output.location = (300, 0)

    background = nodes.new("ShaderNodeBackground")
    background.location = (80, 0)
    background.inputs["Color"].default_value = (0.0, 0.0, 0.0, 1.0)
    background.inputs["Strength"].default_value = 0.0 if scene.render.engine == "BLACKHOLE_RT" else 0.05
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


def _configure_color_management(scene, quality_tier):
    if scene.render.engine == "BLACKHOLE_RT":
        display_settings = getattr(scene, "display_settings", None)
        if display_settings is not None:
            _set_enum_if_available(display_settings, "display_device", ("sRGB",))
        view_settings = scene.view_settings
        _set_enum_if_available(view_settings, "view_transform", ("Raw", "Standard"))
        _set_enum_if_available(view_settings, "look", ("None",))
        view_settings.exposure = 0.0
        view_settings.gamma = 1.0
        if hasattr(scene, "sequencer_colorspace_settings"):
            _set_enum_if_available(scene.sequencer_colorspace_settings, "name", ("Linear", "Linear Rec.709"))
        return
    shared_profile = SHARED_QUALITY_PROFILES[_normalize_octane_quality_tier(quality_tier)]
    display_settings = getattr(scene, "display_settings", None)
    if display_settings is not None:
        _set_enum_if_available(display_settings, "display_device", ("sRGB",))

    view_settings = scene.view_settings
    _set_enum_if_available(view_settings, "view_transform", shared_profile["view_transform"])
    _set_enum_if_available(view_settings, "look", shared_profile["look"])
    view_settings.exposure = shared_profile["exposure"]
    view_settings.gamma = shared_profile["gamma"]
    if hasattr(scene, "sequencer_colorspace_settings"):
        _set_enum_if_available(scene.sequencer_colorspace_settings, "name", ("Linear", "Linear Rec.709"))


def _configure_cycles(scene, quality_tier):
    if not hasattr(scene, "cycles"):
        return
    shared_profile = SHARED_QUALITY_PROFILES[_normalize_octane_quality_tier(quality_tier)]
    cycles = scene.cycles
    _set_enum_if_available(cycles, "device", ("GPU", "CPU"))
    if hasattr(cycles, "samples"):
        cycles.samples = shared_profile["cycles_samples"]
    if hasattr(cycles, "preview_samples"):
        cycles.preview_samples = shared_profile["cycles_preview_samples"]
    if hasattr(cycles, "use_adaptive_sampling"):
        cycles.use_adaptive_sampling = True
    if hasattr(cycles, "adaptive_threshold"):
        cycles.adaptive_threshold = shared_profile["cycles_adaptive_threshold"]
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
        cycles.filter_width = shared_profile["cycles_filter_width"]


def _normalize_octane_quality_tier(quality_tier):
    if quality_tier in (None, "", "auto"):
        return "balanced"
    tier = str(quality_tier).strip().lower()
    aliases = {
        "preview": "interactive",
        "fast": "interactive",
        "interactive": "interactive",
        "balanced": "balanced",
        "final": "balanced",
        "studio": "balanced",
        "cinematic": "cinematic",
        "production": "cinematic",
        "quality": "cinematic",
    }
    return aliases.get(tier, "balanced")


def _configure_octane(scene, quality_tier):
    octane = getattr(scene, "octane", None)
    if octane is None:
        return {}
    tier_name = _normalize_octane_quality_tier(quality_tier)
    profile = OCTANE_QUALITY_PROFILES[tier_name]
    summary = {}
    summary["quality_tier"] = tier_name
    kernel_type = _set_enum_if_available(octane, "kernel_type", (profile["kernel_type"],))
    if kernel_type is not None:
        summary["kernel_type"] = OCTANE_KERNEL_LABELS.get(kernel_type, kernel_type)
    subsample_mode = _set_enum_if_available(octane, "subsample_mode", (profile["subsample_mode"],))
    if subsample_mode is not None:
        summary["subsample_mode"] = subsample_mode
    for name in (
        "max_samples",
        "max_preview_samples",
        "adaptive_sampling",
        "adaptive_min_samples",
        "adaptive_noise_threshold",
        "ai_light_enable",
        "ai_light_update",
        "ai_light_strength",
        "filter_size",
        "max_tile_samples",
        "parallel_samples",
        "coherent_ratio",
        "max_diffuse_depth",
        "max_glossy_depth",
        "max_scatter_depth",
        "gi_clamp",
        "static_noise",
    ):
        if name not in profile:
            continue
        value = _set_value_if_available(octane, name, profile[name])
        if value is not None:
            summary[name] = value
    _set_enum_if_available(octane, "clay_mode", ("None",))
    summary["clay_mode"] = getattr(octane, "clay_mode", "")
    for flag_name in (
        "use_preview_camera_imager",
        "use_render_camera_imager",
        "use_preview_setting_for_camera_imager",
        "hdr_tonemap_preview_enable",
        "hdr_tonemap_render_enable",
        "maximize_instancing",
        "minimize_net_traffic",
    ):
        value = _set_value_if_available(octane, flag_name, True)
        if value is not None:
            summary[flag_name] = bool(value)
    return summary


def _capture_cycles(scene):
    cycles = getattr(scene, "cycles", None)
    if cycles is None:
        return {}
    summary = {}
    for name in (
        "device",
        "samples",
        "preview_samples",
        "use_adaptive_sampling",
        "adaptive_threshold",
        "use_denoising",
        "use_preview_denoising",
        "denoiser",
        "max_bounces",
        "diffuse_bounces",
        "glossy_bounces",
        "transmission_bounces",
        "transparent_max_bounces",
        "filter_width",
    ):
        if hasattr(cycles, name):
            summary[name] = getattr(cycles, name)
    return summary


def _capture_octane(scene):
    octane = getattr(scene, "octane", None)
    if octane is None:
        return {}
    summary = {}
    for name in (
        "octane_blender_version",
        "max_samples",
        "max_preview_samples",
        "adaptive_sampling",
        "adaptive_min_samples",
        "adaptive_noise_threshold",
        "kernel_type",
        "ai_light_enable",
        "ai_light_update",
        "ai_light_strength",
        "filter_size",
        "max_tile_samples",
        "parallel_samples",
        "coherent_ratio",
        "max_diffuse_depth",
        "max_glossy_depth",
        "max_scatter_depth",
        "gi_clamp",
        "static_noise",
        "clay_mode",
        "subsample_mode",
        "use_preview_camera_imager",
        "use_render_camera_imager",
        "use_preview_setting_for_camera_imager",
        "hdr_tonemap_preview_enable",
        "hdr_tonemap_render_enable",
    ):
        if hasattr(octane, name):
            value = getattr(octane, name)
            if name == "kernel_type":
                summary[name] = OCTANE_KERNEL_LABELS.get(value, value)
            else:
                summary[name] = value
    return summary


def _configure_compositor(scene, quality_tier):
    tier_name = _normalize_octane_quality_tier(quality_tier)
    shared_profile = SHARED_QUALITY_PROFILES[tier_name]
    if not shared_profile["use_compositor"]:
        scene.use_nodes = False
        return {
            "enabled": False,
            "quality_tier": tier_name,
            "glare_threshold": 0.0,
            "glare_size": 0,
            "lens_distort": 0.0,
            "lens_dispersion": 0.0,
            "color_gain": [1.0, 1.0, 1.0],
        }

    scene.use_nodes = True
    node_tree = getattr(scene, "node_tree", None)
    if node_tree is None:
        return {"enabled": False, "quality_tier": tier_name}
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
        color_balance.gain = shared_profile["color_gain"]
        links.new(render_layers.outputs["Image"], color_balance.inputs["Image"])
        links.new(color_balance.outputs["Image"], composite.inputs["Image"])
        links.new(color_balance.outputs["Image"], viewer.inputs["Image"])
        return {
            "enabled": True,
            "quality_tier": tier_name,
            "glare_threshold": 0.0,
            "glare_size": 0,
            "lens_distort": 0.0,
            "lens_dispersion": 0.0,
            "color_gain": list(shared_profile["color_gain"]),
        }

    glare = nodes.new("CompositorNodeGlare")
    glare.location = (260, 0)
    glare.glare_type = "FOG_GLOW"
    glare.quality = "HIGH"
    glare.threshold = shared_profile["glare_threshold"]
    glare.size = shared_profile["glare_size"]

    lens = nodes.new("CompositorNodeLensdist")
    lens.location = (520, 0)
    _set_node_input_if_available(lens, ("Distort", "distort"), shared_profile["lens_distort"])
    _set_node_input_if_available(lens, ("Dispersion", "dispersion"), shared_profile["lens_dispersion"])
    if hasattr(lens, "use_fit"):
        lens.use_fit = True

    color_balance = nodes.new("CompositorNodeColorBalance")
    color_balance.location = (720, 0)
    color_balance.correction_method = "LIFT_GAMMA_GAIN"
    color_balance.gain = shared_profile["color_gain"]

    links.new(render_layers.outputs["Image"], glare.inputs["Image"])
    links.new(glare.outputs["Image"], lens.inputs["Image"])
    links.new(lens.outputs["Image"], color_balance.inputs["Image"])
    links.new(color_balance.outputs["Image"], composite.inputs["Image"])
    links.new(color_balance.outputs["Image"], viewer.inputs["Image"])
    return {
        "enabled": True,
        "quality_tier": tier_name,
        "glare_threshold": shared_profile["glare_threshold"],
        "glare_size": shared_profile["glare_size"],
        "lens_distort": shared_profile["lens_distort"],
        "lens_dispersion": shared_profile["lens_dispersion"],
        "color_gain": list(shared_profile["color_gain"]),
    }


def configure_octane_cuda_hybrid_compositor(scene, backplate_image_name, quality_tier="auto"):
    """Compose Octane render layers over a CUDA-generated backplate.

    WHY: Octane and the Blackhole bridge are separate renderers, even when they
    both use the same CUDA-capable GPU. This compositor path is the explicit
    hybrid handoff: the GR/CUDA frame becomes the base image, and Octane's
    contribution is merged on top for offline lookdev and finishing.
    """
    tier_name = _normalize_octane_quality_tier(quality_tier)
    shared_profile = SHARED_QUALITY_PROFILES[tier_name]
    scene.use_nodes = True
    scene.render.use_compositing = True
    scene.render.film_transparent = True
    node_tree = getattr(scene, "node_tree", None)
    image = bpy.data.images.get(backplate_image_name)
    if node_tree is None or image is None:
        return {"enabled": False, "quality_tier": tier_name, "reason": "missing_backplate"}

    nodes = node_tree.nodes
    links = node_tree.links
    nodes.clear()

    image_node = nodes.new("CompositorNodeImage")
    image_node.location = (-320, 120)
    image_node.image = image

    render_layers = nodes.new("CompositorNodeRLayers")
    render_layers.location = (-320, -120)

    glare = nodes.new("CompositorNodeGlare")
    glare.location = (-60, 0)
    glare.glare_type = "FOG_GLOW"
    glare.quality = "HIGH"
    glare.threshold = shared_profile["glare_threshold"]
    glare.size = shared_profile["glare_size"]

    lens = nodes.new("CompositorNodeLensdist")
    lens.location = (180, 0)
    _set_node_input_if_available(lens, ("Distort", "distort"), shared_profile["lens_distort"])
    _set_node_input_if_available(lens, ("Dispersion", "dispersion"), shared_profile["lens_dispersion"])
    if hasattr(lens, "use_fit"):
        lens.use_fit = True

    luma = nodes.new("CompositorNodeRGBToBW")
    luma.location = (-60, -220)

    mask_gain = nodes.new("CompositorNodeMath")
    mask_gain.location = (180, -220)
    mask_gain.operation = "MULTIPLY"
    mask_gain.inputs[1].default_value = 5.0
    if hasattr(mask_gain, "use_clamp"):
        mask_gain.use_clamp = True

    set_alpha = nodes.new("CompositorNodeSetAlpha")
    set_alpha.location = (420, 0)

    alpha_over = nodes.new("CompositorNodeAlphaOver")
    alpha_over.location = (640, 0)
    alpha_over.premul = 1.0

    color_balance = nodes.new("CompositorNodeColorBalance")
    color_balance.location = (860, 0)
    color_balance.correction_method = "LIFT_GAMMA_GAIN"
    color_balance.gain = shared_profile["color_gain"]

    composite = nodes.new("CompositorNodeComposite")
    composite.location = (1080, 20)
    viewer = nodes.new("CompositorNodeViewer")
    viewer.location = (1080, -160)

    links.new(render_layers.outputs["Image"], glare.inputs["Image"])
    links.new(render_layers.outputs["Image"], luma.inputs["Image"])
    links.new(luma.outputs["Val"], mask_gain.inputs[0])
    links.new(glare.outputs["Image"], lens.inputs["Image"])
    links.new(lens.outputs["Image"], set_alpha.inputs["Image"])
    links.new(mask_gain.outputs["Value"], set_alpha.inputs["Alpha"])
    links.new(image_node.outputs["Image"], alpha_over.inputs[1])
    links.new(set_alpha.outputs["Image"], alpha_over.inputs[2])
    links.new(alpha_over.outputs["Image"], color_balance.inputs["Image"])
    links.new(color_balance.outputs["Image"], composite.inputs["Image"])
    links.new(color_balance.outputs["Image"], viewer.inputs["Image"])
    return {
        "enabled": True,
        "quality_tier": tier_name,
        "mode": "octane_cuda_hybrid_backplate",
        "backplate_image_name": backplate_image_name,
        "glare_threshold": shared_profile["glare_threshold"],
        "glare_size": shared_profile["glare_size"],
        "lens_distort": shared_profile["lens_distort"],
        "lens_dispersion": shared_profile["lens_dispersion"],
        "color_gain": list(shared_profile["color_gain"]),
        "render_film_transparent": bool(scene.render.film_transparent),
        "mask_gain": 5.0,
    }


def configure_octane_native_proxy_render(scene, quality_tier="auto"):
    """Configure a pure Octane proxy render without CUDA backplate composition."""
    tier_name = _normalize_octane_quality_tier(quality_tier)
    scene.use_nodes = False
    scene.render.use_compositing = False
    scene.render.film_transparent = False
    return {
        "enabled": True,
        "quality_tier": tier_name,
        "mode": "octane_native_proxy",
        "render_film_transparent": bool(scene.render.film_transparent),
    }


def apply_studio_quality(scene, target_engine=None, quality_tier="auto"):
    normalized_quality_tier = _normalize_octane_quality_tier(quality_tier)
    if target_engine:
        scene.render.engine = target_engine
    scene.render.film_transparent = scene.render.engine not in {"octane", "OCTANE"}
    scene.render.use_compositing = (
        False
        if scene.render.engine == "BLACKHOLE_RT"
        else SHARED_QUALITY_PROFILES[normalized_quality_tier]["use_compositor"]
    )
    scene.render.use_sequencer = False
    scene.render.image_settings.file_format = "PNG"
    scene.render.image_settings.color_mode = "RGBA"
    _ensure_world(scene)
    _ensure_camera(scene)
    _configure_color_management(scene, normalized_quality_tier)
    _configure_cycles(scene, normalized_quality_tier)
    octane_config = _configure_octane(scene, quality_tier)
    compositor_summary = _configure_compositor(scene, normalized_quality_tier)
    applied_quality_tier = (
        octane_config.get("quality_tier", normalized_quality_tier)
        if octane_config
        else normalized_quality_tier
    )
    return {
        "profile": "studio_grade_v4",
        "quality_tier": applied_quality_tier,
        "engine": scene.render.engine,
        "view_transform": getattr(scene.view_settings, "view_transform", ""),
        "look": getattr(scene.view_settings, "look", ""),
        "use_nodes": bool(scene.use_nodes),
        "compositor_configured": bool(compositor_summary.get("enabled", False)),
        "film_transparent": bool(scene.render.film_transparent),
        "compositor": compositor_summary,
        "cycles": _capture_cycles(scene),
        "octane": _capture_octane(scene) or octane_config,
    }
