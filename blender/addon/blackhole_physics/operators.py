# operators.py -- Blender operators for Blackhole physics
#
# Each operator calls into the bridge and creates/modifies Blender objects.

import math
import os
import json
import time

import bpy
import bmesh
import numpy as np
from mathutils import Vector

from . import bridge
from . import sd_textures
from . import quality


def _ensure_collection(name):
    """Get or create a collection for Blackhole objects."""
    if name in bpy.data.collections:
        return bpy.data.collections[name]
    coll = bpy.data.collections.new(name)
    bpy.context.scene.collection.children.link(coll)
    return coll


def _mesh_from_arrays(name, positions, indices, normals=None):
    """Create a Blender mesh from numpy arrays."""
    mesh = bpy.data.meshes.new(name)
    verts = [Vector(positions[i]) for i in range(len(positions))]
    faces = [tuple(indices[i]) for i in range(len(indices))]
    mesh.from_pydata(verts, [], faces)
    if normals is not None:
        mesh.normals_split_custom_set_from_vertices(
            [Vector(normals[i]) for i in range(len(normals))]
        )
    mesh.update()
    return mesh


def _image_from_array(name, data, width, height):
    """Create a Blender image from RGBA float numpy array."""
    if name in bpy.data.images:
        img = bpy.data.images[name]
        if img.size[0] != width or img.size[1] != height:
            bpy.data.images.remove(img)
            img = bpy.data.images.new(name, width, height, alpha=True, float_buffer=True)
    else:
        img = bpy.data.images.new(name, width, height, alpha=True, float_buffer=True)

    # Blender expects flat RGBA, bottom-to-top
    flipped = np.flipud(data).flatten()
    img.pixels.foreach_set(flipped.tolist())
    if hasattr(img, "alpha_mode"):
        img.alpha_mode = 'STRAIGHT'
    colorspace_settings = getattr(img, "colorspace_settings", None)
    if colorspace_settings is not None:
        available = {item.name for item in colorspace_settings.bl_rna.properties["name"].enum_items}
        for candidate in ("Linear Rec.709", "Linear", "Utility - Linear - sRGB"):
            if candidate in available:
                colorspace_settings.name = candidate
                break
    img.update()
    img.pack()
    return img


def _set_signature(target, token: str, payload: dict) -> None:
    """Stamp a cache signature onto a Blender ID block."""
    target["bh_signature_token"] = token
    target["bh_signature_payload"] = json.dumps(payload, sort_keys=True)


def _signature_matches(target, token: str) -> bool:
    """Check whether a Blender ID block carries the expected cache signature."""
    return str(target.get("bh_signature_token", "")) == token


def _policy_report_key() -> str:
    """Return the scene custom-property key for the latest policy run."""
    return "bh_last_policy_generation_report"


def _object_material_uses_image(object_name: str, image_name: str) -> bool:
    """Return whether an object's active materials reference the named image."""
    obj = bpy.data.objects.get(object_name)
    if obj is None or getattr(obj, "data", None) is None:
        return False
    for material in getattr(obj.data, "materials", []):
        if material is None or not material.use_nodes or material.node_tree is None:
            continue
        for node in material.node_tree.nodes:
            image = getattr(node, "image", None)
            if image is not None and getattr(image, "name", "") == image_name:
                return True
    return False


def _world_environment_uses_image(context, image_name: str) -> bool:
    """Return whether the active world environment is bound to the named image."""
    world = getattr(context.scene, "world", None)
    if world is None or not world.use_nodes or world.node_tree is None:
        return False
    for node in world.node_tree.nodes:
        if node.type == 'TEX_ENVIRONMENT':
            image = getattr(node, "image", None)
            if image is not None and getattr(image, "name", "") == image_name:
                return True
    return False


def _refresh_generated_slot_bindings(context, slot: str, image_name: str) -> dict:
    """Refresh scene bindings after generation and report what actually got wired."""
    from . import materials

    summary = {
        "slot": slot,
        "image_name": image_name,
        "material_refresh_applied": False,
        "disk_material_bound_image": False,
        "world_environment_bound_image": False,
    }
    if slot == "disk":
        materials.setup_octane_materials(context)
        summary["material_refresh_applied"] = True
        summary["disk_material_bound_image"] = _object_material_uses_image(
            "AccretionDisk",
            image_name,
        )
    else:
        summary["world_environment_bound_image"] = _world_environment_uses_image(
            context,
            image_name,
        )
    return summary


def _clear_signature(target) -> bool:
    """Remove cached signature metadata from a Blender ID block."""
    changed = False
    for key in ("bh_signature_token", "bh_signature_payload"):
        if key in target:
            del target[key]
            changed = True
    return changed


def _remove_image_if_present(name: str) -> bool:
    """Remove a generated Blender image by name when it exists."""
    image = bpy.data.images.get(name)
    if image is None:
        return False
    bpy.data.images.remove(image)
    return True


def _clear_world_environment_image(name: str) -> bool:
    """Detach the named environment image from the world before deletion."""
    changed = False
    world = getattr(bpy.context.scene, "world", None)
    if world is not None and world.use_nodes and world.node_tree is not None:
        for node in world.node_tree.nodes:
            if node.type == "TEX_ENVIRONMENT" and getattr(node, "image", None) is not None:
                if getattr(node.image, "name", "") == name:
                    node.image = None
                    changed = True
    return changed


def _clear_policy_prerequisites(context) -> list[str]:
    """Invalidate generated prerequisite artifacts without deleting user geometry."""
    actions: list[str] = []
    if _remove_image_if_present("BlackholeLensingMap"):
        actions.append("lensing_map_removed")
    if _remove_image_if_present("DreamTexturesSceneDepth"):
        actions.append("scene_depth_removed")

    scene = context.scene
    if scene.camera is not None and _clear_signature(scene.camera):
        actions.append("camera_signature_cleared")

    for object_name, action_name in (
        ("EventHorizon", "event_horizon_signature_cleared"),
        ("AccretionDisk", "accretion_disk_signature_cleared"),
    ):
        obj = bpy.data.objects.get(object_name)
        if obj is not None and _clear_signature(obj):
            actions.append(action_name)

    if _policy_report_key() in scene:
        del scene[_policy_report_key()]
        actions.append("policy_report_cleared")
    return actions


def _summarize_policy_actions(actions: list[str]) -> dict[str, int]:
    """Count reused/created/updated prerequisite actions for a policy run."""
    summary = {"reused": 0, "created": 0, "updated": 0, "other": 0}
    for action in actions:
        if action.endswith("_reused"):
            summary["reused"] += 1
        elif action.endswith("_created"):
            summary["created"] += 1
        elif action.endswith("_updated"):
            summary["updated"] += 1
        else:
            summary["other"] += 1
    summary["total"] = len(actions)
    return summary


def _store_policy_report(scene, report: dict) -> None:
    """Persist the latest policy-generation report on the scene for tooling."""
    scene[_policy_report_key()] = json.dumps(report, sort_keys=True)


def _load_policy_report(scene) -> dict:
    """Load the latest policy-generation report from the scene, if any."""
    raw = scene.get(_policy_report_key(), "")
    if not raw:
        return {}
    try:
        return json.loads(str(raw))
    except Exception:
        return {}


def _ensure_scene_camera(context, props):
    """Create or retune the policy camera and report whether it was reused."""
    scene = context.scene
    token = sd_textures.prerequisite_signature_token(props, "scene_camera")
    payload = sd_textures.prerequisite_signature(props, "scene_camera")
    if scene.camera is not None and _signature_matches(scene.camera, token):
        return scene.camera, "reused"

    camera_obj = scene.camera
    created = False
    if camera_obj is None:
        existing = bpy.data.objects.get("BH_Camera")
        if existing is not None and existing.type == 'CAMERA':
            camera_obj = existing
            if existing.name not in scene.collection.objects:
                scene.collection.objects.link(existing)
        else:
            camera_data = bpy.data.cameras.new("BH_Camera")
            camera_obj = bpy.data.objects.new("BH_Camera", camera_data)
            scene.collection.objects.link(camera_obj)
            created = True

    radius = float(getattr(props, "observer_distance", 500.0))
    inclination = math.radians(float(getattr(props, "inclination_deg", 17.0)))
    camera_obj.location = Vector((
        radius * math.sin(inclination),
        -radius * 0.15,
        radius * math.cos(inclination),
    ))
    direction = Vector((0.0, 0.0, 0.0)) - camera_obj.location
    camera_obj.rotation_euler = direction.to_track_quat('-Z', 'Y').to_euler()
    scene.camera = camera_obj
    _set_signature(camera_obj, token, payload)
    return camera_obj, "created" if created else "updated"


def _ensure_event_horizon(context, props):
    """Create or refresh the event horizon mesh when stale or missing."""
    token = sd_textures.prerequisite_signature_token(props, "horizon_geometry")
    payload = sd_textures.prerequisite_signature(props, "horizon_geometry")
    obj = bpy.data.objects.get("EventHorizon")
    if obj is not None and _signature_matches(obj, token):
        return "reused"
    state = "updated" if obj is not None else "created"
    result = bpy.ops.blackhole.generate_horizon()
    if 'FINISHED' not in result:
        raise RuntimeError("Failed to generate EventHorizon prerequisite")
    obj = bpy.data.objects.get("EventHorizon")
    if obj is not None:
        _set_signature(obj, token, payload)
    return state


def _ensure_accretion_disk(context, props):
    """Create or refresh the accretion disk mesh when stale or missing."""
    token = sd_textures.prerequisite_signature_token(props, "disk_geometry")
    payload = sd_textures.prerequisite_signature(props, "disk_geometry")
    obj = bpy.data.objects.get("AccretionDisk")
    if obj is not None and _signature_matches(obj, token):
        return "reused"
    state = "updated" if obj is not None else "created"
    result = bpy.ops.blackhole.generate_disk()
    if 'FINISHED' not in result:
        raise RuntimeError("Failed to generate AccretionDisk prerequisite")
    obj = bpy.data.objects.get("AccretionDisk")
    if obj is not None:
        _set_signature(obj, token, payload)
    return state


def _ensure_policy_lensing_source(props):
    """Ensure the lensing source exists and report whether it was reused or rebuilt."""
    token = sd_textures.prerequisite_signature_token(props, "lensing_map")
    existing = bpy.data.images.get("BlackholeLensingMap")
    if existing is not None and _signature_matches(existing, token):
        sd_textures._ensure_bridge_lensing_source(props)
        return "reused"
    sd_textures._ensure_bridge_lensing_source(props)
    image = bpy.data.images.get("BlackholeLensingMap")
    if image is not None:
        _set_signature(
            image,
            token,
            sd_textures.prerequisite_signature(props, "lensing_map"),
        )
    return "updated" if existing is not None else "created"


def _prepare_policy_generation_scene(context, props, slot: str, conditioning_mode: str) -> list[str]:
    """Ensure the scene prerequisites for a policy-driven generation run exist."""
    actions_taken: list[str] = []
    if slot != "disk":
        return actions_taken
    if conditioning_mode in {"image", "image_depth"}:
        actions_taken.append(f"lensing_map_{_ensure_policy_lensing_source(props)}")
    if conditioning_mode in {"depth", "image_depth"}:
        _camera, camera_state = _ensure_scene_camera(context, props)
        actions_taken.append(f"camera_{camera_state}")
        actions_taken.append(f"event_horizon_{_ensure_event_horizon(context, props)}")
        actions_taken.append(f"accretion_disk_{_ensure_accretion_disk(context, props)}")
    return actions_taken


def _generate_sd_texture_core(operator, context) -> tuple[set[str], dict]:
    """Run SD generation, apply it to the scene, and return a structured summary."""
    props = context.scene.blackhole

    operator.report({'INFO'}, "Generating SD texture -- this may take 10-60 s ...")

    try:
        data, metadata = sd_textures.generate_with_metadata(props)
    except RuntimeError as exc:
        operator.report({'ERROR'}, str(exc))
        return {'CANCELLED'}, {"status": "error", "error": str(exc)}
    except Exception as exc:
        operator.report({'ERROR'}, f"SD generation error: {exc}")
        return {'CANCELLED'}, {"status": "error", "error": f"SD generation error: {exc}"}

    w = props.texture_width
    h = props.texture_height
    slot = props.sd_target_slot
    conditioning = metadata.get("conditioning_policy", {})

    if slot == "disk":
        img_name = "BlackholeDiskTexture"
        _image_from_array(img_name, data, w, h)
        refresh_summary = _refresh_generated_slot_bindings(context, slot, img_name)
        operator.report(
            {'INFO'},
            f"SD disk texture generated ({w}x{h}). "
            f"Mode {conditioning.get('requested_mode', 'none')} -> "
            f"{conditioning.get('resolved_mode', conditioning.get('mode', 'none'))}. "
            f"'BlackholeDiskTexture' updated -- render the disk to see it."
        )
        world_environment_applied = False
    else:
        img_name = "BH_SD_Background"
        _image_from_array(img_name, data, w, h)
        _apply_as_world_background(context, img_name)
        refresh_summary = _refresh_generated_slot_bindings(context, slot, img_name)
        operator.report(
            {'INFO'},
            f"SD background generated ({w}x{h}). "
            f"Mode {conditioning.get('requested_mode', 'none')} -> "
            f"{conditioning.get('resolved_mode', conditioning.get('mode', 'none'))}. "
            f"World environment updated."
        )
        world_environment_applied = True

    return {'FINISHED'}, {
        "status": "success",
        "slot": slot,
        "image_name": img_name,
        "shape": list(data.shape),
        "selected_backend": metadata.get("selected_backend", ""),
        "prompt_style": getattr(props, "sd_prompt_style", "scientific"),
        "model_id": props.sd_model_path.strip(),
        "conditioning_policy": conditioning,
        "asset_digest": metadata.get("asset_digest", {}),
        "prompt_budget": metadata.get("prompt_budget", {}),
        "effective_steps": metadata.get("effective_steps"),
        "effective_guidance_scale": metadata.get("effective_guidance_scale"),
        "world_environment_applied": world_environment_applied,
        "binding_refresh": refresh_summary,
    }


class BH_OT_LoadLibrary(bpy.types.Operator):
    bl_idname = "blackhole.load_library"
    bl_label = "Load Physics Library"
    bl_description = "Load libblackhole_bridge.so"

    def execute(self, context):
        if bridge.try_load_library():
            self.report({'INFO'}, "Blackhole physics library loaded")
        else:
            self.report({'ERROR'}, "Failed to load libblackhole_bridge.so")
        return {'FINISHED'}


class BH_OT_GenerateGeodesics(bpy.types.Operator):
    bl_idname = "blackhole.generate_geodesics"
    bl_label = "Generate Geodesics"
    bl_description = "Trace photon geodesics around the black hole"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole

        rays = bridge.trace_geodesics_equatorial(
            a_star=props.spin,
            observer_r=props.observer_distance,
            b_min=props.geodesic_b_min,
            b_max=props.geodesic_b_max,
            n_rays=props.geodesic_count,
            max_steps=props.geodesic_max_steps,
            step_size=props.geodesic_step_size,
        )

        coll = _ensure_collection("Blackhole Geodesics")

        # Remove old geodesics
        for obj in list(coll.objects):
            bpy.data.objects.remove(obj, do_unlink=True)

        for i, ray in enumerate(rays):
            if len(ray) < 2:
                continue

            # Create curve from ray points
            curve_data = bpy.data.curves.new(f"Geodesic_{i:03d}", type='CURVE')
            curve_data.dimensions = '3D'
            curve_data.resolution_u = 2

            spline = curve_data.splines.new('POLY')
            spline.points.add(len(ray) - 1)  # one point already exists

            for j, pt in enumerate(ray):
                spline.points[j].co = (pt[0], pt[1], pt[2], 1.0)

            obj = bpy.data.objects.new(f"Geodesic_{i:03d}", curve_data)
            obj.data.bevel_depth = 0.02
            coll.objects.link(obj)

        self.report({'INFO'}, f"Generated {len(rays)} geodesic curves")
        return {'FINISHED'}


class BH_OT_GenerateDisk(bpy.types.Operator):
    bl_idname = "blackhole.generate_disk"
    bl_label = "Generate Accretion Disk"
    bl_description = "Generate thin accretion disk mesh with temperature data"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole

        positions, normals, temperatures, uvs, indices = bridge.generate_disk_mesh(
            a_star=props.spin,
            mass_msun=props.mass_msun,
            mdot_edd=props.mdot_edd,
            r_out_rg=props.disk_r_out,
            inclination_rad=props.inclination_rad,
            n_radial=props.disk_radial_res,
            n_azimuthal=props.disk_azimuthal_res,
        )

        coll = _ensure_collection("Blackhole Disk")

        mesh = _mesh_from_arrays("AccretionDisk", positions, indices, normals)

        # Add UV layer
        if not mesh.uv_layers:
            mesh.uv_layers.new(name="UVMap")
        uv_layer = mesh.uv_layers.active.data
        for poly in mesh.polygons:
            for li in range(poly.loop_start, poly.loop_start + poly.loop_total):
                vi = mesh.loops[li].vertex_index
                if vi < len(uvs):
                    uv_layer[li].uv = (uvs[vi][0], uvs[vi][1])

        # Store temperature as vertex color
        if not mesh.color_attributes:
            mesh.color_attributes.new("Temperature", 'FLOAT_COLOR', 'POINT')
        temp_attr = mesh.color_attributes["Temperature"]

        t_max = temperatures.max() if temperatures.max() > 0 else 1.0
        for i, t in enumerate(temperatures):
            tn = t / t_max
            # Hot = blue-white, cool = red
            r = min(1.0, tn * 2.0)
            g = min(1.0, max(0.0, tn * 3.0 - 0.5))
            b = min(1.0, max(0.0, tn * 4.0 - 1.5))
            temp_attr.data[i].color = (r, g, b, 1.0)

        # Create or update object
        obj_name = "AccretionDisk"
        if obj_name in bpy.data.objects:
            obj = bpy.data.objects[obj_name]
            obj.data = mesh
        else:
            obj = bpy.data.objects.new(obj_name, mesh)
            coll.objects.link(obj)

        mesh.update()
        self.report({'INFO'}, f"Generated disk: {len(positions)} verts, {len(indices)} tris")
        return {'FINISHED'}


class BH_OT_GenerateHorizon(bpy.types.Operator):
    bl_idname = "blackhole.generate_horizon"
    bl_label = "Generate Event Horizon"
    bl_description = "Generate event horizon mesh (oblate sphere for Kerr)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole
        positions, indices = bridge.generate_horizon_mesh(
            a_star=props.spin,
            n_theta=props.horizon_theta_res,
            n_phi=props.horizon_phi_res,
        )

        coll = _ensure_collection("Blackhole Structure")
        mesh = _mesh_from_arrays("EventHorizon", positions, indices)

        obj_name = "EventHorizon"
        if obj_name in bpy.data.objects:
            obj = bpy.data.objects[obj_name]
            obj.data = mesh
        else:
            obj = bpy.data.objects.new(obj_name, mesh)
            coll.objects.link(obj)

        mesh.update()
        self.report({'INFO'}, f"Generated event horizon: {len(positions)} verts")
        return {'FINISHED'}


class BH_OT_GenerateErgosphere(bpy.types.Operator):
    bl_idname = "blackhole.generate_ergosphere"
    bl_label = "Generate Ergosphere"
    bl_description = "Generate ergosphere boundary mesh"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole
        positions, indices = bridge.generate_ergosphere_mesh(
            a_star=props.spin,
            n_theta=props.horizon_theta_res,
            n_phi=props.horizon_phi_res,
        )

        coll = _ensure_collection("Blackhole Structure")
        mesh = _mesh_from_arrays("Ergosphere", positions, indices)

        obj_name = "Ergosphere"
        if obj_name in bpy.data.objects:
            obj = bpy.data.objects[obj_name]
            obj.data = mesh
        else:
            obj = bpy.data.objects.new(obj_name, mesh)
            coll.objects.link(obj)

        mesh.update()
        self.report({'INFO'}, f"Generated ergosphere: {len(positions)} verts")
        return {'FINISHED'}


class BH_OT_RenderLensingMap(bpy.types.Operator):
    bl_idname = "blackhole.render_lensing_map"
    bl_label = "Render Lensing Map"
    bl_description = "Generate gravitational lensing texture (redshift + Doppler)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole
        w = props.texture_width
        h = props.texture_height

        data = bridge.render_lensing_map(
            a_star=props.spin,
            observer_r=props.observer_distance,
            inclination_rad=props.inclination_rad,
            width=w, height=h,
        )

        image = _image_from_array("BlackholeLensingMap", data, w, h)
        _set_signature(
            image,
            sd_textures.prerequisite_signature_token(props, "lensing_map"),
            sd_textures.prerequisite_signature(props, "lensing_map"),
        )
        self.report({'INFO'}, f"Rendered lensing map {w}x{h}")
        return {'FINISHED'}


class BH_OT_RenderDiskTexture(bpy.types.Operator):
    bl_idname = "blackhole.render_disk_texture"
    bl_label = "Render Disk Texture"
    bl_description = "Generate accretion disk emission texture"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole
        w = props.texture_width
        h = props.texture_height // 4  # disk texture is typically wide and short

        data = bridge.render_disk_texture(
            a_star=props.spin,
            mass_msun=props.mass_msun,
            mdot_edd=props.mdot_edd,
            r_out_rg=props.disk_r_out,
            inclination_rad=props.inclination_rad,
            width=w, height=h,
        )

        _image_from_array("BlackholeDiskTexture", data, w, h)
        self.report({'INFO'}, f"Rendered disk texture {w}x{h}")
        return {'FINISHED'}


class BH_OT_ApplyPresetM87(bpy.types.Operator):
    bl_idname = "blackhole.preset_m87"
    bl_label = "M87*"
    bl_description = "Apply M87* EHT parameters"

    def execute(self, context):
        params = bridge.get_preset_m87()
        props = context.scene.blackhole
        props.mass_msun = params.mass_msun
        props.spin = params.spin
        props.inclination_deg = params.inclination_deg
        self.report({'INFO'}, f"Applied M87* preset: {params.mass_msun:.1e} Msun, a*={params.spin}")
        return {'FINISHED'}


class BH_OT_ApplyPresetSgrA(bpy.types.Operator):
    bl_idname = "blackhole.preset_sgra"
    bl_label = "Sgr A*"
    bl_description = "Apply Sgr A* EHT parameters"

    def execute(self, context):
        params = bridge.get_preset_sgra()
        props = context.scene.blackhole
        props.mass_msun = params.mass_msun
        props.spin = params.spin
        props.inclination_deg = params.inclination_deg
        self.report({'INFO'}, f"Applied Sgr A* preset: {params.mass_msun:.1e} Msun, a*={params.spin}")
        return {'FINISHED'}


class BH_OT_SetupOctaneMaterials(bpy.types.Operator):
    bl_idname = "blackhole.setup_octane_materials"
    bl_label = "Setup Octane Materials"
    bl_description = "Create Octane-compatible materials for black hole objects"

    def execute(self, context):
        from . import materials
        materials.setup_octane_materials(context)
        self.report({'INFO'}, "Octane materials configured")
        return {'FINISHED'}


class BH_OT_ApplyStudioQuality(bpy.types.Operator):
    bl_idname = "blackhole.apply_studio_quality"
    bl_label = "Apply Studio Quality"
    bl_description = "Configure render, color management, and compositor settings for production-quality output"

    def execute(self, context):
        summary = quality.apply_studio_quality(context.scene)
        self.report(
            {'INFO'},
            f"Studio quality applied: engine={summary['engine']} view={summary['view_transform']} look={summary['look']}",
        )
        return {'FINISHED'}


class BH_OT_BuildAssets(bpy.types.Operator):
    bl_idname = "blackhole.build_assets"
    bl_label = "Build Asset Library"
    bl_description = "Create browsable assets for the extended asset browser (presets, materials, node groups)"

    def execute(self, context):
        from . import assets
        assets.build_all_assets()
        self.report({'INFO'}, "Blackhole asset library built")
        return {'FINISHED'}


class BH_OT_GenerateSDTexture(bpy.types.Operator):
    """Generate a physics-conditioned texture using Stable Diffusion.

    WHY: SD inference produces astrophysically-inspired textures
    (accretion disk emission, deep-field backgrounds) without requiring
    GRMHD simulation data.  The generated images feed directly into
    Blackhole's material system (BH_AccretionDisk_Mat) and world
    environment, then are lensed by the Kerr geodesic render engine.

    WHAT: Two backends are supported --
      - sd_cpp: calls the 'sd' binary (stable-diffusion.cpp-cublas-git)
        in a subprocess; zero CUDA context conflict.
      - dream_textures: uses Blender's Dream Textures addon for CUDA-backed
        text-to-image generation, with seamless tiling on disk textures.
      - diffusers: uses python-diffusers in-process; pipeline is cached.
    Auto mode chooses sd_cpp for .gguf paths, Dream Textures for HF models
    when available, and diffusers otherwise.
    """

    bl_idname = "blackhole.generate_sd_texture"
    bl_label = "Generate SD Texture"
    bl_description = (
        "Generate an astrophysics texture with Stable Diffusion and apply it "
        "to the selected slot (disk emission or background)"
    )
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        status, _summary = _generate_sd_texture_core(self, context)
        return status

    def invoke(self, context, event):
        props = context.scene.blackhole
        if not props.sd_model_path.strip():
            self.report(
                {'ERROR'},
                "Set 'SD Model' (a .gguf path or HuggingFace model ID) before generating."
            )
            return {'CANCELLED'}
        return self.execute(context)


def _generate_sd_texture_with_overrides(
    operator,
    context,
    slot: str,
    conditioning_mode: str,
    *,
    intent: str = "production",
    prepare_only: bool = False,
) -> set[str]:
    """Run policy-driven prepare/generate flow with temporary slot/mode overrides."""
    props = context.scene.blackhole
    scene = context.scene
    original_slot = props.sd_target_slot
    original_mode = props.sd_conditioning_mode
    props.sd_target_slot = slot
    props.sd_conditioning_mode = conditioning_mode
    total_start = time.monotonic()
    try:
        resolved_mode = sd_textures.resolve_requested_conditioning_mode(props, conditioning_mode)
        defaults = sd_textures.conditioning_preflight_plan(props, slot=slot, intent=intent)
        prep_start = time.monotonic()
        actions = _prepare_policy_generation_scene(context, props, slot, resolved_mode)
        prep_seconds = time.monotonic() - prep_start
        report = {
            "status": "success",
            "slot": slot,
            "intent": intent,
            "requested_mode": conditioning_mode,
            "resolved_mode": resolved_mode,
            "scene_profile": defaults["scene_profile"],
            "preflight_actions": list(defaults["actions"]),
            "preparation_actions": actions,
            "preparation_summary": _summarize_policy_actions(actions),
            "prepare_only": bool(prepare_only),
            "generated": False,
            "generation": {},
            "timing": {
                "preparation_seconds": prep_seconds,
                "generation_seconds": 0.0,
                "total_seconds": 0.0,
            },
        }
        if actions:
            operator.report({'INFO'}, f"Prepared scene prerequisites: {', '.join(actions)}")
        if prepare_only:
            report["timing"]["total_seconds"] = time.monotonic() - total_start
            _store_policy_report(scene, report)
            return {'FINISHED'}
        generation_start = time.monotonic()
        status, generation_summary = _generate_sd_texture_core(operator, context)
        report["generated"] = status == {'FINISHED'}
        report["generation"] = generation_summary
        report["status"] = "success" if status == {'FINISHED'} else "cancelled"
        report["timing"]["generation_seconds"] = time.monotonic() - generation_start
        report["timing"]["total_seconds"] = time.monotonic() - total_start
        _store_policy_report(scene, report)
        return status
    finally:
        props.sd_target_slot = original_slot
        props.sd_conditioning_mode = original_mode


class BH_OT_PrepareSceneForPolicyGeneration(bpy.types.Operator):
    """Prepare the active scene for a policy-driven Dream Textures run."""

    bl_idname = "blackhole.prepare_scene_for_policy_generation"
    bl_label = "Prepare Scene for Policy Generation"
    bl_description = "Create or refresh only the prerequisite scene inputs required by the selected policy"
    bl_options = {'REGISTER', 'UNDO'}

    target_slot: bpy.props.EnumProperty(
        name="Target Slot",
        items=[
            ("disk", "Disk", "Prepare the disk-generation prerequisites"),
            ("background", "Background", "Prepare the background-generation prerequisites"),
        ],
        default="disk",
    )
    intent: bpy.props.EnumProperty(
        name="Intent",
        items=[
            ("interactive", "Interactive", "Prepare the scene for the measured interactive policy"),
            ("production", "Production", "Prepare the scene for the measured production policy"),
        ],
        default="production",
    )

    def execute(self, context):
        defaults = sd_textures.conditioning_preflight_plan(
            context.scene.blackhole,
            slot=self.target_slot,
            intent=self.intent,
        )
        status = _generate_sd_texture_with_overrides(
            self,
            context,
            defaults["slot"],
            defaults["conditioning_mode"],
            intent=self.intent,
            prepare_only=True,
        )
        if status == {'FINISHED'}:
            report = _load_policy_report(context.scene)
            summary = report.get("preparation_summary", {})
            self.report(
                {'INFO'},
                "Prepared scene inputs: "
                f"{summary.get('reused', 0)} reused, "
                f"{summary.get('created', 0)} created, "
                f"{summary.get('updated', 0)} updated."
            )
        return status


class BH_OT_GenerateDiskTextureWithPolicy(bpy.types.Operator):
    """Generate the disk texture using the measured scene policy."""

    bl_idname = "blackhole.generate_disk_texture_with_policy"
    bl_label = "Regenerate Disk (Scene Policy)"
    bl_description = "Generate the Blackhole disk texture using the measured production policy"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        defaults = sd_textures.conditioning_preflight_plan(
            context.scene.blackhole,
            slot="disk",
            intent="production",
        )
        return _generate_sd_texture_with_overrides(
            self,
            context,
            defaults["slot"],
            defaults["conditioning_mode"],
            intent="production",
        )


class BH_OT_GenerateDiskTextureWithInteractivePolicy(bpy.types.Operator):
    """Generate the disk texture using the measured interactive policy."""

    bl_idname = "blackhole.generate_disk_texture_with_interactive_policy"
    bl_label = "Regenerate Disk (Interactive Policy)"
    bl_description = "Generate the Blackhole disk texture using the measured interactive policy"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        defaults = sd_textures.conditioning_preflight_plan(
            context.scene.blackhole,
            slot="disk",
            intent="interactive",
        )
        return _generate_sd_texture_with_overrides(
            self,
            context,
            defaults["slot"],
            defaults["conditioning_mode"],
            intent="interactive",
        )


class BH_OT_GenerateBackgroundTextureWithPolicy(bpy.types.Operator):
    """Generate the background texture using the safe default scene policy."""

    bl_idname = "blackhole.generate_background_texture_with_policy"
    bl_label = "Regenerate Background (Scene Policy)"
    bl_description = "Generate the Blackhole background texture using the reliable slot default"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        defaults = sd_textures.conditioning_preflight_plan(
            context.scene.blackhole,
            slot="background",
            intent="production",
        )
        return _generate_sd_texture_with_overrides(
            self,
            context,
            defaults["slot"],
            defaults["conditioning_mode"],
            intent="production",
        )


class BH_OT_InvalidateDiskTextureArtifacts(bpy.types.Operator):
    """Remove generated disk texture artifacts while preserving geometry."""

    bl_idname = "blackhole.invalidate_sd_disk_artifacts"
    bl_label = "Invalidate Disk Texture Artifacts"
    bl_description = "Remove generated disk textures and clear the last policy report"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        actions: list[str] = []
        if _remove_image_if_present("BlackholeDiskTexture"):
            actions.append("disk_texture_removed")
        if _policy_report_key() in context.scene:
            del context.scene[_policy_report_key()]
            actions.append("policy_report_cleared")
        message = ", ".join(actions) if actions else "No disk artifacts to invalidate."
        self.report({'INFO'}, message)
        return {'FINISHED'}


class BH_OT_InvalidateBackgroundTextureArtifacts(bpy.types.Operator):
    """Remove generated background artifacts while preserving user world setup."""

    bl_idname = "blackhole.invalidate_sd_background_artifacts"
    bl_label = "Invalidate Background Texture Artifacts"
    bl_description = "Remove generated background images and detach them from the world environment"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        actions: list[str] = []
        if _clear_world_environment_image("BH_SD_Background"):
            actions.append("world_environment_cleared")
        if _remove_image_if_present("BH_SD_Background"):
            actions.append("background_texture_removed")
        if _policy_report_key() in context.scene:
            del context.scene[_policy_report_key()]
            actions.append("policy_report_cleared")
        message = ", ".join(actions) if actions else "No background artifacts to invalidate."
        self.report({'INFO'}, message)
        return {'FINISHED'}


class BH_OT_InvalidatePolicyPrerequisites(bpy.types.Operator):
    """Invalidate cached prerequisite signatures and generated source images."""

    bl_idname = "blackhole.invalidate_policy_prerequisites"
    bl_label = "Invalidate Policy Prerequisites"
    bl_description = "Clear prerequisite cache signatures so the next policy run refreshes generated inputs"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        actions = _clear_policy_prerequisites(context)
        message = ", ".join(actions) if actions else "No policy prerequisites to invalidate."
        self.report({'INFO'}, message)
        return {'FINISHED'}


class BH_OT_ClearSDCache(bpy.types.Operator):
    """Free cached diffusers pipeline and reclaim VRAM."""

    bl_idname = "blackhole.clear_sd_cache"
    bl_label = "Clear SD Pipeline Cache"
    bl_description = "Free the cached diffusers model from VRAM"

    def execute(self, context):
        sd_textures.clear_pipeline_cache()
        self.report({'INFO'}, "SD pipeline cache cleared")
        return {'FINISHED'}


class BH_OT_ExportGWWaveform(bpy.types.Operator):
    """Export a gravitational wave inspiral waveform as a CSV file.

    WHY: Provides a direct path from Kerr BH parameters to a LIGO-style
    waveform (3.5PN + NNLO spin-orbit) without leaving Blender.

    WHAT: Calls bridge.compute_gw_inspiral() and writes t, f, h+, hx, phase
    to a user-chosen CSV path.
    """

    bl_idname = "blackhole.export_gw_waveform"
    bl_label = "Export GW Waveform (CSV)"
    bl_description = "Compute and export GW inspiral waveform to a CSV file"
    bl_options = {'REGISTER'}

    filepath: bpy.props.StringProperty(
        name="Output CSV",
        description="Destination path for the GW waveform CSV",
        default="//gw_waveform.csv",
        subtype='FILE_PATH',
    )
    filter_glob: bpy.props.StringProperty(default="*.csv", options={'HIDDEN'})

    def execute(self, context):
        props = context.scene.blackhole

        try:
            waveform = bridge.compute_gw_inspiral(
                m1_msun=props.gw_m1_msun,
                m2_msun=props.gw_m2_msun,
                a1_star=props.gw_a1_star,
                a2_star=props.gw_a2_star,
                dist_mpc=props.gw_dist_mpc,
                inc_rad=math.radians(props.gw_inclination_deg),
                f_low_hz=props.gw_f_low,
                f_high_hz=props.gw_f_high,
                dt_sec=props.gw_dt,
            )
        except RuntimeError as exc:
            self.report({'ERROR'}, str(exc))
            return {'CANCELLED'}

        path = bpy.path.abspath(self.filepath)
        dir_path = os.path.dirname(path)
        if dir_path:
            os.makedirs(dir_path, exist_ok=True)

        with open(path, "w") as fh:
            fh.write("t_s,f_hz,h_plus,h_cross,phase_rad\n")
            for pt in waveform:
                fh.write(
                    f"{pt['t']:.9e},{pt['f']:.6f},"
                    f"{pt['h_plus']:.9e},{pt['h_cross']:.9e},{pt['phase']:.9f}\n"
                )

        self.report({'INFO'}, f"Exported {len(waveform)} GW points to {path}")
        return {'FINISHED'}

    def invoke(self, context, event):
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}


def _apply_as_world_background(context, img_name: str) -> None:
    """Set a Blender image as the scene's world environment texture.

    Creates a minimal World node tree:  Environment Texture -> Background -> Output.
    Reuses the existing world if already set up; updates the image reference otherwise.
    """
    scene = context.scene
    world = scene.world
    if world is None:
        world = bpy.data.worlds.new("BH_World")
        scene.world = world

    world.use_nodes = True
    nodes = world.node_tree.nodes
    links = world.node_tree.links

    # Find or create the Environment Texture node
    env_node = next(
        (n for n in nodes if n.type == 'TEX_ENVIRONMENT'), None
    )
    if env_node is None:
        nodes.clear()
        out_node = nodes.new('ShaderNodeOutputWorld')
        out_node.location = (400, 0)

        bg_node = nodes.new('ShaderNodeBackground')
        bg_node.location = (200, 0)
        bg_node.inputs['Strength'].default_value = 1.0

        env_node = nodes.new('ShaderNodeTexEnvironment')
        env_node.location = (0, 0)

        links.new(env_node.outputs['Color'], bg_node.inputs['Color'])
        links.new(bg_node.outputs['Background'], out_node.inputs['Surface'])

    if img_name in bpy.data.images:
        env_node.image = bpy.data.images[img_name]
