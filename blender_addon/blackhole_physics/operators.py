# operators.py -- Blender operators for Blackhole physics
#
# Each operator calls into the bridge and creates/modifies Blender objects.

import math
import os

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
    img.update()
    img.pack()
    return img


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

        _image_from_array("BlackholeLensingMap", data, w, h)
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
      - diffusers: uses python-diffusers in-process; pipeline is cached.
    Auto mode chooses sd_cpp for .gguf paths, diffusers otherwise.
    """

    bl_idname = "blackhole.generate_sd_texture"
    bl_label = "Generate SD Texture"
    bl_description = (
        "Generate an astrophysics texture with Stable Diffusion and apply it "
        "to the selected slot (disk emission or background)"
    )
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        props = context.scene.blackhole

        self.report({'INFO'}, "Generating SD texture -- this may take 10-60 s ...")

        try:
            data = sd_textures.generate(props)
        except RuntimeError as exc:
            self.report({'ERROR'}, str(exc))
            return {'CANCELLED'}
        except Exception as exc:
            self.report({'ERROR'}, f"SD generation error: {exc}")
            return {'CANCELLED'}

        w = props.texture_width
        h = props.texture_height
        slot = props.sd_target_slot

        if slot == "disk":
            img_name = "BlackholeDiskTexture"
            _image_from_array(img_name, data, w, h)
            self.report(
                {'INFO'},
                f"SD disk texture generated ({w}x{h}). "
                f"'BlackholeDiskTexture' updated -- render the disk to see it."
            )
        else:  # background
            img_name = "BH_SD_Background"
            _image_from_array(img_name, data, w, h)
            _apply_as_world_background(context, img_name)
            self.report(
                {'INFO'},
                f"SD background generated ({w}x{h}). World environment updated."
            )

        return {'FINISHED'}

    def invoke(self, context, event):
        props = context.scene.blackhole
        if not props.sd_model_path.strip():
            self.report(
                {'ERROR'},
                "Set 'SD Model' (a .gguf path or HuggingFace model ID) before generating."
            )
            return {'CANCELLED'}
        return self.execute(context)


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
