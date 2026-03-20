# operators.py -- Blender operators for Blackhole physics
#
# Each operator calls into the bridge and creates/modifies Blender objects.

import bpy
import bmesh
import numpy as np
from mathutils import Vector

from . import bridge


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


class BH_OT_BuildAssets(bpy.types.Operator):
    bl_idname = "blackhole.build_assets"
    bl_label = "Build Asset Library"
    bl_description = "Create browsable assets for the extended asset browser (presets, materials, node groups)"

    def execute(self, context):
        from . import assets
        assets.build_all_assets()
        self.report({'INFO'}, "Blackhole asset library built")
        return {'FINISHED'}
