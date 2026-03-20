# panels.py -- Blender UI panels for Blackhole physics
#
# Sidebar panels in 3D Viewport > Blackhole tab.

import math
import bpy
from bpy.props import (
    FloatProperty, IntProperty, BoolProperty,
    EnumProperty, StringProperty,
)
from . import bridge


class BlackholeProperties(bpy.types.PropertyGroup):
    """Scene-level properties for the Blackhole addon."""

    # Black hole parameters
    spin: FloatProperty(
        name="Spin (a*)",
        description="Dimensionless Kerr spin parameter",
        default=0.9375, min=0.0, max=0.9999, step=1, precision=4,
    )
    mass_msun: FloatProperty(
        name="Mass (Msun)",
        description="Black hole mass in solar masses",
        default=6.5e9, min=1.0, soft_max=1e12,
    )
    inclination_deg: FloatProperty(
        name="Inclination (deg)",
        description="Observer inclination from spin axis",
        default=17.0, min=0.0, max=90.0,
    )
    observer_distance: FloatProperty(
        name="Observer Distance (r_g)",
        description="Observer distance in gravitational radii",
        default=500.0, min=10.0, soft_max=10000.0,
    )

    # Derived (read-only display)
    @property
    def inclination_rad(self):
        return math.radians(self.inclination_deg)

    # Accretion rate
    mdot_edd: FloatProperty(
        name="Mdot (Edd)",
        description="Accretion rate in Eddington units",
        default=0.1, min=0.001, max=10.0,
    )

    # Geodesic parameters
    geodesic_count: IntProperty(
        name="Ray Count", default=64, min=4, max=512,
    )
    geodesic_b_min: FloatProperty(
        name="b_min (r_g)", default=1.0, min=0.1,
    )
    geodesic_b_max: FloatProperty(
        name="b_max (r_g)", default=15.0, min=1.0,
    )
    geodesic_max_steps: IntProperty(
        name="Max Steps", default=2000, min=100, max=50000,
    )
    geodesic_step_size: FloatProperty(
        name="Step Size", default=0.05, min=0.001, max=1.0,
    )

    # Disk parameters
    disk_r_out: FloatProperty(
        name="Outer Radius (r_g)", default=100.0, min=10.0, soft_max=1000.0,
    )
    disk_radial_res: IntProperty(
        name="Radial Resolution", default=64, min=4, max=512,
    )
    disk_azimuthal_res: IntProperty(
        name="Azimuthal Resolution", default=128, min=8, max=1024,
    )

    # Horizon mesh resolution
    horizon_theta_res: IntProperty(
        name="Theta Resolution", default=32, min=8, max=256,
    )
    horizon_phi_res: IntProperty(
        name="Phi Resolution", default=64, min=8, max=512,
    )

    # Texture parameters
    texture_width: IntProperty(
        name="Width", default=1024, min=64, max=8192,
    )
    texture_height: IntProperty(
        name="Height", default=1024, min=64, max=8192,
    )

    # CUDA preference
    use_cuda: BoolProperty(
        name="Use CUDA", default=True,
        description="Use GPU-accelerated paths when available",
    )


class BH_PT_MainPanel(bpy.types.Panel):
    bl_label = "Blackhole Physics"
    bl_idname = "BH_PT_main"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"

    def draw(self, context):
        layout = self.layout

        if not bridge.is_loaded():
            layout.label(text="Library not loaded", icon='ERROR')
            layout.operator("blackhole.load_library", icon='FILE_REFRESH')
            return

        lib = bridge.get_lib()
        row = layout.row()
        row.label(text=f"v{lib.bhb_version_major()}.{lib.bhb_version_minor()}", icon='PHYSICS')
        if lib.bhb_has_cuda():
            row.label(text="CUDA", icon='GPU')
        if lib.bhb_has_boost():
            row.label(text="Boost", icon='LIBRARY_DATA_DIRECT')

        # Render engine info
        engine = context.scene.render.engine
        layout.label(text=f"Render: {engine}", icon='SCENE')


class BH_PT_MetricPanel(bpy.types.Panel):
    bl_label = "Kerr Metric"
    bl_idname = "BH_PT_metric"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        layout.prop(props, "spin")
        layout.prop(props, "mass_msun")
        layout.prop(props, "inclination_deg")
        layout.prop(props, "observer_distance")
        layout.prop(props, "mdot_edd")

        if bridge.is_loaded():
            lib = bridge.get_lib()
            a = props.spin

            box = layout.box()
            box.label(text="Derived Quantities:", icon='INFO')
            col = box.column(align=True)
            col.label(text=f"r+ = {lib.bhb_kerr_outer_horizon(a):.4f} M")
            col.label(text=f"r- = {lib.bhb_kerr_inner_horizon(a):.4f} M")
            col.label(text=f"ISCO = {lib.bhb_kerr_isco(a, 1):.4f} M")
            col.label(text=f"Photon orbit = {lib.bhb_kerr_photon_orbit_prograde(a):.4f} M")
            col.label(text=f"Efficiency = {lib.bhb_nt_radiative_efficiency(a)*100:.2f}%")


class BH_PT_GeodesicsPanel(bpy.types.Panel):
    bl_label = "Geodesics"
    bl_idname = "BH_PT_geodesics"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        layout.prop(props, "geodesic_count")
        row = layout.row(align=True)
        row.prop(props, "geodesic_b_min")
        row.prop(props, "geodesic_b_max")
        layout.prop(props, "geodesic_max_steps")
        layout.prop(props, "geodesic_step_size")

        layout.operator("blackhole.generate_geodesics", icon='CURVE_BEZCURVE')


class BH_PT_DiskPanel(bpy.types.Panel):
    bl_label = "Accretion Disk"
    bl_idname = "BH_PT_disk"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        layout.prop(props, "disk_r_out")
        row = layout.row(align=True)
        row.prop(props, "disk_radial_res")
        row.prop(props, "disk_azimuthal_res")

        layout.operator("blackhole.generate_disk", icon='MESH_TORUS')

        layout.separator()
        layout.label(text="Structures:")
        row = layout.row(align=True)
        row.prop(props, "horizon_theta_res")
        row.prop(props, "horizon_phi_res")
        row = layout.row(align=True)
        row.operator("blackhole.generate_horizon", icon='SHADING_SOLID')
        row.operator("blackhole.generate_ergosphere", icon='SHADING_WIRE')


class BH_PT_TexturesPanel(bpy.types.Panel):
    bl_label = "Textures"
    bl_idname = "BH_PT_textures"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        row = layout.row(align=True)
        row.prop(props, "texture_width")
        row.prop(props, "texture_height")

        layout.operator("blackhole.render_lensing_map", icon='IMAGE_DATA')
        layout.operator("blackhole.render_disk_texture", icon='TEXTURE')
        layout.operator("blackhole.setup_octane_materials", icon='MATERIAL')


class BH_PT_PresetsPanel(bpy.types.Panel):
    bl_label = "EHT Presets"
    bl_idname = "BH_PT_presets"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        row = layout.row(align=True)
        row.operator("blackhole.preset_m87", icon='WORLD')
        row.operator("blackhole.preset_sgra", icon='WORLD')

        layout.separator()
        layout.operator("blackhole.build_assets", icon='ASSET_MANAGER')
