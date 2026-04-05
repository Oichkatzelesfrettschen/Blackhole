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

    # Gravitational wave inspiral parameters
    gw_m1_msun: FloatProperty(
        name="M1 (Msun)", default=30.0, min=0.1, soft_max=1000.0,
        description="Primary compact object mass [solar masses]",
    )
    gw_m2_msun: FloatProperty(
        name="M2 (Msun)", default=25.0, min=0.1, soft_max=1000.0,
        description="Secondary compact object mass [solar masses]",
    )
    gw_a1_star: FloatProperty(
        name="a1*", default=0.0, min=0.0, max=0.9999, step=1, precision=4,
        description="Primary dimensionless spin [0, 1)",
    )
    gw_a2_star: FloatProperty(
        name="a2*", default=0.0, min=0.0, max=0.9999, step=1, precision=4,
        description="Secondary dimensionless spin [0, 1)",
    )
    gw_dist_mpc: FloatProperty(
        name="Distance (Mpc)", default=100.0, min=0.01, soft_max=10000.0,
        description="Luminosity distance [Mpc]",
    )
    gw_inclination_deg: FloatProperty(
        name="Inclination (deg)", default=0.0, min=0.0, max=90.0,
        description="Orbital inclination from line of sight [deg]",
    )
    gw_f_low: FloatProperty(
        name="f_low (Hz)", default=10.0, min=0.1, max=1000.0,
        description="Start frequency for waveform integration [Hz]",
    )
    gw_f_high: FloatProperty(
        name="f_high (Hz)", default=2000.0, min=10.0, max=8000.0,
        description="End frequency (typically near ISCO) [Hz]",
    )
    gw_dt: FloatProperty(
        name="dt (s)", default=1.0 / 4096, min=1e-5, max=0.1, precision=6,
        description="Time step for waveform output [s]",
    )

    # Stable Diffusion texture generation
    sd_model_path: StringProperty(
        name="SD Model",
        description=(
            "Path to a .gguf model file (used with the sd_cpp backend) or a "
            "HuggingFace model ID such as 'stabilityai/stable-diffusion-2-1' "
            "(used with the diffusers backend)"
        ),
        default="",
        subtype='FILE_PATH',
    )
    sd_target_slot: EnumProperty(
        name="Target Slot",
        description="Which Blender image / LUT slot receives the generated texture",
        items=[
            ("disk",       "Disk Emission",   "Replace 'BlackholeDiskTexture' (emission LUT, BhLutSlot 0)"),
            ("background", "Background",       "Replace the world environment texture (Galaxy / starfield)"),
        ],
        default="disk",
    )
    sd_backend: EnumProperty(
        name="Backend",
        description="Inference backend to use for SD generation",
        items=[
            ("auto",      "Auto",             "sd_cpp for .gguf paths, diffusers otherwise"),
            ("sd_cpp",    "sd.cpp (CUBLAS)",  "stable-diffusion.cpp subprocess -- zero CUDA conflict"),
            ("diffusers", "diffusers (HF)",   "python-diffusers in-process -- requires diffusers+torch in Blender Python"),
        ],
        default="auto",
    )
    sd_prompt_prefix: StringProperty(
        name="Prompt Prefix",
        description="Optional text prepended to the auto-generated physics prompt",
        default="",
    )
    sd_negative_prompt: StringProperty(
        name="Negative Prompt",
        description="SD negative prompt (leave empty for default)",
        default="",
    )
    sd_steps: IntProperty(
        name="Steps",
        description="Number of diffusion denoising steps (higher = better quality, slower)",
        default=25, min=5, max=150,
    )
    sd_seed: IntProperty(
        name="Seed",
        description="Random seed for reproducible generation (-1 for random)",
        default=42, min=-1, max=2147483647,
    )
    sd_guidance_scale: FloatProperty(
        name="Guidance Scale",
        description="CFG guidance scale (diffusers backend only; higher = closer to prompt)",
        default=7.5, min=1.0, max=20.0, step=5, precision=1,
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
        layout.operator("blackhole.apply_studio_quality", icon='SHADING_RENDERED')


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


class BH_PT_SDPanel(bpy.types.Panel):
    """Stable Diffusion texture generation panel.

    WHY: Exposes the SD backends and physics-conditioned prompt controls in the
    Blackhole sidebar so users can generate and iterate on astrophysical textures
    without leaving Blender.

    The generated image replaces the target Blender image in-place (same name), so
    existing material nodes and LUT bindings update automatically on the next render.
    """

    bl_label = "Stable Diffusion"
    bl_idname = "BH_PT_sd"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        from . import sd_textures

        # Model configuration
        col = layout.column(align=True)
        col.label(text="Model:", icon='FILE_CACHE')
        col.prop(props, "sd_model_path", text="")
        col.prop(props, "sd_backend")

        layout.separator()

        # Target
        layout.prop(props, "sd_target_slot")

        # Generation parameters
        box = layout.box()
        box.label(text="Generation Parameters:", icon='SETTINGS')
        col = box.column(align=True)
        col.prop(props, "sd_steps")
        col.prop(props, "sd_seed")
        col.prop(props, "sd_guidance_scale")

        # Prompt controls
        box2 = layout.box()
        box2.label(text="Prompt:", icon='TEXT')
        box2.prop(props, "sd_prompt_prefix", text="Prefix")
        box2.prop(props, "sd_negative_prompt", text="Negative")

        # Show the auto-generated prompt for inspection
        if props.sd_model_path.strip():
            try:
                preview = sd_textures.build_prompt(props)
                box2.label(text="Preview:", icon='VIEWZOOM')
                # Wrap long prompts over multiple label lines (Blender has no word wrap)
                _draw_wrapped_text(box2, preview, max_chars=48)
            except Exception:
                pass

        layout.separator()

        # Available backends status
        backends = sd_textures.available_backends()
        row = layout.row(align=True)
        row.label(
            text="sd.cpp: " + ("ready" if "sd_cpp" in backends else "not found"),
            icon='CHECKMARK' if "sd_cpp" in backends else 'X',
        )
        row.label(
            text="diffusers: " + ("ready" if "diffusers" in backends else "not found"),
            icon='CHECKMARK' if "diffusers" in backends else 'X',
        )

        layout.separator()
        layout.operator("blackhole.generate_sd_texture", icon='RENDER_STILL')
        layout.operator("blackhole.clear_sd_cache", icon='TRASH')


class BH_PT_GWPanel(bpy.types.Panel):
    """Gravitational wave inspiral waveform export."""

    bl_label = "Gravitational Waves"
    bl_idname = "BH_PT_gw"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Blackhole"
    bl_parent_id = "BH_PT_main"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        props = context.scene.blackhole

        box = layout.box()
        box.label(text="Binary Parameters:", icon='FORCE_HARMONIC')
        col = box.column(align=True)
        row = col.row(align=True)
        row.prop(props, "gw_m1_msun")
        row.prop(props, "gw_m2_msun")
        row = col.row(align=True)
        row.prop(props, "gw_a1_star")
        row.prop(props, "gw_a2_star")
        col.prop(props, "gw_dist_mpc")
        col.prop(props, "gw_inclination_deg")

        box2 = layout.box()
        box2.label(text="Waveform Parameters:", icon='FCURVE')
        col2 = box2.column(align=True)
        row2 = col2.row(align=True)
        row2.prop(props, "gw_f_low")
        row2.prop(props, "gw_f_high")
        col2.prop(props, "gw_dt")

        layout.operator("blackhole.export_gw_waveform", icon='EXPORT')


def _draw_wrapped_text(layout, text: str, max_chars: int = 48) -> None:
    """Draw long text wrapped across multiple label lines."""
    words = text.split()
    line = ""
    for word in words:
        candidate = f"{line} {word}".strip()
        if len(candidate) > max_chars and line:
            layout.label(text=line)
            line = word
        else:
            line = candidate
    if line:
        layout.label(text=line)
