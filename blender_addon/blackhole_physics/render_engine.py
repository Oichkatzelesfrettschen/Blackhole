# render_engine.py -- Custom Blender RenderEngine wrapping the CUDA geodesic kernel.
#
# WHY: Eliminates the billboard approach. Blender's camera directly drives the
#      CUDA ray tracer, producing physically-correct Kerr geodesic images that
#      go through Blender's full compositor pipeline (bloom, lens distortion,
#      color grading, tonemapping).
#
# WHAT: BlackholeRenderEngine registered as 'BLACKHOLE_RT'. Implements render()
#       for final frames and view_draw() for viewport preview.
#
# HOW: ctypes calls to libblackhole_bridge.so -> bhb_cuda_render_raytraced.

import bpy
import ctypes as ct
import numpy as np
import gpu
from gpu_extras.batch import batch_for_shader

from . import bridge
from .camera_mapping import observer_params_from_blender_position


# ============================================================================
# CUDA kernel interface (mirrors the test scripts but as a reusable class)
# ============================================================================

class CUDARenderer:
    """Manages ray-traced dispatch through the public Blender bridge ABI."""

    def __init__(self):
        self._lib = None

    def _ensure_cuda(self):
        if self._lib is None:
            self._lib = bridge.get_lib()

    def render(self, params, w, h):
        """Launch kernel and return (h, w, 4) float32 numpy array."""
        self._ensure_cuda()
        host = np.zeros((h, w, 4), dtype=np.float32)
        if hasattr(self._lib, "bhb_cuda_render_raytraced_camera"):
            ret = self._lib.bhb_cuda_render_raytraced_camera(
                float(params["spin"]),
                float(params["observer_r"]),
                float(params["inclination_rad"]),
                float(params["fov_scale"]),
                w,
                h,
                host.ctypes.data_as(ct.POINTER(ct.c_float)),
            )
        else:
            ret = self._lib.bhb_cuda_render_raytraced(
                float(params["spin"]),
                float(params["observer_r"]),
                float(params["inclination_rad"]),
                w,
                h,
                host.ctypes.data_as(ct.POINTER(ct.c_float)),
            )
        if ret != 0:
            raise RuntimeError(f"Bridge ray-traced render failed: {ret}")
        return host

    def cleanup(self):
        self._lib = None


# Singleton renderer
_renderer = CUDARenderer()


def _blender_camera_to_params(scene, depsgraph):
    """Convert Blender camera + scene properties to bridge render parameters."""
    params = {
        "spin": 0.0,
        "observer_r": 15.0,
        "inclination_rad": 0.0,
        "fov_scale": 1.0,
    }

    # Black hole parameters from scene properties
    props = scene.blackhole
    a_star = props.spin

    params["spin"] = a_star

    # Camera: extract from Blender camera object
    camera_obj = scene.camera
    if camera_obj is None:
        params["observer_r"] = 15.0
        params["inclination_rad"] = 0.0
    else:
        mat = camera_obj.matrix_world
        pos = mat.translation
        observer_r, inclination_rad = observer_params_from_blender_position(
            float(pos.x),
            float(pos.y),
            float(pos.z),
        )
        params["observer_r"] = observer_r
        params["inclination_rad"] = inclination_rad
        camera_data = getattr(camera_obj, "data", None)
        if camera_data is not None and getattr(camera_data, "type", "") == "PERSP":
            sensor_width = max(float(getattr(camera_data, "sensor_width", 36.0)), 1.0e-6)
            focal_length = max(float(getattr(camera_data, "lens", 50.0)), 1.0e-6)
            params["fov_scale"] = sensor_width / (2.0 * focal_length)

    return params


# ============================================================================
# Blender Render Engine
# ============================================================================

class BlackholeRenderEngine(bpy.types.RenderEngine):
    bl_idname = 'BLACKHOLE_RT'
    bl_label = 'Blackhole Ray Tracer'
    bl_use_preview = False
    bl_use_postprocess = True  # enable compositor
    bl_use_gpu_context = False  # we manage CUDA ourselves

    def render(self, depsgraph):
        """Final frame render."""
        scene = depsgraph.scene
        w = scene.render.resolution_x
        h = scene.render.resolution_y
        scale = scene.render.resolution_percentage / 100.0
        w = int(w * scale)
        h = int(h * scale)

        self.update_stats("", "Blackhole: Preparing launch parameters")
        params = _blender_camera_to_params(scene, depsgraph)

        self.update_stats("", f"Blackhole: Tracing {w}x{h} via bridge ray tracer")

        try:
            rgba = _renderer.render(params, w, h)
        except Exception as e:
            self.report({'ERROR'}, str(e))
            return

        self.update_stats("", "Blackhole: Writing pixels")

        # Write to Blender render result
        result = self.begin_result(0, 0, w, h)
        layer = result.layers[0].passes["Combined"]

        # Blender 5.2: layer.rect = list of (r,g,b,a) native-float tuples, bottom-to-top.
        # CRITICAL: numpy float32 scalars are silently rejected by bpy_prop_array.
        # Convert via .tolist() which produces native Python floats all the way down.
        flipped = np.ascontiguousarray(np.flipud(rgba))
        # reshape to (N, 4) then .tolist() gives [[r,g,b,a], ...] with native floats
        pixel_lists = flipped.reshape(-1, 4).tolist()
        # tuple() each sublist (Blender requires tuples, not lists)
        layer.rect = [tuple(p) for p in pixel_lists]

        self.end_result(result)
        self.update_stats("", "Blackhole: Complete")

    def view_update(self, context, depsgraph):
        """Called when viewport data changes."""
        pass

    def view_draw(self, context, depsgraph):
        """Viewport preview: render at reduced resolution and display."""
        scene = depsgraph.scene
        region = context.region
        w = region.width // 2  # half res for viewport speed
        h = region.height // 2

        if w < 64 or h < 64:
            return

        try:
            params = _blender_camera_to_params(scene, depsgraph)
            rgba = _renderer.render(params, w, h)
        except Exception:
            return

        # The CUDA bridge already applies bloom + ACES + gamma. Keep the
        # viewport path display-referred instead of re-exposing and clipping it.
        rgba = np.clip(rgba, 0.0, 1.0)

        # Upload to GPU texture and draw
        pixels = np.flipud(rgba).flatten()
        pixel_buf = gpu.types.Buffer('FLOAT', len(pixels), pixels.tolist())
        texture = gpu.types.GPUTexture((w, h), format='RGBA32F', data=pixel_buf)

        shader = gpu.shader.from_builtin('IMAGE')
        batch = batch_for_shader(shader, 'TRI_FAN', {
            "pos": [(0, 0), (region.width, 0), (region.width, region.height), (0, region.height)],
            "texCoord": [(0, 0), (1, 0), (1, 1), (0, 1)],
        })
        shader.bind()
        shader.uniform_sampler("image", texture)
        batch.draw(shader)

        # Request continuous redraw for interactive navigation
        self.tag_redraw()


def get_panels():
    """Get compatible Blender panels for the render engine."""
    exclude = {'VIEWLAYER_PT_filter', 'VIEWLAYER_PT_layer_passes'}
    panels = []
    for panel_cls in bpy.types.Panel.__subclasses__():
        if hasattr(panel_cls, 'COMPAT_ENGINES') and 'BLENDER_RENDER' in panel_cls.COMPAT_ENGINES:
            if panel_cls.__name__ not in exclude:
                panels.append(panel_cls)
    return panels


def register():
    bpy.utils.register_class(BlackholeRenderEngine)
    for panel in get_panels():
        panel.COMPAT_ENGINES.add('BLACKHOLE_RT')


def unregister():
    for panel in get_panels():
        panel.COMPAT_ENGINES.discard('BLACKHOLE_RT')
    bpy.utils.unregister_class(BlackholeRenderEngine)
    _renderer.cleanup()
