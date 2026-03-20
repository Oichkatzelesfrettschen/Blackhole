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
# HOW: ctypes calls to libblackhole_bridge.so -> bh_launch_geodesic_kernel.

import bpy
import ctypes as ct
import numpy as np
import math
import gpu
from gpu_extras.batch import batch_for_shader
from mathutils import Matrix

from . import bridge


# ============================================================================
# CUDA kernel interface (mirrors the test scripts but as a reusable class)
# ============================================================================

class CUDARenderer:
    """Manages CUDA framebuffer allocation and kernel dispatch."""

    # BH_LaunchParams struct matching kernel_launch.h
    class BH_LaunchParams(ct.Structure):
        _fields_ = [
            ('rs', ct.c_float), ('spin', ct.c_float), ('isco', ct.c_float),
            ('step_size', ct.c_float), ('fov_scale', ct.c_float), ('max_dist', ct.c_float),
            ('cam_pos', ct.c_float * 3), ('cam_basis', ct.c_float * 9),
            ('max_steps', ct.c_int), ('width', ct.c_int), ('height', ct.c_int),
            ('adisk_enabled', ct.c_int), ('redshift_enabled', ct.c_int),
            ('kerr_enabled', ct.c_int), ('use_luts', ct.c_int),
            ('lut_radius_min', ct.c_float), ('lut_radius_max', ct.c_float),
            ('redshift_radius_min', ct.c_float), ('redshift_radius_max', ct.c_float),
            ('spectral_radius_min', ct.c_float), ('spectral_radius_max', ct.c_float),
            ('time_sec', ct.c_float), ('doppler_strength', ct.c_float),
            ('background_intensity', ct.c_float), ('background_enabled', ct.c_int),
        ]

    def __init__(self):
        self._cuda_rt = None
        self._lib = None
        self._d_fb = None
        self._fb_w = 0
        self._fb_h = 0

    def _ensure_cuda(self):
        if self._cuda_rt is None:
            self._cuda_rt = ct.CDLL("libcudart.so")
            self._cuda_rt.cudaMalloc.restype = ct.c_int
            self._cuda_rt.cudaMalloc.argtypes = [ct.POINTER(ct.c_void_p), ct.c_size_t]
            self._cuda_rt.cudaMemcpy.restype = ct.c_int
            self._cuda_rt.cudaFree.restype = ct.c_int
            self._cuda_rt.cudaDeviceSynchronize.restype = ct.c_int
            self._cuda_rt.cudaMemset.restype = ct.c_int
        if self._lib is None:
            self._lib = bridge.get_lib()
            self._lib.bh_launch_geodesic_kernel.restype = ct.c_int
            self._lib.bh_launch_geodesic_kernel.argtypes = [
                ct.c_void_p, ct.POINTER(self.BH_LaunchParams), ct.c_int, ct.c_void_p
            ]
            self._lib.bh_select_kernel_variant.restype = ct.c_int

    def _ensure_framebuffer(self, w, h):
        if self._d_fb is not None and self._fb_w == w and self._fb_h == h:
            return
        self._free_framebuffer()
        self._d_fb = ct.c_void_p()
        self._cuda_rt.cudaMalloc(ct.byref(self._d_fb), w * h * 16)
        self._fb_w = w
        self._fb_h = h

    def _free_framebuffer(self):
        if self._d_fb is not None and self._d_fb.value:
            self._cuda_rt.cudaFree(self._d_fb)
            self._d_fb = None

    def render(self, params, w, h):
        """Launch kernel and return (h, w, 4) float32 numpy array."""
        self._ensure_cuda()
        self._ensure_framebuffer(w, h)
        self._cuda_rt.cudaMemset(self._d_fb, 0, w * h * 16)

        params.width = w
        params.height = h

        variant = self._lib.bh_select_kernel_variant()
        ret = self._lib.bh_launch_geodesic_kernel(
            self._d_fb, ct.byref(params), variant, None
        )
        if ret != 0:
            raise RuntimeError(f"CUDA kernel launch failed: {ret}")

        self._cuda_rt.cudaDeviceSynchronize()

        host = (ct.c_float * (w * h * 4))()
        self._cuda_rt.cudaMemcpy(host, self._d_fb, w * h * 16, 2)  # D2H

        return np.array(host, dtype=np.float32).reshape(h, w, 4)

    def cleanup(self):
        self._free_framebuffer()


# Singleton renderer
_renderer = CUDARenderer()


def _blender_camera_to_params(scene, depsgraph):
    """Convert Blender camera + scene properties to BH_LaunchParams."""
    params = CUDARenderer.BH_LaunchParams()

    # Black hole parameters from scene properties
    props = scene.blackhole
    a_star = props.spin

    params.rs = 1.0
    params.spin = a_star

    # ISCO
    z1 = 1.0 + (1.0 - a_star**2)**(1/3) * ((1+a_star)**(1/3) + (1-a_star)**(1/3))
    z2 = math.sqrt(3 * a_star**2 + z1**2)
    isco_M = 3.0 + z2 - math.sqrt((3-z1)*(3+z1+2*z2))
    params.isco = isco_M * 0.5

    params.step_size = 0.08
    params.max_dist = 120.0
    params.max_steps = 600

    # Camera: extract from Blender camera object
    camera_obj = scene.camera
    if camera_obj is None:
        # Default fallback
        params.cam_pos[0] = 0
        params.cam_pos[1] = 0
        params.cam_pos[2] = 15.0
        for i in range(9):
            params.cam_basis[i] = 1.0 if i % 4 == 0 else 0.0
        params.fov_scale = 1.0
    else:
        # Camera world position
        mat = camera_obj.matrix_world
        pos = mat.translation
        params.cam_pos[0] = pos.x
        params.cam_pos[1] = pos.y
        params.cam_pos[2] = pos.z

        # Camera basis: Blender camera looks along -Z local axis
        # Extract right (X), up (Y), forward (-Z) from world matrix
        right = mat.col[0].xyz.normalized()
        up = mat.col[1].xyz.normalized()
        # The kernel expects the ANTI-forward (the direction the camera faces away from)
        # Blender camera -Z = look direction, so +Z = anti-forward
        anti_fwd = mat.col[2].xyz.normalized()

        # Column-major: col0=right, col1=up, col2=anti_fwd
        params.cam_basis[0] = right.x
        params.cam_basis[1] = right.y
        params.cam_basis[2] = right.z
        params.cam_basis[3] = up.x
        params.cam_basis[4] = up.y
        params.cam_basis[5] = up.z
        params.cam_basis[6] = anti_fwd.x
        params.cam_basis[7] = anti_fwd.y
        params.cam_basis[8] = anti_fwd.z

        # FOV scale from camera lens
        cam_data = camera_obj.data
        if cam_data.type == 'PERSP':
            # fov_scale maps FOV to NDC range
            # The kernel: u = (2*px/w - 1) * fov_scale * aspect
            # For a 50mm lens on 36mm sensor: hfov = 2*atan(18/50) = 39.6 deg
            # fov_scale = tan(hfov/2)
            sensor_w = cam_data.sensor_width  # mm
            focal = cam_data.lens  # mm
            params.fov_scale = sensor_w / (2.0 * focal)
        else:
            params.fov_scale = 1.0

    # Feature flags
    params.adisk_enabled = 1
    params.redshift_enabled = 1
    params.kerr_enabled = 1 if abs(a_star) > 1e-6 else 0
    params.use_luts = 0
    params.doppler_strength = 1.5
    params.background_enabled = 1
    params.background_intensity = 3.0
    params.time_sec = scene.frame_current / scene.render.fps

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
        # Faster for interactive use -- can be raised for production
        params.max_steps = min(params.max_steps, 400)
        params.step_size = max(params.step_size, 0.1)

        self.update_stats("", f"Blackhole: Tracing {w}x{h} ({params.max_steps} steps)")

        # Call bhb_cuda_render_raytraced directly via ctypes (bypasses bridge.py
        # prototype issues from the camelCase rename). This function runs:
        # geodesic kernel + bloom + ACES tonemap + CA + vignette + grain + gamma.
        try:
            import os
            lib = ct.CDLL('/usr/local/lib/libblackhole_bridge.so.1.0.0',
                          mode=os.RTLD_NOW | os.RTLD_GLOBAL)
            fn = lib.bhb_cuda_render_raytraced
            fn.restype = ct.c_int
            fn.argtypes = [ct.c_float, ct.c_float, ct.c_float,
                           ct.c_int, ct.c_int, ct.POINTER(ct.c_float)]

            buf = (ct.c_float * (w * h * 4))()
            cam_pos = np.array([params.cam_pos[0], params.cam_pos[1], params.cam_pos[2]])
            dist = float(np.linalg.norm(cam_pos))
            incl = float(np.arctan2(cam_pos[1], cam_pos[2])) if dist > 0 else 0.0

            ret = fn(ct.c_float(params.spin), ct.c_float(dist),
                     ct.c_float(incl), w, h, buf)
            if ret != 0:
                raise RuntimeError(f"CUDA render failed: {ret}")
            rgba = np.array(buf, dtype=np.float32).reshape(h, w, 4)
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
            rgba[:, :, :3] *= 10.0
        except Exception:
            return

        # Clamp for display
        rgba = np.clip(rgba, 0, 100)

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
