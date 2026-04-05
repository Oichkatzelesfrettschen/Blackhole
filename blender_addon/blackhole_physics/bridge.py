# bridge.py -- ctypes bindings to libblackhole_bridge.so
#
# Loads the shared library and exposes all bhb_* functions with proper
# argument/return types for safe calling from Blender Python.

import ctypes
import ctypes.util
import os
import sys
import numpy as np
from pathlib import Path

_lib = None
_lib_path = None


class BHB_SourceParams(ctypes.Structure):
    _fields_ = [
        ("name", ctypes.c_char * 64),
        ("mass_msun", ctypes.c_double),
        ("spin", ctypes.c_double),
        ("distance_cm", ctypes.c_double),
        ("inclination_deg", ctypes.c_double),
        ("freq_hz", ctypes.c_double),
        ("r_g_cm", ctypes.c_double),
        ("shadow_uas", ctypes.c_double),
    ]


class BHB_DiskParams(ctypes.Structure):
    _fields_ = [
        ("a_star", ctypes.c_double),
        ("mass_msun", ctypes.c_double),
        ("mdot_edd", ctypes.c_double),
        ("r_out_rg", ctypes.c_double),
        ("inclination_rad", ctypes.c_double),
    ]


def _find_library():
    """Search for libblackhole_bridge.so in common locations."""
    candidates = []

    addon_dir = Path(__file__).parent
    repo_root = None
    for parent in addon_dir.parents:
        if (parent / "CMakeLists.txt").exists() and (parent / "src" / "blender_bridge").exists():
            repo_root = parent
            break

    if repo_root is not None:
        candidates.extend([
            repo_root / "build" / "Release" / "src" / "blender_bridge" / "libblackhole_bridge.so",
            repo_root / "build" / "src" / "blender_bridge" / "libblackhole_bridge.so",
            repo_root / "build" / "BlenderBridge" / "Release" / "src" / "blender_bridge" / "libblackhole_bridge.so",
            repo_root / "build" / "FullDev" / "RelWithDebInfo" / "src" / "blender_bridge" / "libblackhole_bridge.so",
        ])

    # System paths
    candidates.append(Path("/usr/local/lib/libblackhole_bridge.so"))
    candidates.append(Path("/usr/lib/libblackhole_bridge.so"))

    # Environment override
    env_path = os.environ.get("BLACKHOLE_BRIDGE_LIB")
    if env_path:
        candidates.insert(0, Path(env_path))

    for p in candidates:
        if p.exists():
            return str(p)

    # Last resort: ctypes search
    found = ctypes.util.find_library("blackhole_bridge")
    return found


def _setup_prototypes(lib):
    """Declare argument and return types for all bridge functions."""

    # Version / capability
    lib.bhb_version_major.restype = ctypes.c_int
    lib.bhb_version_major.argtypes = []
    lib.bhb_version_minor.restype = ctypes.c_int
    lib.bhb_version_minor.argtypes = []
    lib.bhb_has_cuda.restype = ctypes.c_int
    lib.bhb_has_cuda.argtypes = []
    lib.bhb_has_boost.restype = ctypes.c_int
    lib.bhb_has_boost.argtypes = []
    lib.bhb_sizeof_source_params.restype = ctypes.c_int
    lib.bhb_sizeof_source_params.argtypes = []
    lib.bhb_sizeof_disk_params.restype = ctypes.c_int
    lib.bhb_sizeof_disk_params.argtypes = []

    # Source presets
    lib.bhb_preset_m87.restype = None
    lib.bhb_preset_m87.argtypes = [ctypes.POINTER(BHB_SourceParams)]
    lib.bhb_preset_sgra.restype = None
    lib.bhb_preset_sgra.argtypes = [ctypes.POINTER(BHB_SourceParams)]

    # Kerr metric
    for fn_name in ["bhb_kerr_outer_horizon", "bhb_kerr_inner_horizon"]:
        fn = getattr(lib, fn_name)
        fn.restype = ctypes.c_double
        fn.argtypes = [ctypes.c_double]

    lib.bhb_kerr_ergosphere.restype = ctypes.c_double
    lib.bhb_kerr_ergosphere.argtypes = [ctypes.c_double, ctypes.c_double]

    lib.bhb_kerr_isco.restype = ctypes.c_double
    lib.bhb_kerr_isco.argtypes = [ctypes.c_double, ctypes.c_int]

    for fn_name in ["bhb_kerr_photon_orbit_prograde", "bhb_kerr_photon_orbit_retrograde"]:
        fn = getattr(lib, fn_name)
        fn.restype = ctypes.c_double
        fn.argtypes = [ctypes.c_double]

    lib.bhb_kerr_sigma.restype = ctypes.c_double
    lib.bhb_kerr_sigma.argtypes = [ctypes.c_double, ctypes.c_double, ctypes.c_double]
    lib.bhb_kerr_delta.restype = ctypes.c_double
    lib.bhb_kerr_delta.argtypes = [ctypes.c_double, ctypes.c_double]

    # Geodesic tracing
    lib.bhb_trace_geodesics_equatorial.restype = ctypes.c_int
    lib.bhb_trace_geodesics_equatorial.argtypes = [
        ctypes.c_double, ctypes.c_double,
        ctypes.c_double, ctypes.c_double,
        ctypes.c_int, ctypes.c_int, ctypes.c_double,
        ctypes.POINTER(ctypes.c_float),
        ctypes.POINTER(ctypes.c_int),
    ]

    lib.bhb_trace_geodesics_image_plane.restype = ctypes.c_int
    lib.bhb_trace_geodesics_image_plane.argtypes = [
        ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.c_double, ctypes.c_double, ctypes.c_int,
        ctypes.c_double, ctypes.c_double, ctypes.c_int,
        ctypes.c_int, ctypes.c_double,
        ctypes.POINTER(ctypes.c_float),
        ctypes.POINTER(ctypes.c_int),
    ]

    # Disk mesh
    lib.bhb_generate_disk_mesh.restype = ctypes.c_int
    lib.bhb_generate_disk_mesh.argtypes = [
        ctypes.POINTER(BHB_DiskParams),
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),  # positions
        ctypes.POINTER(ctypes.c_float),  # normals
        ctypes.POINTER(ctypes.c_float),  # temperatures
        ctypes.POINTER(ctypes.c_float),  # uvs
        ctypes.POINTER(ctypes.c_int),    # indices
        ctypes.POINTER(ctypes.c_int),    # vertex count
        ctypes.POINTER(ctypes.c_int),    # index count
    ]

    # Novikov-Thorne
    lib.bhb_nt_radiative_efficiency.restype = ctypes.c_double
    lib.bhb_nt_radiative_efficiency.argtypes = [ctypes.c_double]
    lib.bhb_nt_isco_radius.restype = ctypes.c_double
    lib.bhb_nt_isco_radius.argtypes = [ctypes.c_double]
    lib.bhb_nt_temperature_profile.restype = ctypes.c_int
    lib.bhb_nt_temperature_profile.argtypes = [
        ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.POINTER(ctypes.c_double), ctypes.c_int,
        ctypes.POINTER(ctypes.c_double),
        ctypes.POINTER(ctypes.c_double),
    ]

    # Doppler
    lib.bhb_lorentz_factor.restype = ctypes.c_double
    lib.bhb_lorentz_factor.argtypes = [ctypes.c_double]
    lib.bhb_doppler_factor.restype = ctypes.c_double
    lib.bhb_doppler_factor.argtypes = [ctypes.c_double, ctypes.c_double]
    lib.bhb_beaming_flux.restype = ctypes.c_double
    lib.bhb_beaming_flux.argtypes = [ctypes.c_double, ctypes.c_double]

    # Synchrotron
    for fn_name in ["bhb_synchrotron_gyrofreq", "bhb_synchrotron_critical_freq",
                     "bhb_synchrotron_power", "bhb_synchrotron_cooling_time"]:
        fn = getattr(lib, fn_name)
        fn.restype = ctypes.c_double
        fn.argtypes = [ctypes.c_double, ctypes.c_double]

    # Texture generation
    lib.bhb_render_lensing_map.restype = ctypes.c_int
    lib.bhb_render_lensing_map.argtypes = [
        ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),
    ]

    lib.bhb_render_disk_texture.restype = ctypes.c_int
    lib.bhb_render_disk_texture.argtypes = [
        ctypes.POINTER(BHB_DiskParams),
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),
    ]

    # Horizon / ergosphere meshes
    for fn_name in ["bhb_generate_horizon_mesh", "bhb_generate_ergosphere_mesh"]:
        fn = getattr(lib, fn_name)
        fn.restype = ctypes.c_int
        fn.argtypes = [
            ctypes.c_double, ctypes.c_int, ctypes.c_int,
            ctypes.POINTER(ctypes.c_float),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
        ]

    # CUDA paths
    lib.bhb_cuda_trace_geodesics.restype = ctypes.c_int
    lib.bhb_cuda_trace_geodesics.argtypes = [
        ctypes.c_double, ctypes.c_double, ctypes.c_double,
        ctypes.c_double, ctypes.c_double, ctypes.c_int,
        ctypes.c_double, ctypes.c_double, ctypes.c_int,
        ctypes.c_int, ctypes.c_double,
        ctypes.POINTER(ctypes.c_float),
        ctypes.POINTER(ctypes.c_int),
    ]
    lib.bhb_cuda_render_lensing_map.restype = ctypes.c_int
    lib.bhb_cuda_render_lensing_map.argtypes = [
        ctypes.c_float, ctypes.c_float, ctypes.c_float,
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),
    ]
    lib.bhb_cuda_render_disk_texture.restype = ctypes.c_int
    lib.bhb_cuda_render_disk_texture.argtypes = [
        ctypes.c_float, ctypes.c_float, ctypes.c_float,
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),
    ]
    lib.bhb_cuda_render_raytraced.restype = ctypes.c_int
    lib.bhb_cuda_render_raytraced.argtypes = [
        ctypes.c_float, ctypes.c_float, ctypes.c_float,
        ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_float),
    ]
    if hasattr(lib, "bhb_cuda_render_raytraced_camera"):
        lib.bhb_cuda_render_raytraced_camera.restype = ctypes.c_int
        lib.bhb_cuda_render_raytraced_camera.argtypes = [
            ctypes.c_float, ctypes.c_float, ctypes.c_float, ctypes.c_float,
            ctypes.c_int, ctypes.c_int,
            ctypes.POINTER(ctypes.c_float),
        ]

    # Gravitational wave inspiral waveform
    lib.bhb_gw_inspiral.restype = ctypes.c_int
    lib.bhb_gw_inspiral.argtypes = [
        ctypes.c_double, ctypes.c_double,  # m1_msun, m2_msun
        ctypes.c_double, ctypes.c_double,  # a1_star, a2_star
        ctypes.c_double, ctypes.c_double,  # dist_mpc, inc_rad
        ctypes.c_double, ctypes.c_double,  # f_low_hz, f_high_hz
        ctypes.c_double,                   # dt_sec
        ctypes.POINTER(ctypes.c_double),   # out_buf (maxPoints * 5 doubles)
        ctypes.c_int,                      # max_points
    ]


def try_load_library():
    """Attempt to load libblackhole_bridge.so. Non-fatal if not found."""
    global _lib, _lib_path
    path = _find_library()
    if path is None:
        print("[Blackhole] libblackhole_bridge.so not found. Physics features disabled.")
        print("[Blackhole] Set BLACKHOLE_BRIDGE_LIB env var or build with -DENABLE_BLENDER_BRIDGE=ON")
        return False
    try:
        _lib = ctypes.CDLL(path)
        _setup_prototypes(_lib)
        _lib_path = path
        v = f"{_lib.bhb_version_major()}.{_lib.bhb_version_minor()}"
        cuda = "yes" if _lib.bhb_has_cuda() else "no"
        boost = "yes" if _lib.bhb_has_boost() else "no"
        source_size = ctypes.sizeof(BHB_SourceParams)
        disk_size = ctypes.sizeof(BHB_DiskParams)
        c_source_size = _lib.bhb_sizeof_source_params()
        c_disk_size = _lib.bhb_sizeof_disk_params()
        if c_source_size != source_size:
            raise RuntimeError(
                f"BHB_SourceParams layout mismatch: python={source_size} c={c_source_size}"
            )
        if c_disk_size != disk_size:
            raise RuntimeError(
                f"BHB_DiskParams layout mismatch: python={disk_size} c={c_disk_size}"
            )
        print(f"[Blackhole] Loaded {path} v{v} (CUDA: {cuda}, Boost: {boost})")
        return True
    except OSError as e:
        print(f"[Blackhole] Failed to load {path}: {e}")
        _lib = None
        return False
    except RuntimeError as e:
        print(f"[Blackhole] ABI validation failed for {path}: {e}")
        _lib = None
        _lib_path = None
        return False


def unload_library():
    global _lib, _lib_path
    _lib = None
    _lib_path = None


def is_loaded():
    return _lib is not None


def get_lib():
    if _lib is None:
        raise RuntimeError("libblackhole_bridge.so not loaded. Use Load Library operator first.")
    return _lib


def get_library_path():
    return _lib_path


def get_version_tuple():
    lib = get_lib()
    return (lib.bhb_version_major(), lib.bhb_version_minor())


def get_capabilities():
    lib = get_lib()
    return {
        "cuda": bool(lib.bhb_has_cuda()),
        "boost": bool(lib.bhb_has_boost()),
        "source_params_size": lib.bhb_sizeof_source_params(),
        "disk_params_size": lib.bhb_sizeof_disk_params(),
    }


# ============================================================================
# High-level Python wrappers
# ============================================================================

def get_preset_m87():
    lib = get_lib()
    params = BHB_SourceParams()
    lib.bhb_preset_m87(ctypes.byref(params))
    return params


def get_preset_sgra():
    lib = get_lib()
    params = BHB_SourceParams()
    lib.bhb_preset_sgra(ctypes.byref(params))
    return params


def trace_geodesics_equatorial(a_star, observer_r, b_min, b_max,
                                n_rays=64, max_steps=2000, step_size=0.05):
    lib = get_lib()
    total_floats = n_rays * max_steps * 3
    xyz_buf = (ctypes.c_float * total_floats)()
    counts_buf = (ctypes.c_int * n_rays)()

    ret = lib.bhb_trace_geodesics_equatorial(
        a_star, observer_r, b_min, b_max,
        n_rays, max_steps, step_size,
        xyz_buf, counts_buf,
    )
    if ret != 0:
        raise RuntimeError(f"Geodesic trace failed: {ret}")

    # Convert to list of numpy arrays
    rays = []
    for i in range(n_rays):
        n = counts_buf[i]
        offset = i * max_steps * 3
        arr = np.array(xyz_buf[offset:offset + n * 3], dtype=np.float32).reshape(-1, 3)
        rays.append(arr)
    return rays


def generate_disk_mesh(a_star, mass_msun, mdot_edd=0.1, r_out_rg=100.0,
                       inclination_rad=0.3, n_radial=64, n_azimuthal=128):
    lib = get_lib()
    params = BHB_DiskParams(
        a_star=a_star, mass_msun=mass_msun, mdot_edd=mdot_edd,
        r_out_rg=r_out_rg, inclination_rad=inclination_rad,
    )

    n_verts = n_radial * n_azimuthal
    n_tris = 2 * (n_radial - 1) * n_azimuthal

    pos_buf = (ctypes.c_float * (n_verts * 3))()
    norm_buf = (ctypes.c_float * (n_verts * 3))()
    temp_buf = (ctypes.c_float * n_verts)()
    uv_buf = (ctypes.c_float * (n_verts * 2))()
    idx_buf = (ctypes.c_int * (n_tris * 3))()
    vert_count = ctypes.c_int(0)
    idx_count = ctypes.c_int(0)

    ret = lib.bhb_generate_disk_mesh(
        ctypes.byref(params), n_radial, n_azimuthal,
        pos_buf, norm_buf, temp_buf, uv_buf, idx_buf,
        ctypes.byref(vert_count), ctypes.byref(idx_count),
    )
    if ret != 0:
        raise RuntimeError(f"Disk mesh generation failed: {ret}")

    nv = vert_count.value
    ni = idx_count.value
    positions = np.array(pos_buf[:nv * 3], dtype=np.float32).reshape(-1, 3)
    normals = np.array(norm_buf[:nv * 3], dtype=np.float32).reshape(-1, 3)
    temperatures = np.array(temp_buf[:nv], dtype=np.float32)
    uvs = np.array(uv_buf[:nv * 2], dtype=np.float32).reshape(-1, 2)
    indices = np.array(idx_buf[:ni], dtype=np.int32).reshape(-1, 3)

    return positions, normals, temperatures, uvs, indices


def generate_horizon_mesh(a_star, n_theta=32, n_phi=64):
    lib = get_lib()
    n_verts = n_theta * n_phi
    n_tris = 2 * (n_theta - 1) * n_phi

    pos_buf = (ctypes.c_float * (n_verts * 3))()
    idx_buf = (ctypes.c_int * (n_tris * 3))()
    vert_count = ctypes.c_int(0)
    idx_count = ctypes.c_int(0)

    ret = lib.bhb_generate_horizon_mesh(
        a_star, n_theta, n_phi,
        pos_buf, idx_buf,
        ctypes.byref(vert_count), ctypes.byref(idx_count),
    )
    if ret != 0:
        raise RuntimeError(f"Horizon mesh generation failed: {ret}")

    nv = vert_count.value
    ni = idx_count.value
    return (
        np.array(pos_buf[:nv * 3], dtype=np.float32).reshape(-1, 3),
        np.array(idx_buf[:ni], dtype=np.int32).reshape(-1, 3),
    )


def generate_ergosphere_mesh(a_star, n_theta=32, n_phi=64):
    lib = get_lib()
    n_verts = n_theta * n_phi
    n_tris = 2 * (n_theta - 1) * n_phi

    pos_buf = (ctypes.c_float * (n_verts * 3))()
    idx_buf = (ctypes.c_int * (n_tris * 3))()
    vert_count = ctypes.c_int(0)
    idx_count = ctypes.c_int(0)

    ret = lib.bhb_generate_ergosphere_mesh(
        a_star, n_theta, n_phi,
        pos_buf, idx_buf,
        ctypes.byref(vert_count), ctypes.byref(idx_count),
    )
    if ret != 0:
        raise RuntimeError(f"Ergosphere mesh generation failed: {ret}")

    nv = vert_count.value
    ni = idx_count.value
    return (
        np.array(pos_buf[:nv * 3], dtype=np.float32).reshape(-1, 3),
        np.array(idx_buf[:ni], dtype=np.int32).reshape(-1, 3),
    )


def render_lensing_map(a_star, observer_r, inclination_rad, width=1024, height=1024):
    lib = get_lib()
    buf = (ctypes.c_float * (width * height * 4))()
    ret = lib.bhb_render_lensing_map(
        a_star, observer_r, inclination_rad, width, height, buf,
    )
    if ret != 0:
        raise RuntimeError(f"Lensing map render failed: {ret}")
    return np.array(buf, dtype=np.float32).reshape(height, width, 4)


def render_disk_texture(a_star, mass_msun, mdot_edd=0.1, r_out_rg=100.0,
                        inclination_rad=0.3, width=1024, height=256):
    lib = get_lib()
    params = BHB_DiskParams(
        a_star=a_star, mass_msun=mass_msun, mdot_edd=mdot_edd,
        r_out_rg=r_out_rg, inclination_rad=inclination_rad,
    )
    buf = (ctypes.c_float * (width * height * 4))()
    ret = lib.bhb_render_disk_texture(ctypes.byref(params), width, height, buf)
    if ret != 0:
        raise RuntimeError(f"Disk texture render failed: {ret}")
    return np.array(buf, dtype=np.float32).reshape(height, width, 4)


def compute_gw_inspiral(m1_msun, m2_msun, a1_star=0.0, a2_star=0.0,
                        dist_mpc=100.0, inc_rad=0.0,
                        f_low_hz=10.0, f_high_hz=2000.0, dt_sec=1.0 / 4096):
    """Compute GW inspiral waveform using 3.5PN + NNLO spin-orbit formalism.

    Returns a list of dicts, one per time step, with keys:
        t       -- time [s]
        f       -- GW frequency [Hz]
        h_plus  -- plus polarization amplitude
        h_cross -- cross polarization amplitude
        phase   -- orbital phase [rad]
    """
    lib = get_lib()
    # Allocate conservatively: (f_high - f_low) / (f_low * 1e-4) is the
    # maximum number of frequency steps; add headroom for the time-domain buffer.
    max_points = max(4096, int((f_high_hz - f_low_hz) / max(f_low_hz * 1e-4, 1e-10)) + 4096)
    buf = (ctypes.c_double * (max_points * 5))()

    n = lib.bhb_gw_inspiral(
        m1_msun, m2_msun, a1_star, a2_star,
        dist_mpc, inc_rad, f_low_hz, f_high_hz, dt_sec,
        buf, max_points,
    )
    if n < 0:
        raise RuntimeError(f"bhb_gw_inspiral failed (ret={n}): check argument ranges")

    result = []
    for i in range(n):
        base = i * 5
        result.append({
            "t":       buf[base],
            "f":       buf[base + 1],
            "h_plus":  buf[base + 2],
            "h_cross": buf[base + 3],
            "phase":   buf[base + 4],
        })
    return result
