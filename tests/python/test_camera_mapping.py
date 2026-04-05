from __future__ import annotations

import importlib.util
import math
from pathlib import Path


_MODULE_PATH = (
    Path("/home/eirikr/Github/Blackhole")
    / "blender"
    / "addon"
    / "blackhole_physics"
    / "camera_mapping.py"
)
_SPEC = importlib.util.spec_from_file_location("camera_mapping", _MODULE_PATH)
assert _SPEC is not None and _SPEC.loader is not None
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)  # type: ignore[union-attr]

blender_position_for_observer = _MODULE.blender_position_for_observer
observer_params_from_blender_position = _MODULE.observer_params_from_blender_position
camera_position_from_yaw_pitch = _MODULE.camera_position_from_yaw_pitch
build_camera_basis = _MODULE.build_camera_basis
desktop_view_camera = _MODULE.desktop_view_camera


def test_round_trip_preserves_observer_radius_and_inclination() -> None:
    observer_r = 32.0
    inclination_rad = math.radians(17.0)
    x, y, z = blender_position_for_observer(observer_r, inclination_rad)
    mapped_r, mapped_inclination = observer_params_from_blender_position(x, y, z)
    assert math.isclose(mapped_r, observer_r, rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert math.isclose(
        mapped_inclination,
        inclination_rad,
        rel_tol=1.0e-9,
        abs_tol=1.0e-9,
    )


def test_upper_and_lower_hemispheres_collapse_to_same_inclination() -> None:
    observer_r = 24.0
    inclination_rad = math.radians(34.0)
    x, y, z = blender_position_for_observer(observer_r, inclination_rad)
    upper = observer_params_from_blender_position(x, y, z)
    lower = observer_params_from_blender_position(x, y, -z)
    assert math.isclose(upper[0], lower[0], rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert math.isclose(upper[1], lower[1], rel_tol=1.0e-9, abs_tol=1.0e-9)


def test_zero_position_honors_minimum_distance_floor() -> None:
    mapped_r, mapped_inclination = observer_params_from_blender_position(0.0, 0.0, 0.0)
    assert math.isclose(mapped_r, 2.5, rel_tol=0.0, abs_tol=1.0e-12)
    assert math.isclose(mapped_inclination, 0.0, rel_tol=0.0, abs_tol=1.0e-12)


def test_camera_position_from_yaw_pitch_matches_desktop_axes() -> None:
    assert camera_position_from_yaw_pitch(0.0, 0.0, 10.0) == (0.0, 0.0, 10.0)
    x, y, z = camera_position_from_yaw_pitch(90.0, 0.0, 10.0)
    assert math.isclose(x, 10.0, rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert math.isclose(y, 0.0, rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert math.isclose(z, 0.0, rel_tol=1.0e-9, abs_tol=1.0e-9)


def test_build_camera_basis_points_forward_to_origin() -> None:
    basis = build_camera_basis((0.0, 0.0, 10.0), (0.0, 0.0, 0.0), 0.0)
    right = basis[0:3]
    up = basis[3:6]
    forward = basis[6:9]
    assert all(math.isfinite(value) for value in basis)
    assert math.isclose(forward[0], 0.0, rel_tol=0.0, abs_tol=1.0e-9)
    assert math.isclose(forward[1], 0.0, rel_tol=0.0, abs_tol=1.0e-9)
    assert math.isclose(forward[2], -1.0, rel_tol=0.0, abs_tol=1.0e-9)
    assert math.isclose(sum(component * component for component in right), 1.0, rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert math.isclose(sum(component * component for component in up), 1.0, rel_tol=1.0e-9, abs_tol=1.0e-9)


def test_desktop_view_camera_round_trip_distance() -> None:
    cam_pos, basis = desktop_view_camera(30.0, -10.0, 15.0, 8.0)
    radius = math.sqrt(sum(component * component for component in cam_pos))
    assert math.isclose(radius, 8.0, rel_tol=1.0e-9, abs_tol=1.0e-9)
    assert len(basis) == 9
