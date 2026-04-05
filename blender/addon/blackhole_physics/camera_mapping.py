"""Shared camera mapping helpers for the Blender Blackhole addon.

WHY: The physics bridge is axisymmetric around the spin axis, so the CUDA
renderer only needs observer distance and inclination. Blender scenes are Z-up,
while the bridge consumes an inclination from the spin axis. Keeping this
mapping in one pure-Python module makes the convention testable and reusable.
"""

from __future__ import annotations

import math


def observer_params_from_blender_position(
    x: float,
    y: float,
    z: float,
    minimum_distance: float = 2.5,
) -> tuple[float, float]:
    """Convert a Blender camera position into bridge observer parameters.

    Blender scenes in this addon are authored with Z-up composition. The
    physical inclination is the angle from the spin axis, so we measure it from
    the Blender Z axis and collapse upper/lower hemispheres with ``abs(z)``.
    The bridge does not model azimuth independently, only radius + inclination.
    """

    radius = math.sqrt((x * x) + (y * y) + (z * z))
    observer_r = max(minimum_distance, radius)
    if radius <= 1.0e-6:
        return observer_r, 0.0
    cos_theta = max(-1.0, min(1.0, abs(z) / radius))
    inclination_rad = math.acos(cos_theta)
    return observer_r, inclination_rad


def blender_position_for_observer(
    observer_r: float,
    inclination_rad: float,
    azimuth_rad: float = 0.0,
) -> tuple[float, float, float]:
    """Place a Blender camera for a desired physical observer configuration."""

    radius = max(observer_r, 0.0)
    cylindrical = radius * math.sin(inclination_rad)
    z = radius * math.cos(inclination_rad)
    x = cylindrical * math.cos(azimuth_rad)
    y = cylindrical * math.sin(azimuth_rad)
    return x, y, z


def camera_position_from_yaw_pitch(
    yaw_deg: float,
    pitch_deg: float,
    radius: float,
) -> tuple[float, float, float]:
    """Mirror the desktop cameraPositionFromYawPitch helper."""

    yaw_rad = math.radians(yaw_deg)
    pitch_rad = math.radians(pitch_deg)
    return (
        radius * math.cos(pitch_rad) * math.sin(yaw_rad),
        radius * math.sin(pitch_rad),
        radius * math.cos(pitch_rad) * math.cos(yaw_rad),
    )


def _normalize3(vec: tuple[float, float, float]) -> tuple[float, float, float]:
    x, y, z = vec
    length = math.sqrt((x * x) + (y * y) + (z * z))
    if length <= 1.0e-12:
        return (0.0, 0.0, 0.0)
    return (x / length, y / length, z / length)


def _cross3(
    a: tuple[float, float, float],
    b: tuple[float, float, float],
) -> tuple[float, float, float]:
    ax, ay, az = a
    bx, by, bz = b
    return (
        ay * bz - az * by,
        az * bx - ax * bz,
        ax * by - ay * bx,
    )


def build_camera_basis(
    camera_pos: tuple[float, float, float],
    target: tuple[float, float, float] = (0.0, 0.0, 0.0),
    roll_deg: float = 0.0,
) -> tuple[float, ...]:
    """Mirror the desktop buildCameraBasis helper in pure Python."""

    forward = _normalize3(
        (
            target[0] - camera_pos[0],
            target[1] - camera_pos[1],
            target[2] - camera_pos[2],
        )
    )
    world_up = (0.0, 1.0, 0.0)
    dot = forward[0] * world_up[0] + forward[1] * world_up[1] + forward[2] * world_up[2]
    if abs(dot) > 0.99:
        world_up = (0.0, 0.0, 1.0)

    right = _normalize3(_cross3(forward, world_up))
    up = _normalize3(_cross3(right, forward))

    if abs(roll_deg) > 0.001:
        roll_rad = math.radians(roll_deg)
        cos_roll = math.cos(roll_rad)
        sin_roll = math.sin(roll_rad)
        rolled_right = (
            right[0] * cos_roll + up[0] * sin_roll,
            right[1] * cos_roll + up[1] * sin_roll,
            right[2] * cos_roll + up[2] * sin_roll,
        )
        rolled_up = (
            -right[0] * sin_roll + up[0] * cos_roll,
            -right[1] * sin_roll + up[1] * cos_roll,
            -right[2] * sin_roll + up[2] * cos_roll,
        )
        right = rolled_right
        up = rolled_up

    return (
        right[0], right[1], right[2],
        up[0], up[1], up[2],
        forward[0], forward[1], forward[2],
    )


def desktop_view_camera(
    yaw_deg: float,
    pitch_deg: float,
    roll_deg: float,
    distance: float,
) -> tuple[tuple[float, float, float], tuple[float, ...]]:
    """Build an exact bridge camera pose matching desktop yaw/pitch/roll semantics."""

    camera_pos = camera_position_from_yaw_pitch(yaw_deg, pitch_deg, distance)
    camera_basis = build_camera_basis(camera_pos, (0.0, 0.0, 0.0), roll_deg)
    return camera_pos, camera_basis
