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
