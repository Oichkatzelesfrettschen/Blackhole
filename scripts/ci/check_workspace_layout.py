"""Validate captured default workspace geometry without image comparisons."""

import argparse
import json
import math
from pathlib import Path
from typing import Any

# Minimum content areas at the smallest 1280x720 capture. The scene needs room
# for an image, while rails need room for controls or strategic decisions.
MINIMUMS = {
    "simulator": {"Viewport": (500, 300), "Settings": (300, 180), "Controls": (300, 180)},
    "propertime": {
        "Viewport": (500, 300),
        "Operations": (380, 180),
        "System/Strategic Map": (380, 180),
        "Briefing": (380, 120),
    },
    "diagnostics": {"Viewport": (500, 300), "Settings": (300, 180), "Controls": (300, 180)},
}
SCENE_MINIMUMS = {
    "observer": {"Observer sky": (300, 180)},
    "tesseract": {"Tesseract": (300, 180)},
}
EDGE_TOLERANCE = 2.0
OVERLAP_TOLERANCE = 4.0


def geometry(window: dict[str, Any]) -> tuple[float, float, float, float]:
    position = window["position"]
    size = window["size"]
    return (float(position[0]), float(position[1]), float(size[0]), float(size[1]))


def validate(layout: dict[str, Any]) -> list[str]:
    errors = []
    workspace = layout["workspace"]
    scene = layout.get("scene", "blackhole")
    if scene not in ("blackhole", "observer", "tesseract"):
        return [f"unknown scene: {scene}"]
    required = {**MINIMUMS[workspace], **SCENE_MINIMUMS.get(scene, {})}
    viewport_x, viewport_y, viewport_width, viewport_height = map(float, layout["viewport"])
    if viewport_width <= 0 or viewport_height <= 0 or not math.isfinite(float(layout["ui_scale"])):
        return ["invalid viewport or UI scale"]
    windows = {window["name"]: window for window in layout["windows"]}
    for name, minimum in required.items():
        if name not in windows:
            errors.append(f"missing visible decision window: {name}")
            continue
        window = windows[name]
        if name in SCENE_MINIMUMS.get(scene, {}) and not window.get("visible", True):
            errors.append(f"scene control window is not visible: {name}")
        if name in SCENE_MINIMUMS.get(scene, {}) and not window["dock_node_id"]:
            errors.append(f"scene control window is not docked: {name}")
        x, y, width, height = geometry(window)
        if window["collapsed"] or width < minimum[0] or height < minimum[1]:
            errors.append(f"undersized or collapsed decision window: {name}")
        if (
            x < viewport_x - EDGE_TOLERANCE
            or y < viewport_y - EDGE_TOLERANCE
            or x + width > viewport_x + viewport_width + EDGE_TOLERANCE
            or y + height > viewport_y + viewport_height + EDGE_TOLERANCE
        ):
            errors.append(f"decision window outside viewport: {name}")
    present = [windows[name] for name in required if name in windows]
    for index, first in enumerate(present):
        first_x, first_y, first_width, first_height = geometry(first)
        for second in present[index + 1 :]:
            if first["dock_node_id"] and first["dock_node_id"] == second["dock_node_id"]:
                continue
            second_x, second_y, second_width, second_height = geometry(second)
            overlap_width = min(first_x + first_width, second_x + second_width) - max(
                first_x, second_x
            )
            overlap_height = min(first_y + first_height, second_y + second_height) - max(
                first_y, second_y
            )
            if overlap_width > OVERLAP_TOLERANCE and overlap_height > OVERLAP_TOLERANCE:
                errors.append(f"decision windows overlap: {first['name']} and {second['name']}")
    return errors


def normalized(layout: dict[str, Any]) -> tuple[Any, ...]:
    """Ignore generated dock IDs while retaining the tab grouping they express."""
    dock_groups = {}
    windows = []
    for window in sorted(layout["windows"], key=lambda item: item["name"]):
        dock_id = window["dock_node_id"]
        group = dock_groups.setdefault(dock_id, len(dock_groups)) if dock_id else None
        windows.append((window["name"], group, window["collapsed"], window.get("visible", True)))
    return (
        layout["workspace"],
        layout.get("scene", "blackhole"),
        tuple(layout["viewport"]),
        layout["ui_scale"],
        tuple(windows),
    )


def geometry_drift(layout: dict[str, Any], first: dict[str, Any]) -> list[str]:
    """Name windows whose edges moved by more than EDGE_TOLERANCE after Reset Layout.

    DockBuilder rounds each split ratio to whole pixels against the node size,
    so a rebuilt splitter can land one pixel from the first build.
    """
    before = {window["name"]: geometry(window) for window in first["windows"]}
    drifted = []
    for window in layout["windows"]:
        previous = before.get(window["name"])
        if previous is None:
            continue
        x, y, width, height = geometry(window)
        edges = (x, y, x + width, y + height)
        previous_edges = (
            previous[0],
            previous[1],
            previous[0] + previous[2],
            previous[1] + previous[3],
        )
        if any(abs(a - b) > EDGE_TOLERANCE for a, b in zip(edges, previous_edges, strict=True)):
            drifted.append(window["name"])
    return drifted


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("layout", type=Path)
    parser.add_argument("first_layout", type=Path)
    arguments = parser.parse_args()
    layout = json.loads(arguments.layout.read_text(encoding="utf-8"))
    first = json.loads(arguments.first_layout.read_text(encoding="utf-8"))
    errors = validate(layout)
    errors.extend(validate(first))
    if normalized(layout) != normalized(first):
        errors.append("Reset Layout changed the window set, tab grouping, or selected tabs")
    errors.extend(
        f"Reset Layout moved {name} by more than {EDGE_TOLERANCE} px"
        for name in geometry_drift(layout, first)
    )
    for error in errors:
        print(error)
    if errors:
        raise SystemExit(1)
    print(f"{arguments.layout}: layout passed")


if __name__ == "__main__":
    main()
