"""Synthetic coverage for workspace layout admission rules."""

import unittest
from typing import Any

from check_workspace_layout import geometry_drift, normalized, validate


def layout() -> dict[str, Any]:
    return {
        "workspace": "simulator",
        "viewport": [0, 0, 1280, 720],
        "ui_scale": 1,
        "windows": [
            {
                "name": "Viewport",
                "position": [400, 20],
                "size": [880, 700],
                "dock_node_id": 3,
                "collapsed": False,
            },
            {
                "name": "Settings",
                "position": [0, 20],
                "size": [400, 350],
                "dock_node_id": 1,
                "collapsed": False,
            },
            {
                "name": "Controls",
                "position": [0, 370],
                "size": [400, 350],
                "dock_node_id": 2,
                "collapsed": False,
            },
        ],
    }


class WorkspaceLayoutChecks(unittest.TestCase):
    def test_valid_layout(self) -> None:
        self.assertEqual(validate(layout()), [])

    def test_missing_and_small_window(self) -> None:
        changed = layout()
        changed["windows"][1]["size"] = [100, 100]
        changed["windows"].pop()
        self.assertTrue(any("missing" in error for error in validate(changed)))
        self.assertTrue(any("undersized" in error for error in validate(changed)))

    def test_overlap_and_bounds(self) -> None:
        changed = layout()
        changed["windows"][1]["position"] = [420, 20]
        self.assertTrue(any("overlap" in error for error in validate(changed)))
        changed["windows"][1]["position"] = [-20, 20]
        self.assertTrue(any("outside" in error for error in validate(changed)))

    def test_generated_dock_ids_do_not_change_layout(self) -> None:
        changed = layout()
        for window in changed["windows"]:
            window["dock_node_id"] += 100
        self.assertEqual(normalized(layout()), normalized(changed))
        changed["windows"][1]["dock_node_id"] = changed["windows"][2]["dock_node_id"]
        self.assertNotEqual(normalized(layout()), normalized(changed))

    def test_reset_geometry_tolerates_splitter_rounding_only(self) -> None:
        rounded = layout()
        rounded["windows"][1]["size"][1] += 1
        rounded["windows"][2]["position"][1] += 1
        rounded["windows"][2]["size"][1] -= 1
        self.assertEqual(geometry_drift(rounded, layout()), [])
        moved = layout()
        moved["windows"][0]["size"][0] -= 20
        self.assertEqual(geometry_drift(moved, layout()), ["Viewport"])


if __name__ == "__main__":
    unittest.main()
