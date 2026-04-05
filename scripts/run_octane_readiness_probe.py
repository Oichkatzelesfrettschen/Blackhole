#!/usr/bin/env python3
"""Run a tiny OctaneBlender render probe and classify automation readiness."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import tempfile

from octane_server_util import ensure_octane_server

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--addon-zip", required=True)
    parser.add_argument("--bridge-lib", required=True)
    parser.add_argument("--json-out")
    parser.add_argument("--log-out")
    parser.add_argument("--width", type=int, default=96)
    parser.add_argument("--height", type=int, default=54)
    parser.add_argument("--timeout-seconds", type=int, default=180)
    return parser

def classify_readiness(inner_report: dict, output: str, server_running: bool) -> tuple[str, str]:
    lowered = output.lower()
    if inner_report.get("render_ready"):
        return "ready", "Octane headless probe produced a non-empty render artifact"
    if "can't connect to octane server" in lowered or "connecttoserver" in lowered:
        if server_running:
            return "setup_required", "Octane server appears installed, but headless rendering still could not connect"
        return "server_unavailable", "OctaneBlender could not connect to OctaneServer for final rendering"
    if any(token in lowered for token in ("sign in", "log in", "activate", "account", "cudnn")):
        return "setup_required", "Octane interactive first-run setup or sign-in still appears to be required"
    if inner_report.get("status") == "failure":
        return "probe_failed", inner_report.get("error", "Octane readiness probe failed")
    return "not_ready", "Octane launched, but the readiness probe could not verify a final render"


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    addon_zip = pathlib.Path(args.addon_zip).resolve()
    bridge_lib = pathlib.Path(args.bridge_lib).resolve()
    inner_script = source_dir / "scripts" / "octane_readiness_probe_inner.py"
    json_out = pathlib.Path(args.json_out).resolve() if args.json_out else None
    log_out = pathlib.Path(args.log_out).resolve() if args.log_out else None
    blender_path = shutil.which(args.blender_executable) or args.blender_executable

    if not inner_script.exists():
        raise SystemExit(f"Inner Octane readiness probe script not found: {inner_script}")
    if not addon_zip.exists():
        raise SystemExit(f"Addon package not found: {addon_zip}")
    if not bridge_lib.exists():
        raise SystemExit(f"Bridge library not found: {bridge_lib}")

    with tempfile.TemporaryDirectory(prefix="blackhole_octane_probe_") as tmp:
        temp_root = pathlib.Path(tmp)
        user_scripts = temp_root / "scripts"
        addons_dir = user_scripts / "addons"
        addons_dir.mkdir(parents=True, exist_ok=True)
        shutil.unpack_archive(str(addon_zip), str(addons_dir), "zip")

        inner_report_path = temp_root / "octane_probe_inner.json"
        output_image_path = temp_root / "octane_probe.png"
        env = os.environ.copy()
        env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        env["BLACKHOLE_BRIDGE_LIB"] = str(bridge_lib)
        env["BLACKHOLE_OCTANE_PROBE_REPORT_JSON"] = str(inner_report_path)
        env["BLACKHOLE_OCTANE_PROBE_IMAGE_PATH"] = str(output_image_path)
        env["BLACKHOLE_OCTANE_PROBE_WIDTH"] = str(args.width)
        env["BLACKHOLE_OCTANE_PROBE_HEIGHT"] = str(args.height)
        env.pop("OCIO", None)
        server_info = ensure_octane_server(temp_root / "octaneserver_autolaunch.log")

        command = [
            blender_path,
            "--background",
            "--factory-startup",
            "--python-exit-code",
            "1",
            "--python",
            str(inner_script),
        ]
        timed_out = False
        try:
            proc = subprocess.run(
                command,
                env=env,
                check=False,
                capture_output=True,
                text=True,
                timeout=args.timeout_seconds,
            )
            combined_output = (proc.stdout or "") + (proc.stderr or "")
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            proc = subprocess.CompletedProcess(
                command,
                124,
                stdout=(exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")),
                stderr=(exc.stderr.decode("utf-8", errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")),
            )
            combined_output = (proc.stdout or "") + (proc.stderr or "")
        inner_report = {}
        if inner_report_path.exists():
            inner_report = json.loads(inner_report_path.read_text(encoding="utf-8"))
        readiness, reason = classify_readiness(inner_report, combined_output, bool(server_info.get("running", False)))
        if timed_out and readiness in {"not_ready", "probe_failed"}:
            readiness = "setup_required" if server_info.get("running", False) else "server_unavailable"
            reason = (
                f"Octane headless readiness probe timed out after {args.timeout_seconds} seconds while waiting for a render"
            )
        report = {
            "blender_executable": blender_path,
            "bridge_lib": str(bridge_lib),
            "addon_zip": str(addon_zip),
            "command": command,
            "returncode": proc.returncode,
            "timed_out": timed_out,
            "server": server_info,
            "inner_report": inner_report,
            "readiness": readiness,
            "ready_for_automation": readiness == "ready",
            "reason": reason,
            "output_image": str(output_image_path),
        }
        if log_out is not None:
            log_out.parent.mkdir(parents=True, exist_ok=True)
            log_out.write_text(combined_output, encoding="utf-8")
        if json_out is not None:
            json_out.parent.mkdir(parents=True, exist_ok=True)
            json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

        print(json.dumps(report, indent=2, sort_keys=True))
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
