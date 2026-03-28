#!/usr/bin/env python3
"""Run an isolated Blender addon benchmark and capture a structured report."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import tempfile

from octane_server_util import ensure_octane_server


def set_default_env(env: dict[str, str], name: str, value: str) -> None:
    env[name] = os.environ.get(name, value)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--addon-zip", required=True)
    parser.add_argument("--bridge-lib", required=True)
    parser.add_argument("--label", default="blender-interactive")
    parser.add_argument("--quality-tier", default="auto")
    parser.add_argument("--scene-profile", default="baseline")
    parser.add_argument("--width", type=int, default=640)
    parser.add_argument("--height", type=int, default=360)
    parser.add_argument("--measured-frames", type=int, default=4)
    parser.add_argument("--warmup-frames", type=int, default=1)
    parser.add_argument(
        "--scenario",
        choices=["all", "bridge_lensing", "bridge_cuda", "render_engine"],
        default="all",
    )
    parser.add_argument("--expect-engine", choices=["blackhole", "octane", "cycles"], default="blackhole")
    parser.add_argument("--json-out")
    parser.add_argument("--log-out")
    parser.add_argument("--timeout-seconds", type=int, default=180)
    parser.add_argument("--disable-mcp-scene", action="store_true")
    parser.add_argument("--octane-readiness-report")
    return parser


def normalize_output(value) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def stable_temp_root(source_dir: pathlib.Path) -> pathlib.Path:
    """Use a repo-local cache root instead of tmpfs-backed /tmp by default."""

    root = source_dir / ".cache" / "tmp"
    root.mkdir(parents=True, exist_ok=True)
    return root

def maybe_prepare_octane_server() -> dict[str, object]:
    return ensure_octane_server()


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    addon_zip = pathlib.Path(args.addon_zip).resolve()
    bridge_lib = pathlib.Path(args.bridge_lib).resolve()
    inner_script = source_dir / "scripts" / "blender_interactive_benchmark_inner.py"
    mcp_scene_script = source_dir / "scripts" / "run_blender_mcp_studio_scene.py"
    json_out = pathlib.Path(args.json_out).resolve() if args.json_out else None
    log_out = pathlib.Path(args.log_out).resolve() if args.log_out else None
    octane_readiness_path = pathlib.Path(args.octane_readiness_report).resolve() if args.octane_readiness_report else None

    if not addon_zip.exists():
        raise SystemExit(f"Addon package not found: {addon_zip}")
    if not bridge_lib.exists():
        raise SystemExit(f"Bridge library not found: {bridge_lib}")
    if not inner_script.exists():
        raise SystemExit(f"Inner Blender benchmark script not found: {inner_script}")
    if not args.disable_mcp_scene and not mcp_scene_script.exists():
        raise SystemExit(f"Blender MCP scene bootstrap script not found: {mcp_scene_script}")
    blender_path = shutil.which(args.blender_executable) or args.blender_executable

    with tempfile.TemporaryDirectory(
        prefix="blackhole_blender_benchmark_",
        dir=stable_temp_root(source_dir),
    ) as tmp:
        temp_root = pathlib.Path(tmp)
        user_scripts = temp_root / "scripts"
        addons_dir = user_scripts / "addons"
        addons_dir.mkdir(parents=True, exist_ok=True)
        shutil.unpack_archive(str(addon_zip), str(addons_dir), "zip")

        env = os.environ.copy()
        env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        env["BLACKHOLE_SOURCE_DIR"] = str(source_dir)
        env["BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR"] = os.environ.get(
            "BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR",
            str(source_dir / "assets" / "skybox_eso_milkyway"),
        )
        set_default_env(env, "BLACKHOLE_BRIDGE_ADISK_ENABLED", "0")
        set_default_env(env, "BLACKHOLE_BRIDGE_BACKGROUND_ENABLED", "1")
        set_default_env(env, "BLACKHOLE_BRIDGE_BACKGROUND_INTENSITY", "0.9")
        set_default_env(env, "BLACKHOLE_BRIDGE_STEP_SIZE", "0.02")
        set_default_env(env, "BLACKHOLE_BRIDGE_MAX_STEPS", "1000")
        set_default_env(env, "BLACKHOLE_BRIDGE_MAX_DIST", "160")
        set_default_env(env, "BLACKHOLE_BRIDGE_EXPOSURE", "2.6")
        set_default_env(env, "BLACKHOLE_BRIDGE_BLOOM_STRENGTH", "0.0")
        set_default_env(env, "BLACKHOLE_BRIDGE_PHOTON_GLOW_STRENGTH", "0.18")
        env["BLACKHOLE_BRIDGE_LIB"] = str(bridge_lib)
        env["BLACKHOLE_BENCHMARK_LABEL"] = args.label
        env["BLACKHOLE_BENCHMARK_QUALITY_TIER"] = args.quality_tier
        env["BLACKHOLE_BENCHMARK_SCENE_PROFILE"] = args.scene_profile
        env["BLACKHOLE_BENCHMARK_WIDTH"] = str(args.width)
        env["BLACKHOLE_BENCHMARK_HEIGHT"] = str(args.height)
        env["BLACKHOLE_BENCHMARK_MEASURED_FRAMES"] = str(args.measured_frames)
        env["BLACKHOLE_BENCHMARK_WARMUP_FRAMES"] = str(args.warmup_frames)
        env["BLACKHOLE_BENCHMARK_SCENARIO"] = args.scenario
        env["BLACKHOLE_BENCHMARK_EXPECT_ENGINE"] = args.expect_engine
        env.pop("OCIO", None)
        inner_report = temp_root / "benchmark_report.json"
        env["BLACKHOLE_BENCHMARK_REPORT_JSON"] = str(inner_report)
        artifact_dir = (json_out.parent / f"{json_out.stem}_artifacts") if json_out is not None else (temp_root / "artifacts")
        artifact_dir.mkdir(parents=True, exist_ok=True)
        env["BLACKHOLE_BENCHMARK_ARTIFACT_DIR"] = str(artifact_dir)
        benchmark_scene_blend = temp_root / "benchmark_scene.blend"
        mcp_scene_json = temp_root / "mcp_scene_report.json"
        mcp_scene_log = temp_root / "mcp_scene.log"

        mcp_scene_report = {}
        octane_server_info = {}
        octane_readiness = {}
        octane_preflight_warning = ""
        if args.expect_engine == "octane":
            if octane_readiness_path is not None and octane_readiness_path.exists():
                octane_readiness = json.loads(octane_readiness_path.read_text(encoding="utf-8"))
                octane_server_info = dict(octane_readiness.get("server", {}))
            else:
                octane_server_info = maybe_prepare_octane_server()
                octane_readiness = {
                    "readiness": "server_unavailable" if not octane_server_info.get("running", False) else "not_ready",
                    "ready_for_automation": False,
                    "reason": "Octane readiness probe was not provided to the benchmark runner",
                    "server": octane_server_info,
                }
            readiness_class = str(octane_readiness.get("readiness", ""))
            if readiness_class == "server_unavailable" and not octane_server_info.get("running", False):
                env["BLACKHOLE_BENCHMARK_SKIP_FINAL_RENDER"] = "1"
                env["BLACKHOLE_BENCHMARK_SKIP_FINAL_RENDER_REASON"] = str(
                    octane_readiness.get("reason", "Octane render automation is not ready")
                )
            elif not octane_readiness.get("ready_for_automation", False):
                octane_preflight_warning = str(
                    octane_readiness.get("reason", "Octane readiness probe was inconclusive")
                )
        if not args.disable_mcp_scene:
            scene_startup_timeout = max(float(args.timeout_seconds), 120.0)
            scene_probe_timeout = 20.0
            if args.expect_engine == "octane":
                scene_probe_timeout = min(max(float(args.timeout_seconds) / 2.0, 45.0), float(args.timeout_seconds))
            mcp_command = [
                shutil.which("python3") or "python3",
                str(mcp_scene_script),
                "--blender-executable",
                blender_path,
                "--source-dir",
                str(source_dir),
                "--addon-zip",
                str(addon_zip),
                "--bridge-lib",
                str(bridge_lib),
                "--blend-out",
                str(benchmark_scene_blend),
                "--session-root",
                str(temp_root / "mcp_session"),
                "--width",
                str(args.width),
                "--height",
                str(args.height),
                "--engine-mode",
                args.expect_engine,
                "--startup-timeout",
                str(scene_startup_timeout),
                "--probe-timeout",
                str(scene_probe_timeout),
                "--json-out",
                str(mcp_scene_json),
                "--log-out",
                str(mcp_scene_log),
            ]
            mcp_proc = subprocess.run(
                mcp_command,
                env=env,
                check=False,
                capture_output=True,
                text=True,
                timeout=args.timeout_seconds,
            )
            if mcp_proc.stdout:
                print(mcp_proc.stdout, end="")
            if mcp_proc.stderr:
                print(mcp_proc.stderr, end="")
            if mcp_proc.returncode != 0:
                raise SystemExit(
                    "Failed to build benchmark scene through isolated BlenderMCP: "
                    f"rc={mcp_proc.returncode}"
                )
            if mcp_scene_json.exists():
                mcp_scene_report = json.loads(mcp_scene_json.read_text(encoding="utf-8"))

        command = [
            blender_path,
            "--background",
            "--factory-startup",
        ]
        if benchmark_scene_blend.exists():
            command.append(str(benchmark_scene_blend))
        command.extend([
            "--python-exit-code",
            "1",
            "--python",
            str(inner_script),
        ])
        report = {
            "blender_executable": blender_path,
            "label": args.label,
            "quality_tier": args.quality_tier,
            "scene_profile": args.scene_profile,
            "addon_zip": str(addon_zip),
            "bridge_lib": str(bridge_lib),
            "width": args.width,
            "height": args.height,
            "measured_frames": args.measured_frames,
            "warmup_frames": args.warmup_frames,
            "scenario": args.scenario,
            "expect_engine": args.expect_engine,
            "command": command,
            "mcp_scene_enabled": not args.disable_mcp_scene,
            "mcp_scene_report": mcp_scene_report,
            "octane_server": octane_server_info,
            "octane_readiness": octane_readiness,
            "octane_preflight_warning": octane_preflight_warning,
            "artifact_dir": str(artifact_dir),
            "log_path": str(log_out) if log_out is not None else "",
            "inner_report": {},
        }
        try:
            proc = subprocess.run(
                command,
                env=env,
                check=False,
                capture_output=True,
                text=True,
                timeout=args.timeout_seconds,
            )
            combined_output = normalize_output(proc.stdout) + normalize_output(proc.stderr)
            report["returncode"] = proc.returncode
        except subprocess.TimeoutExpired as exc:
            combined_output = normalize_output(exc.stdout) + normalize_output(exc.stderr)
            report["returncode"] = 124
            report["error"] = f"Timed out after {args.timeout_seconds} seconds"
        if combined_output:
            print(combined_output, end="")
        if inner_report.exists():
            report["inner_report"] = json.loads(inner_report.read_text(encoding="utf-8"))
        if log_out is not None:
            log_out.parent.mkdir(parents=True, exist_ok=True)
            log_out.write_text(combined_output, encoding="utf-8")
        if json_out is not None:
            json_out.parent.mkdir(parents=True, exist_ok=True)
            json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return int(report["returncode"])


if __name__ == "__main__":
    raise SystemExit(main())
