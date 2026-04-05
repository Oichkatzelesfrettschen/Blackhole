#!/usr/bin/env python3
"""Verify policy-driven Dream Textures preparation/generation and cache reuse."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import textwrap


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", type=pathlib.Path, required=True)
    parser.add_argument("--user-scripts", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--slot", choices=("disk", "background"), default="disk")
    parser.add_argument("--intent", choices=("interactive", "production"), default="production")
    parser.add_argument("--scene-profile", choices=("baseline", "harsh_lighting"), default="baseline")
    parser.add_argument("--mutate-inclination-deg", type=float)
    parser.add_argument("--mutate-observer-distance", type=float)
    parser.add_argument("--timeout-seconds", type=float, default=240.0)
    parser.add_argument("--sanitize-ocio", action="store_true")
    parser.add_argument(
        "--memory-profile",
        choices=("default", "conditioning_sweep", "low_vram"),
        default="conditioning_sweep",
    )
    return parser.parse_args(argv)


def write_optional(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    checks = report.get("checks", {})
    warm = report.get("warm_prepare", {})
    cold = report.get("cold_prepare", {})
    stale = report.get("stale_prepare", {})
    lines = [
        "# Dream Textures Policy Generation Verification",
        "",
        f"- Label: `{report.get('label', '')}`",
        f"- Slot: `{report.get('slot', '')}`",
        f"- Intent: `{report.get('intent', '')}`",
        f"- Scene profile: `{report.get('scene_profile', '')}`",
        f"- Status: `{report.get('status', '')}`",
        f"- Return code: `{report.get('returncode', -1)}`",
        f"- Cold resolved mode: `{cold.get('resolved_mode', '')}`",
        f"- Warm resolved mode: `{warm.get('resolved_mode', '')}`",
        f"- Warm reused prerequisites: `{warm.get('preparation_summary', {}).get('reused', 0)}`",
        f"- Warm created prerequisites: `{warm.get('preparation_summary', {}).get('created', 0)}`",
        f"- Warm updated prerequisites: `{warm.get('preparation_summary', {}).get('updated', 0)}`",
        f"- Cold total seconds: `{cold.get('timing', {}).get('total_seconds', 0.0):.3f}`",
        f"- Warm total seconds: `{warm.get('timing', {}).get('total_seconds', 0.0):.3f}`",
    ]
    if stale:
        lines.extend(
            [
                f"- Stale resolved mode: `{stale.get('resolved_mode', '')}`",
                f"- Stale reused prerequisites: `{stale.get('preparation_summary', {}).get('reused', 0)}`",
                f"- Stale created prerequisites: `{stale.get('preparation_summary', {}).get('created', 0)}`",
                f"- Stale updated prerequisites: `{stale.get('preparation_summary', {}).get('updated', 0)}`",
                f"- Stale total seconds: `{stale.get('timing', {}).get('total_seconds', 0.0):.3f}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Checks",
            "",
        ]
    )
    for key, value in checks.items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    blender_path = shutil.which(args.blender_executable) or args.blender_executable
    source_dir = args.source_dir.resolve()
    user_scripts = args.user_scripts.resolve() if args.user_scripts else None

    with tempfile.TemporaryDirectory(prefix="blackhole_policy_generation_") as tmp:
        temp_root = pathlib.Path(tmp)
        inner_report = temp_root / "policy_generation_inner.json"
        env = os.environ.copy()
        env["BLACKHOLE_POLICY_VERIFY_SOURCE_DIR"] = str(source_dir)
        env["BLACKHOLE_POLICY_VERIFY_REPORT_JSON"] = str(inner_report)
        env["BLACKHOLE_POLICY_VERIFY_SLOT"] = args.slot
        env["BLACKHOLE_POLICY_VERIFY_INTENT"] = args.intent
        env["BLACKHOLE_POLICY_VERIFY_SCENE_PROFILE"] = args.scene_profile
        env["BLACKHOLE_POLICY_VERIFY_MUTATE_INCLINATION_DEG"] = (
            "" if args.mutate_inclination_deg is None else str(args.mutate_inclination_deg)
        )
        env["BLACKHOLE_POLICY_VERIFY_MUTATE_OBSERVER_DISTANCE"] = (
            "" if args.mutate_observer_distance is None else str(args.mutate_observer_distance)
        )
        env["BLACKHOLE_DREAM_TEXTURES_MEMORY_PROFILE"] = args.memory_profile
        if args.memory_profile != "default":
            env["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
        if user_scripts is not None:
            env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        if args.sanitize_ocio:
            env.pop("OCIO", None)

        inline_code = textwrap.dedent(
            """
            import json
            import os
            import pathlib
            import sys

            import bpy

            sys.modules['__main__'].__file__ = '<blender string>'

            source_dir = pathlib.Path(os.environ['BLACKHOLE_POLICY_VERIFY_SOURCE_DIR'])
            sys.path.insert(0, str(source_dir / 'blender' / 'addon'))

            import blackhole_physics
            try:
                blackhole_physics.register()
            except ValueError:
                pass

            scene = bpy.context.scene
            props = scene.blackhole
            props.sd_backend = 'dream_textures'
            props.sd_prompt_style = 'scientific'
            props.sd_prompt_prefix = ''
            props.sd_negative_prompt = ''
            props.sd_steps = 8
            props.sd_seed = 7
            props.sd_guidance_scale = 7.5
            props.sd_conditioning_strength = 0.35
            props.sd_target_slot = os.environ['BLACKHOLE_POLICY_VERIFY_SLOT']
            props.texture_width = 64
            props.texture_height = 64
            props.spin = 0.9375
            props.mass_msun = 6.5e9
            props.mdot_edd = 0.1
            props.inclination_deg = 17.0
            props.observer_distance = 500.0
            if os.environ['BLACKHOLE_POLICY_VERIFY_SCENE_PROFILE'] == 'harsh_lighting':
                props.inclination_deg = 34.0
                props.observer_distance = 24.0

            slot = os.environ['BLACKHOLE_POLICY_VERIFY_SLOT']
            intent = os.environ['BLACKHOLE_POLICY_VERIFY_INTENT']
            props.sd_model_path = 'stabilityai/sdxl-turbo'
            report_key = 'bh_last_policy_generation_report'

            def _latest():
                raw = scene.get(report_key, '')
                return json.loads(str(raw)) if raw else {}

            prepare_result = bpy.ops.blackhole.prepare_scene_for_policy_generation(
                target_slot=slot,
                intent=intent,
            )
            cold_prepare = _latest()
            second_result = bpy.ops.blackhole.prepare_scene_for_policy_generation(
                target_slot=slot,
                intent=intent,
            )
            warm_prepare = _latest()
            stale_prepare = {}
            stale_result = {'SKIPPED'}
            mutate_inclination = os.environ.get('BLACKHOLE_POLICY_VERIFY_MUTATE_INCLINATION_DEG', '').strip()
            mutate_distance = os.environ.get('BLACKHOLE_POLICY_VERIFY_MUTATE_OBSERVER_DISTANCE', '').strip()
            if mutate_inclination:
                props.inclination_deg = float(mutate_inclination)
            if mutate_distance:
                props.observer_distance = float(mutate_distance)
            if mutate_inclination or mutate_distance:
                stale_result = bpy.ops.blackhole.prepare_scene_for_policy_generation(
                    target_slot=slot,
                    intent=intent,
                )
                stale_prepare = _latest()

            checks = {
                'prepare_finished': 'FINISHED' in prepare_result,
                'prepare_only_reported': bool(cold_prepare.get('prepare_only', False)),
                'warm_prepare_finished': 'FINISHED' in second_result,
                'warm_prepare_only_reported': bool(warm_prepare.get('prepare_only', False)),
                'resolved_mode_consistent': cold_prepare.get('resolved_mode', '') == warm_prepare.get('resolved_mode', ''),
                'warm_reused_inputs': warm_prepare.get('preparation_summary', {}).get('reused', 0) >= 1 if slot == 'disk' else True,
            }
            if mutate_inclination or mutate_distance:
                checks['stale_prepare_finished'] = 'FINISHED' in stale_result
                checks['stale_prepare_only_reported'] = bool(stale_prepare.get('prepare_only', False))
                checks['stale_refresh_detected'] = (
                    stale_prepare.get('preparation_summary', {}).get('updated', 0)
                    + stale_prepare.get('preparation_summary', {}).get('created', 0)
                ) >= 1 if slot == 'disk' else True

            report = {
                'status': 'success' if all(checks.values()) else 'failure',
                'slot': slot,
                'intent': intent,
                'scene_profile': os.environ['BLACKHOLE_POLICY_VERIFY_SCENE_PROFILE'],
                'cold_prepare': cold_prepare,
                'warm_prepare': warm_prepare,
                'stale_prepare': stale_prepare,
                'mutation': {
                    'inclination_deg': mutate_inclination,
                    'observer_distance': mutate_distance,
                },
                'checks': checks,
            }
            pathlib.Path(os.environ['BLACKHOLE_POLICY_VERIFY_REPORT_JSON']).write_text(
                json.dumps(report, indent=2, sort_keys=True),
                encoding='utf-8',
            )
            """
        )

        command = [
            blender_path,
            "--factory-startup",
            "--background",
            "--python-expr",
            inline_code,
        ]
        proc = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=args.timeout_seconds,
            env=env,
        )
        inner = {}
        if inner_report.exists():
            inner = json.loads(inner_report.read_text(encoding="utf-8"))
        report = {
            "label": args.label,
            "blender_executable": blender_path,
            "slot": args.slot,
            "intent": args.intent,
            "scene_profile": args.scene_profile,
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            **inner,
        }
        if not inner_report.exists():
            report["status"] = "failure"
            report["checks"] = {"inner_report_present": False}
        report["json_out"] = str(args.json_out)
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
        write_optional(args.md_out, render_markdown(report))
        write_optional(args.log_out, (proc.stdout or "") + ("\n" if proc.stdout else "") + (proc.stderr or ""))
        return 0 if proc.returncode == 0 and report.get("status") == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
