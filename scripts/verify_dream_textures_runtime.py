#!/usr/bin/env python3
"""Verify Dream Textures generation inside Blender or OctaneBlender."""

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
    parser.add_argument("--user-scripts", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--model-id", default="stabilityai/sdxl-turbo")
    parser.add_argument("--prompt", default="cinematic black hole accretion disk")
    parser.add_argument("--width", type=int, default=64)
    parser.add_argument("--height", type=int, default=64)
    parser.add_argument("--steps", type=int, default=1)
    parser.add_argument("--seed", type=int, default=1)
    return parser.parse_args(argv)


def write_optional(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    inner = report.get("inner_report", {})
    lines = [
        "# Dream Textures Runtime Verification",
        "",
        f"- Label: `{report.get('label', '')}`",
        f"- Executable: `{report.get('blender_executable', '')}`",
        f"- Return code: `{report.get('returncode', -1)}`",
        f"- Status: `{inner.get('status', '')}`",
        f"- Device: `{inner.get('device', '')}`",
        f"- Model: `{inner.get('model_id', '')}`",
        f"- Shape: `{inner.get('shape', [])}`",
        f"- Mean: `{inner.get('mean', 0.0):.6f}`",
        "",
    ]
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    blender_path = shutil.which(args.blender_executable) or args.blender_executable
    user_scripts = args.user_scripts.resolve() if args.user_scripts else None

    with tempfile.TemporaryDirectory(prefix="blackhole_dream_textures_probe_") as tmp:
        temp_root = pathlib.Path(tmp)
        inner_report = temp_root / "dream_textures_inner.json"
        env = os.environ.copy()
        env["BLACKHOLE_DREAM_TEXTURES_REPORT_JSON"] = str(inner_report)
        env["BLACKHOLE_DREAM_TEXTURES_MODEL_ID"] = args.model_id
        env["BLACKHOLE_DREAM_TEXTURES_PROMPT"] = args.prompt
        env["BLACKHOLE_DREAM_TEXTURES_WIDTH"] = str(args.width)
        env["BLACKHOLE_DREAM_TEXTURES_HEIGHT"] = str(args.height)
        env["BLACKHOLE_DREAM_TEXTURES_STEPS"] = str(args.steps)
        env["BLACKHOLE_DREAM_TEXTURES_SEED"] = str(args.seed)
        if user_scripts is not None:
            env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        env.pop("OCIO", None)

        inline_code = textwrap.dedent(
            """
            import addon_utils, json, os, pathlib, sys
            sys.modules['__main__'].__file__ = '<blender string>'
            addon_utils.enable('dream_textures', default_set=False, persistent=False)
            from dream_textures.generator_process import Generator
            from dream_textures.generator_process.models import Optimizations, Scheduler
            from dream_textures.api.models.step_preview_mode import StepPreviewMode

            def extract_first_image(payload):
                if isinstance(payload, list):
                    if not payload:
                        raise ValueError('Dream Textures returned an empty list')
                    payload = payload[-1]
                if hasattr(payload, 'image'):
                    return payload.image, type(payload).__name__
                if hasattr(payload, 'images') and payload.images:
                    return payload.images[0], type(payload).__name__
                raise TypeError(f'Unsupported Dream Textures result container: {type(payload)!r}')

            report_path = pathlib.Path(os.environ['BLACKHOLE_DREAM_TEXTURES_REPORT_JSON'])
            report = {
                'status': 'failure',
                'model_id': os.environ.get('BLACKHOLE_DREAM_TEXTURES_MODEL_ID', 'stabilityai/sdxl-turbo'),
                'prompt': os.environ.get('BLACKHOLE_DREAM_TEXTURES_PROMPT', 'cinematic black hole accretion disk'),
                'width': int(os.environ.get('BLACKHOLE_DREAM_TEXTURES_WIDTH', '64')),
                'height': int(os.environ.get('BLACKHOLE_DREAM_TEXTURES_HEIGHT', '64')),
                'steps': int(os.environ.get('BLACKHOLE_DREAM_TEXTURES_STEPS', '1')),
                'seed': int(os.environ.get('BLACKHOLE_DREAM_TEXTURES_SEED', '1')),
            }
            try:
                gen = Generator.shared()
                optimizations = Optimizations()
                installed_models = gen.hf_list_installed_models().result()
                device = gen.choose_device(optimizations).result()
                output = gen.prompt_to_image(
                    model=report['model_id'],
                    scheduler=Scheduler.DDIM,
                    optimizations=optimizations,
                    prompt=report['prompt'],
                    steps=report['steps'],
                    width=report['width'],
                    height=report['height'],
                    seed=report['seed'],
                    cfg_scale=1.0,
                    use_negative_prompt=False,
                    negative_prompt='',
                    seamless_axes=False,
                    iterations=1,
                    step_preview_mode=StepPreviewMode.NONE,
                    sdxl_refiner_model=None,
                ).result(last_only=True)
                image, container_type = extract_first_image(output)
                report.update({
                    'status': 'success',
                    'device': str(device),
                    'installed_model_count': len(installed_models),
                    'result_type': type(output).__name__,
                    'container_type': container_type,
                    'shape': list(image.shape),
                    'mean': float(image.mean()),
                    'min': float(image.min()),
                    'max': float(image.max()),
                })
            except Exception as exc:
                report['error'] = repr(exc)
            report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\\n', encoding='utf-8')
            print(json.dumps(report, sort_keys=True))
            """
        ).strip()

        proc = subprocess.run(
            [
                blender_path,
                "--background",
                "--factory-startup",
                "--python-exit-code",
                "1",
                "--python-expr",
                inline_code,
            ],
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )
        combined_output = (proc.stdout or "") + (proc.stderr or "")
        payload = {}
        if inner_report.exists():
            payload = json.loads(inner_report.read_text(encoding="utf-8"))

    report = {
        "label": args.label,
        "blender_executable": blender_path,
        "user_scripts": str(user_scripts) if user_scripts is not None else "",
        "returncode": proc.returncode,
        "inner_report": payload,
    }
    if args.log_out is not None:
        write_optional(args.log_out.resolve(), combined_output)
    if proc.returncode != 0:
        raise SystemExit(f"Dream Textures probe failed with return code {proc.returncode}")
    if payload.get("status") != "success":
        raise SystemExit(f"Dream Textures probe did not succeed: {payload.get('error', payload)}")
    if payload.get("device") != "cuda":
        raise SystemExit(f"Dream Textures did not select CUDA: {payload.get('device')}")
    if int(payload.get("installed_model_count", 0)) <= 0:
        raise SystemExit("Dream Textures did not detect any installed models")
    shape = payload.get("shape", [])
    if shape != [args.height, args.width, 3]:
        raise SystemExit(f"Unexpected Dream Textures image shape: {shape}")
    if float(payload.get("max", 0.0)) <= float(payload.get("min", 0.0)):
        raise SystemExit("Dream Textures image statistics were degenerate")

    write_optional(args.json_out.resolve() if args.json_out else None, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_optional(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
