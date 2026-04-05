#!/usr/bin/env python3
"""Verify the direct Dream Textures -> Blackhole texture pipeline."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import signal
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
    parser.add_argument("--slot", choices=("disk", "background"), default="disk")
    parser.add_argument("--model-id", default="stabilityai/sdxl-turbo")
    parser.add_argument("--prompt-style", choices=("scientific", "hybrid", "cinematic"), default="scientific")
    parser.add_argument("--conditioning-mode", choices=("none", "image", "depth", "image_depth"), default="none")
    parser.add_argument("--scene-profile", choices=("baseline", "harsh_lighting"), default="baseline")
    parser.add_argument("--conditioning-strength", type=float, default=0.35)
    parser.add_argument("--width", type=int, default=64)
    parser.add_argument("--height", type=int, default=64)
    parser.add_argument("--steps", type=int, default=8)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--timeout-seconds", type=float, default=180.0)
    parser.add_argument("--sanitize-ocio", action="store_true")
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--artifact-out", type=pathlib.Path)
    parser.add_argument(
        "--memory-profile",
        choices=("default", "conditioning_sweep", "low_vram"),
        default="default",
    )
    return parser.parse_args(argv)


def write_optional(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    inner = report.get("inner_report", {})
    lines = [
        "# Dream Textures Direct Pipeline Verification",
        "",
        f"- Label: `{report.get('label', '')}`",
        f"- Executable: `{report.get('blender_executable', '')}`",
        f"- Return code: `{report.get('returncode', -1)}`",
        f"- Status: `{inner.get('status', '')}`",
        f"- Slot: `{inner.get('slot', '')}`",
        f"- Backend: `{inner.get('selected_backend', '')}`",
        f"- Prompt style: `{inner.get('prompt_style', '')}`",
        f"- Conditioning: `{inner.get('conditioning_policy', {}).get('effective_mode', inner.get('conditioning_mode', 'text_to_image'))}`",
        f"- Model: `{inner.get('model_id', '')}`",
        f"- Image name: `{inner.get('image_name', '')}`",
        f"- Image exists: `{bool(inner.get('image_exists', False))}`",
        f"- Shape: `{inner.get('shape', [])}`",
        f"- Mean: `{inner.get('mean', 0.0):.6f}`",
        f"- Asset SHA256: `{inner.get('asset_digest', {}).get('sha256', '')}`",
        "",
    ]
    prompt_budget = inner.get("prompt_budget", {})
    if prompt_budget:
        lines.extend(
            [
                f"- Prompt chars: `{prompt_budget.get('prompt_characters', 0)}`",
                f"- Within budget: `{prompt_budget.get('within_budget', False)}`",
                "",
            ]
        )
    conditioning = inner.get("conditioning_policy", {})
    if conditioning.get("has_source_depth", False):
        lines.extend(
            [
                f"- Source depth name: `{conditioning.get('source_depth_name', '')}`",
                f"- Source depth range: `{conditioning.get('source_depth_metadata', {}).get('range', [])}`",
                "",
            ]
        )
    if "world_environment_applied" in inner:
        lines.append(
            f"- World environment applied: `{inner.get('world_environment_applied', False)}`"
        )
        lines.append("")
    prompt = inner.get("prompt", "")
    if prompt:
        lines.append(f"- Prompt: `{prompt}`")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    blender_path = shutil.which(args.blender_executable) or args.blender_executable
    source_dir = args.source_dir.resolve()
    user_scripts = args.user_scripts.resolve() if args.user_scripts else None

    with tempfile.TemporaryDirectory(prefix="blackhole_dream_direct_") as tmp:
        temp_root = pathlib.Path(tmp)
        inner_report = temp_root / "dream_textures_direct_inner.json"
        env = os.environ.copy()
        env["BLACKHOLE_DREAM_DIRECT_REPORT_JSON"] = str(inner_report)
        env["BLACKHOLE_DREAM_DIRECT_SOURCE_DIR"] = str(source_dir)
        env["BLACKHOLE_DREAM_DIRECT_SLOT"] = args.slot
        env["BLACKHOLE_DREAM_DIRECT_MODEL_ID"] = args.model_id
        env["BLACKHOLE_DREAM_DIRECT_PROMPT_STYLE"] = args.prompt_style
        env["BLACKHOLE_DREAM_DIRECT_CONDITIONING_MODE"] = args.conditioning_mode
        env["BLACKHOLE_DREAM_DIRECT_SCENE_PROFILE"] = args.scene_profile
        env["BLACKHOLE_DREAM_DIRECT_CONDITIONING_STRENGTH"] = str(args.conditioning_strength)
        env["BLACKHOLE_DREAM_DIRECT_WIDTH"] = str(args.width)
        env["BLACKHOLE_DREAM_DIRECT_HEIGHT"] = str(args.height)
        env["BLACKHOLE_DREAM_DIRECT_STEPS"] = str(args.steps)
        env["BLACKHOLE_DREAM_DIRECT_SEED"] = str(args.seed)
        env["BLACKHOLE_DREAM_TEXTURES_MEMORY_PROFILE"] = args.memory_profile
        if args.memory_profile != "default":
            env["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
        if user_scripts is not None:
            env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        if args.sanitize_ocio:
            env.pop("OCIO", None)
        if args.artifact_out is not None:
            env["BLACKHOLE_DREAM_DIRECT_ARTIFACT_OUT"] = str(args.artifact_out.resolve())

        inline_code = textwrap.dedent(
            """
            import addon_utils
            import bpy
            import json
            import numpy as np
            import os
            import pathlib
            import sys

            sys.modules['__main__'].__file__ = '<blender string>'

            source_dir = pathlib.Path(os.environ['BLACKHOLE_DREAM_DIRECT_SOURCE_DIR'])
            sys.path.insert(0, str(source_dir / 'blender' / 'addon'))

            user_scripts = os.environ.get('BLENDER_USER_SCRIPTS', '')
            if user_scripts:
                runtime_json = pathlib.Path(user_scripts) / 'addons' / 'dream_textures' / '.python_dependencies' / 'runtime.json'
                if runtime_json.exists():
                    runtime_info = json.loads(runtime_json.read_text(encoding='utf-8'))
                    site_packages = runtime_info.get('site_packages', '')
                    if site_packages:
                        sys.path.insert(0, site_packages)

            addon_utils.enable('dream_textures', default_set=False, persistent=False)
            import torch  # noqa: F401

            from blackhole_physics import operators, sd_textures
            from blackhole_physics import bridge

            class Props:
                sd_model_path = os.environ['BLACKHOLE_DREAM_DIRECT_MODEL_ID']
                sd_backend = 'dream_textures'
                sd_prompt_prefix = ''
                sd_negative_prompt = ''
                sd_steps = int(os.environ['BLACKHOLE_DREAM_DIRECT_STEPS'])
                sd_seed = int(os.environ['BLACKHOLE_DREAM_DIRECT_SEED'])
                sd_guidance_scale = 7.5
                sd_prompt_style = os.environ['BLACKHOLE_DREAM_DIRECT_PROMPT_STYLE']
                sd_conditioning_mode = os.environ['BLACKHOLE_DREAM_DIRECT_CONDITIONING_MODE']
                scene_profile = os.environ['BLACKHOLE_DREAM_DIRECT_SCENE_PROFILE']
                sd_conditioning_strength = float(os.environ['BLACKHOLE_DREAM_DIRECT_CONDITIONING_STRENGTH'])
                texture_width = int(os.environ['BLACKHOLE_DREAM_DIRECT_WIDTH'])
                texture_height = int(os.environ['BLACKHOLE_DREAM_DIRECT_HEIGHT'])
                spin = 0.9375
                inclination_deg = 17.0
                mass_msun = 6.5e9
                mdot_edd = 0.1
                observer_distance = 32.0
                sd_target_slot = os.environ['BLACKHOLE_DREAM_DIRECT_SLOT']

            report_path = pathlib.Path(os.environ['BLACKHOLE_DREAM_DIRECT_REPORT_JSON'])
            report = {
                'status': 'failure',
                'slot': Props.sd_target_slot,
                'prompt_style': Props.sd_prompt_style,
                'model_id': Props.sd_model_path,
                'conditioning_mode': Props.sd_conditioning_mode,
                'scene_profile': Props.scene_profile,
                'conditioning_strength': Props.sd_conditioning_strength,
                'width': Props.texture_width,
                'height': Props.texture_height,
                'steps': Props.sd_steps,
                'seed': Props.sd_seed,
            }
            try:
                props = Props()
                if props.scene_profile == 'harsh_lighting':
                    props.inclination_deg = 34.0
                    props.observer_distance = 24.0
                if props.sd_conditioning_mode in {'image', 'depth', 'image_depth'}:
                    if not bridge.try_load_library():
                        raise RuntimeError('Conditioned Dream Textures verification requires libblackhole_bridge.so')
                    if props.sd_target_slot == 'disk':
                        positions, normals, temperatures, uvs, indices = bridge.generate_disk_mesh(
                            a_star=props.spin,
                            mass_msun=props.mass_msun,
                            mdot_edd=props.mdot_edd,
                            r_out_rg=100.0,
                            inclination_rad=props.inclination_deg * 3.141592653589793 / 180.0,
                            n_radial=32,
                            n_azimuthal=64,
                        )
                        disk_coll = operators._ensure_collection('Blackhole Disk')
                        for obj in list(disk_coll.objects):
                            bpy.data.objects.remove(obj, do_unlink=True)
                        disk_mesh = operators._mesh_from_arrays('AccretionDisk', positions, indices, normals)
                        disk_obj = bpy.data.objects.new('AccretionDisk', disk_mesh)
                        disk_coll.objects.link(disk_obj)

                        horizon_positions, horizon_indices = bridge.generate_horizon_mesh(
                            a_star=props.spin,
                            n_theta=24,
                            n_phi=48,
                        )
                        structure_coll = operators._ensure_collection('Blackhole Structure')
                        for obj in list(structure_coll.objects):
                            bpy.data.objects.remove(obj, do_unlink=True)
                        horizon_mesh = operators._mesh_from_arrays('EventHorizon', horizon_positions, horizon_indices)
                        horizon_obj = bpy.data.objects.new('EventHorizon', horizon_mesh)
                        structure_coll.objects.link(horizon_obj)

                        lensing = bridge.render_lensing_map(
                            a_star=props.spin,
                            observer_r=props.observer_distance,
                            inclination_rad=props.inclination_deg * 3.141592653589793 / 180.0,
                            width=props.texture_width,
                            height=props.texture_height,
                        )
                        operators._image_from_array(
                            'BlackholeLensingMap',
                            lensing,
                            props.texture_width,
                            props.texture_height,
                        )
                    else:
                        seed_props = Props()
                        seed_props.sd_conditioning_mode = 'none'
                        seed_data, _seed_metadata = sd_textures.generate_with_metadata(seed_props)
                        operators._image_from_array(
                            'BH_SD_Background',
                            seed_data,
                            seed_props.texture_width,
                            seed_props.texture_height,
                        )
                        operators._apply_as_world_background(bpy.context, 'BH_SD_Background')
                data, metadata = sd_textures.generate_with_metadata(props)
                slot = props.sd_target_slot
                image_name = 'BlackholeDiskTexture' if slot == 'disk' else 'BH_SD_Background'
                operators._image_from_array(
                    image_name,
                    data,
                    props.texture_width,
                    props.texture_height,
                )
                if slot == 'background':
                    operators._apply_as_world_background(bpy.context, image_name)
                image = bpy.data.images.get(image_name)
                world_environment_applied = False
                world_environment_image = ''
                world = bpy.context.scene.world
                if slot == 'background' and world and world.use_nodes:
                    env_node = next(
                        (node for node in world.node_tree.nodes if node.type == 'TEX_ENVIRONMENT'),
                        None,
                    )
                    if env_node is not None and env_node.image is not None:
                        world_environment_image = env_node.image.name
                        world_environment_applied = env_node.image.name == image_name
                report.update({
                    'status': 'success',
                    'image_name': image_name,
                    'image_exists': image is not None,
                    'shape': list(data.shape),
                    'min': float(data.min()),
                    'max': float(data.max()),
                    'mean': float(data.mean()),
                    'world_environment_applied': world_environment_applied,
                    'world_environment_image': world_environment_image,
                })
                report.update(metadata)
                if image is not None:
                    report['image_size'] = list(image.size)
                    artifact_out = os.environ.get('BLACKHOLE_DREAM_DIRECT_ARTIFACT_OUT', '')
                    if artifact_out:
                        artifact_path = pathlib.Path(artifact_out)
                        artifact_path.parent.mkdir(parents=True, exist_ok=True)
                        try:
                            from PIL import Image
                            rgba = np.clip(data, 0.0, 1.0)
                            rgba_u8 = (rgba * 255.0).round().astype(np.uint8)
                            Image.fromarray(rgba_u8, mode='RGBA').save(artifact_path)
                        except Exception:
                            image.filepath_raw = str(artifact_path)
                            image.file_format = 'PNG'
                            image.save()
                        report['artifact_path'] = str(artifact_path)
            except Exception as exc:
                report['error'] = repr(exc)
            report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\\n', encoding='utf-8')
            print(json.dumps(report, sort_keys=True))
            """
        ).strip()

        timed_out = False
        command = [
            blender_path,
            "--background",
            "--factory-startup",
            "--python-exit-code",
            "1",
            "--python-expr",
            inline_code,
        ]
        proc_handle = subprocess.Popen(
            command,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        try:
            stdout, stderr = proc_handle.communicate(timeout=args.timeout_seconds)
            proc = subprocess.CompletedProcess(command, proc_handle.returncode, stdout, stderr)
            combined_output = (stdout or "") + (stderr or "")
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            try:
                os.killpg(proc_handle.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                stdout, stderr = proc_handle.communicate(timeout=10.0)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc_handle.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = proc_handle.communicate()
            combined_output = stdout + stderr
            proc = subprocess.CompletedProcess(
                command,
                124,
                stdout,
                stderr,
            )
        finally:
            try:
                os.killpg(proc_handle.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        payload = {}
        if inner_report.exists():
            payload = json.loads(inner_report.read_text(encoding="utf-8"))

    report = {
        "label": args.label,
        "blender_executable": blender_path,
        "user_scripts": str(user_scripts) if user_scripts is not None else "",
        "source_dir": str(source_dir),
        "scene_profile": args.scene_profile,
        "memory_profile": args.memory_profile,
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "inner_report": payload,
    }
    write_optional(args.log_out.resolve() if args.log_out else None, combined_output)

    if proc.returncode != 0 and not (timed_out and payload.get("status") == "success"):
        raise SystemExit(f"Dream Textures direct pipeline probe failed with return code {proc.returncode}")
    if payload.get("status") != "success":
        raise SystemExit(f"Dream Textures direct pipeline did not succeed: {payload.get('error', payload)}")
    if payload.get("slot") != args.slot:
        raise SystemExit(f"Unexpected slot in direct pipeline report: {payload.get('slot')}")
    if payload.get("scene_profile") != args.scene_profile:
        raise SystemExit(f"Unexpected scene profile in direct pipeline report: {payload.get('scene_profile')}")
    if payload.get("selected_backend") != "dream_textures":
        raise SystemExit(f"Direct pipeline did not use dream_textures: {payload.get('selected_backend')}")
    if not payload.get("image_exists", False):
        raise SystemExit("Direct pipeline did not populate a Blender image")
    expected_image_name = "BlackholeDiskTexture" if args.slot == "disk" else "BH_SD_Background"
    if payload.get("image_name") != expected_image_name:
        raise SystemExit(f"Unexpected image target: {payload.get('image_name')}")
    shape = payload.get("shape", [])
    if shape != [args.height, args.width, 4]:
        raise SystemExit(f"Unexpected direct pipeline shape: {shape}")
    image_size = payload.get("image_size", [])
    if image_size != [args.width, args.height]:
        raise SystemExit(f"Unexpected Blender image size: {image_size}")
    if float(payload.get("max", 0.0)) <= float(payload.get("min", 0.0)):
        raise SystemExit("Direct pipeline image statistics were degenerate")
    if args.artifact_out is not None:
        artifact_path = pathlib.Path(payload.get("artifact_path", ""))
        if not artifact_path.exists():
            raise SystemExit(f"Direct pipeline did not write artifact image: {artifact_path}")
    prompt = str(payload.get("prompt", ""))
    if not prompt:
        raise SystemExit("Direct pipeline prompt was empty")
    if args.slot == "background" and not payload.get("world_environment_applied", False):
        raise SystemExit("Background direct pipeline did not update the world environment")
    if "prompt_budget" not in payload:
        raise SystemExit("Direct pipeline prompt budget metadata was missing")
    if "asset_digest" not in payload:
        raise SystemExit("Direct pipeline asset digest metadata was missing")
    if "seed_policy" not in payload:
        raise SystemExit("Direct pipeline seed policy metadata was missing")
    if "backend_capabilities" not in payload:
        raise SystemExit("Direct pipeline backend capability metadata was missing")
    if payload.get("conditioning_policy", {}).get("mode") != args.conditioning_mode:
        raise SystemExit(
            f"Unexpected conditioning mode in report: {payload.get('conditioning_policy', {}).get('mode')}"
        )
    if args.conditioning_mode != "none":
        conditioning_policy = payload.get("conditioning_policy", {})
        if not conditioning_policy.get("implemented", False):
            raise SystemExit("Conditioned direct pipeline did not mark conditioning as implemented")
        if not conditioning_policy.get("source_origin", ""):
            raise SystemExit("Conditioned direct pipeline did not record source provenance")
        if args.slot == "disk" and args.conditioning_mode in {"image", "image_depth"} and not conditioning_policy.get("source_image_name", ""):
            raise SystemExit("Conditioned disk pipeline did not record a source image name")
        if args.conditioning_mode in {"depth", "image_depth"}:
            if not conditioning_policy.get("has_source_depth", False):
                raise SystemExit("Depth-conditioned direct pipeline did not capture a source depth field")
            if not conditioning_policy.get("source_depth_name", ""):
                raise SystemExit("Depth-conditioned direct pipeline did not record a source depth name")
            depth_range = conditioning_policy.get("source_depth_metadata", {}).get("range", [])
            if not depth_range or float(depth_range[-1]) <= float(depth_range[0]):
                raise SystemExit(f"Depth-conditioned direct pipeline reported a degenerate depth range: {depth_range}")

    write_optional(args.json_out.resolve(), json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_optional(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
