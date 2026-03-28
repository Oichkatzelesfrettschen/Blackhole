#!/usr/bin/env python3
"""Render a small set of Blackhole showcase stills in Blender or OctaneBlender."""

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
    parser.add_argument("--engine", choices=("blackhole", "octane"), required=True)
    parser.add_argument("--width", type=int, default=640)
    parser.add_argument("--height", type=int, default=360)
    parser.add_argument("--json-out", type=pathlib.Path, required=True)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--artifact-dir", type=pathlib.Path, required=True)
    parser.add_argument("--sanitize-ocio", action="store_true")
    parser.add_argument("--timeout-seconds", type=float, default=900.0)
    return parser.parse_args(argv)


def write_optional(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def set_default_env(env: dict[str, str], name: str, value: str) -> None:
    env[name] = os.environ.get(name, value)


def stable_temp_root(source_dir: pathlib.Path) -> pathlib.Path:
    """Use a repo-local cache root instead of tmpfs-backed /tmp by default."""

    root = source_dir / ".cache" / "tmp"
    root.mkdir(parents=True, exist_ok=True)
    return root


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    blender_path = shutil.which(args.blender_executable) or args.blender_executable
    source_dir = args.source_dir.resolve()
    artifact_dir = args.artifact_dir.resolve()
    artifact_dir.mkdir(parents=True, exist_ok=True)
    temp_root = stable_temp_root(source_dir)

    with tempfile.TemporaryDirectory(prefix="blackhole_showcase_", dir=temp_root) as tmp:
        inner_report = pathlib.Path(tmp) / "showcase_inner.json"
        env = os.environ.copy()
        env["BLACKHOLE_SOURCE_DIR"] = str(source_dir)
        env["BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR"] = os.environ.get(
            "BLACKHOLE_BRIDGE_BACKGROUND_SKYBOX_DIR",
            str(source_dir / "assets" / "skybox_eso_milkyway"),
        )
        env["BLACKHOLE_SHOWCASE_SOURCE_DIR"] = str(source_dir)
        env["BLACKHOLE_SHOWCASE_REPORT_JSON"] = str(inner_report)
        env["BLACKHOLE_SHOWCASE_ENGINE"] = args.engine
        env["BLACKHOLE_SHOWCASE_WIDTH"] = str(args.width)
        env["BLACKHOLE_SHOWCASE_HEIGHT"] = str(args.height)
        env["BLACKHOLE_SHOWCASE_ARTIFACT_DIR"] = str(artifact_dir)
        env["BLACKHOLE_DREAM_TEXTURES_MEMORY_PROFILE"] = "low_vram"
        env["PYTORCH_CUDA_ALLOC_CONF"] = "expandable_segments:True"
        set_default_env(env, "BLACKHOLE_BRIDGE_ADISK_ENABLED", "0")
        set_default_env(env, "BLACKHOLE_BRIDGE_BACKGROUND_ENABLED", "1")
        set_default_env(env, "BLACKHOLE_BRIDGE_BACKGROUND_INTENSITY", "0.9")
        set_default_env(env, "BLACKHOLE_BRIDGE_STEP_SIZE", "0.02")
        set_default_env(env, "BLACKHOLE_BRIDGE_MAX_STEPS", "1000")
        set_default_env(env, "BLACKHOLE_BRIDGE_MAX_DIST", "160")
        set_default_env(env, "BLACKHOLE_BRIDGE_EXPOSURE", "2.6")
        set_default_env(env, "BLACKHOLE_BRIDGE_BLOOM_STRENGTH", "0.0")
        set_default_env(env, "BLACKHOLE_BRIDGE_PHOTON_GLOW_STRENGTH", "0.18")
        if args.user_scripts:
            env["BLENDER_USER_SCRIPTS"] = str(args.user_scripts.resolve())
        if args.sanitize_ocio:
            env.pop("OCIO", None)

        inline_code = textwrap.dedent(
            """
            import addon_utils
            import json
            import math
            import os
            import pathlib
            import sys

            import bpy
            from mathutils import Vector

            sys.modules['__main__'].__file__ = '<blender string>'

            source_dir = pathlib.Path(os.environ['BLACKHOLE_SHOWCASE_SOURCE_DIR'])
            sys.path.insert(0, str(source_dir / 'blender' / 'addon'))

            def enable_runtime_paths():
                user_scripts = os.environ.get('BLENDER_USER_SCRIPTS', '')
                if not user_scripts:
                    return
                runtime_json = pathlib.Path(user_scripts) / 'addons' / 'dream_textures' / '.python_dependencies' / 'runtime.json'
                if runtime_json.exists():
                    runtime_info = json.loads(runtime_json.read_text(encoding='utf-8'))
                    site_packages = runtime_info.get('site_packages', '')
                    if site_packages:
                        sys.path.insert(0, site_packages)

            def find_engine_id(expectation: str) -> str | None:
                engines = []
                for cls in bpy.types.RenderEngine.__subclasses__():
                    bl_idname = getattr(cls, 'bl_idname', None)
                    if bl_idname:
                        engines.append(bl_idname)
                lowered = {engine.lower(): engine for engine in engines}
                if expectation == 'blackhole':
                    return 'BLACKHOLE_RT' if 'BLACKHOLE_RT' in engines else None
                if expectation == 'octane':
                    for engine in engines:
                        if 'octane' in engine.lower():
                            return engine
                return None

            def point_camera_at_origin(camera):
                direction = Vector((0.0, 0.0, 0.0)) - camera.location
                camera.rotation_euler = direction.to_track_quat('-Z', 'Y').to_euler()

            def ensure_camera(scene, radius: float, inclination_deg: float):
                if scene.camera is None:
                    camera_data = bpy.data.cameras.new('ShowcaseCamera')
                    camera_obj = bpy.data.objects.new('ShowcaseCamera', camera_data)
                    scene.collection.objects.link(camera_obj)
                    scene.camera = camera_obj
                camera = scene.camera
                camera.data.lens = 18.0
                camera.data.sensor_width = 36.0
                camera.data.clip_start = 0.01
                camera.data.clip_end = 100000.0
                camera.location = blender_position_for_observer(
                    radius,
                    math.radians(inclination_deg),
                )
                point_camera_at_origin(camera)
                return camera

            def collect_disk_binding():
                obj = bpy.data.objects.get('AccretionDisk')
                if obj is None or getattr(obj, 'data', None) is None:
                    return False
                for material in getattr(obj.data, 'materials', []):
                    if material is None or not material.use_nodes or material.node_tree is None:
                        continue
                    for node in material.node_tree.nodes:
                        image = getattr(node, 'image', None)
                        if image is not None and getattr(image, 'name', '') == 'BlackholeDiskTexture':
                            return True
                return False

            def collect_world_binding(scene):
                world = getattr(scene, 'world', None)
                if world is None or not world.use_nodes or world.node_tree is None:
                    return False
                for node in world.node_tree.nodes:
                    if node.type == 'TEX_ENVIRONMENT':
                        image = getattr(node, 'image', None)
                        if image is not None and getattr(image, 'name', '') == 'BH_SD_Background':
                            return True
                return False

            def apply_black_world(scene):
                world = scene.world
                if world is None:
                    world = bpy.data.worlds.new('BH_ShowcaseWorld')
                    scene.world = world
                world.use_nodes = True
                nodes = world.node_tree.nodes
                links = world.node_tree.links
                nodes.clear()
                out_node = nodes.new('ShaderNodeOutputWorld')
                bg_node = nodes.new('ShaderNodeBackground')
                bg_node.inputs['Color'].default_value = (0.0, 0.0, 0.0, 1.0)
                bg_node.inputs['Strength'].default_value = 0.05
                links.new(bg_node.outputs['Background'], out_node.inputs['Surface'])

            def render_profile(scene, props, engine_id: str, profile: str, artifact_dir: pathlib.Path):
                if profile == 'harsh_lighting':
                    props.spin = 0.0
                    props.inclination_deg = 82.0
                    props.observer_distance = 8.0
                else:
                    props.spin = 0.0
                    props.inclination_deg = 90.0
                    props.observer_distance = 10.0
                ensure_camera(
                    scene,
                    float(props.observer_distance),
                    float(props.inclination_deg),
                )
                bpy.context.view_layer.update()

                disk_report = {}
                background_report = {}
                background_generation = {'status': 'skipped'}
                if engine_id != 'BLACKHOLE_RT':
                    props.sd_model_path = 'carsonkatri/stable-diffusion-2-depth-diffusers'
                    result = bpy.ops.blackhole.generate_disk_texture_with_policy()
                    if 'FINISHED' not in result:
                        raise RuntimeError(f'disk policy generation failed for {profile}: {result}')
                    raw = scene.get('bh_last_policy_generation_report', '')
                    if raw:
                        disk_report = json.loads(str(raw))
                    bpy.ops.blackhole.clear_sd_cache()
                    props.sd_model_path = 'stabilityai/sdxl-turbo'
                    try:
                        result = bpy.ops.blackhole.generate_background_texture_with_policy()
                        if 'FINISHED' not in result:
                            raise RuntimeError(f'background policy generation failed for {profile}: {result}')
                        raw = scene.get('bh_last_policy_generation_report', '')
                        if raw:
                            background_report = json.loads(str(raw))
                        background_generation = {'status': 'success'}
                    except Exception as exc:
                        apply_black_world(scene)
                        background_generation = {
                            'status': 'fallback_black_world',
                            'error': str(exc),
                        }
                    bpy.ops.blackhole.clear_sd_cache()
                else:
                    apply_black_world(scene)
                    background_generation = {
                        'status': 'blackhole_rt_skips_sd_background',
                    }

                render_path = artifact_dir / f"{profile}_{engine_id.lower()}.png"
                scene.render.engine = engine_id
                scene.render.image_settings.file_format = 'PNG'
                scene.render.filepath = str(render_path)
                render_result = bpy.ops.render.render(write_still=True, use_viewport=False)
                if 'FINISHED' not in render_result:
                    raise RuntimeError(f'render failed for {profile}: {render_result}')
                return {
                    'profile': profile,
                    'engine': scene.render.engine,
                    'render_path': str(render_path),
                    'disk_material_bound_image': collect_disk_binding(),
                    'world_environment_bound_image': collect_world_binding(scene),
                    'disk_policy_report': disk_report,
                    'background_policy_report': background_report,
                    'background_generation': background_generation,
                }

            enable_runtime_paths()
            addon_utils.enable('dream_textures', default_set=False, persistent=False)
            addon_utils.enable('blackhole_physics', default_set=False, persistent=False)

            import blackhole_physics  # noqa: F401
            from blackhole_physics import bridge, quality
            from blackhole_physics.camera_mapping import blender_position_for_observer

            report = {
                'status': 'failure',
                'engine_request': os.environ['BLACKHOLE_SHOWCASE_ENGINE'],
                'renders': [],
            }
            try:
                if not bridge.try_load_library():
                    raise RuntimeError('libblackhole_bridge.so did not load')
                scene = bpy.context.scene
                props = scene.blackhole
                props.spin = 0.9375
                props.mass_msun = 6.5e9
                props.mdot_edd = 0.1
                props.texture_width = 128
                props.texture_height = 128
                props.sd_backend = 'dream_textures'
                props.sd_prompt_style = 'scientific'
                props.sd_steps = 8
                props.sd_seed = 7
                props.sd_guidance_scale = 7.5
                bpy.ops.blackhole.generate_horizon()
                bpy.ops.blackhole.generate_disk()

                engine_id = find_engine_id(os.environ['BLACKHOLE_SHOWCASE_ENGINE'])
                if engine_id is None:
                    raise RuntimeError(f"Requested engine {os.environ['BLACKHOLE_SHOWCASE_ENGINE']} is unavailable")
                report['selected_engine'] = engine_id

                quality.apply_studio_quality(scene, target_engine=engine_id)
                artifact_dir = pathlib.Path(os.environ['BLACKHOLE_SHOWCASE_ARTIFACT_DIR'])
                artifact_dir.mkdir(parents=True, exist_ok=True)
                for profile in ('baseline', 'harsh_lighting'):
                    report['renders'].append(render_profile(scene, props, engine_id, profile, artifact_dir))
                report['status'] = 'success'
            except Exception as exc:
                import traceback
                report['error'] = str(exc)
                report['traceback'] = traceback.format_exc()
            pathlib.Path(os.environ['BLACKHOLE_SHOWCASE_REPORT_JSON']).write_text(
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

        report = {
            "label": args.label,
            "blender_executable": blender_path,
            "engine": args.engine,
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
        if inner_report.exists():
            raw_inner = inner_report.read_text(encoding="utf-8").strip()
            if raw_inner:
                report["inner_report"] = json.loads(raw_inner)
            else:
                report["inner_report"] = {"status": "failure", "error": "inner_report_empty"}
        else:
            report["inner_report"] = {"status": "failure", "error": "inner_report_missing"}
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
        write_optional(args.log_out, (proc.stdout or "") + ("\n" if proc.stdout else "") + (proc.stderr or ""))
        return 0 if proc.returncode == 0 and report["inner_report"].get("status") == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
