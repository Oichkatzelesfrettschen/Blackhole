#!/usr/bin/env python3
"""Run inside Blender to benchmark the Blackhole addon render paths."""

from __future__ import annotations

import ctypes
import json
import math
import os
import pathlib
import time
import traceback

import addon_utils
import bpy
import numpy as np
from mathutils import Vector
from blackhole_physics.camera_mapping import blender_position_for_observer


def get_env_int(name: str, default: int) -> int:
    value = os.environ.get(name)
    if value is None or value == "":
        return default
    return int(value)


def compute_metrics(frame_times_ms: list[float]) -> dict[str, float | int]:
    values = np.array(frame_times_ms, dtype=np.float64)
    if values.size == 0:
        raise RuntimeError("Benchmark captured zero measured frames")
    median_ms = float(np.median(values))
    mean_ms = float(np.mean(values))
    p95_ms = float(np.percentile(values, 95))
    p99_ms = float(np.percentile(values, 99))
    hitch_threshold_ms = float(max(16.667, median_ms * 2.0))
    hitch_count = int(np.sum(values > hitch_threshold_ms))
    one_percent_bucket = max(1, int(math.ceil(values.size * 0.01)))
    worst_ms = np.sort(values)[-one_percent_bucket:]
    worst_mean_ms = float(np.mean(worst_ms))
    return {
        "sample_count": int(values.size),
        "mean_ms": mean_ms,
        "median_ms": median_ms,
        "min_ms": float(np.min(values)),
        "max_ms": float(np.max(values)),
        "p95_ms": p95_ms,
        "p99_ms": p99_ms,
        "mean_fps": float(1000.0 / mean_ms) if mean_ms > 0.0 else 0.0,
        "median_fps": float(1000.0 / median_ms) if median_ms > 0.0 else 0.0,
        "one_percent_low_fps": float(1000.0 / worst_mean_ms) if worst_mean_ms > 0.0 else 0.0,
        "hitch_threshold_ms": hitch_threshold_ms,
        "hitch_count": hitch_count,
    }


def compute_image_quality_metrics(array: np.ndarray) -> dict[str, float]:
    rgba = np.asarray(array, dtype=np.float64)
    rgb = rgba[..., :3]
    alpha = rgba[..., 3]
    luma = 0.2126 * rgb[..., 0] + 0.7152 * rgb[..., 1] + 0.0722 * rgb[..., 2]
    dx = np.abs(np.diff(luma, axis=1))
    dy = np.abs(np.diff(luma, axis=0))
    edge_energy = float((dx.mean() if dx.size else 0.0) + (dy.mean() if dy.size else 0.0))
    return {
        "mean_luma": float(np.mean(luma)),
        "std_luma": float(np.std(luma)),
        "max_luma": float(np.max(luma)),
        "p99_luma": float(np.percentile(luma, 99)),
        "nonzero_rgb_fraction": float(np.mean(np.any(rgb > 1.0e-6, axis=2))),
        "alpha_mean": float(np.mean(alpha)),
        "edge_energy": edge_energy,
    }


def compute_comparison_metrics(reference: np.ndarray, candidate: np.ndarray) -> tuple[dict[str, float], np.ndarray]:
    ref = np.clip(np.asarray(reference, dtype=np.float64), 0.0, 1.0)
    cur = np.clip(np.asarray(candidate, dtype=np.float64), 0.0, 1.0)
    if ref.shape != cur.shape:
        raise RuntimeError(f"Image comparison requires equal shapes, got {ref.shape} vs {cur.shape}")
    ref_rgb = ref[..., :3]
    cur_rgb = cur[..., :3]
    diff_rgb = cur_rgb - ref_rgb
    abs_diff_rgb = np.abs(diff_rgb)
    mae_rgb = float(np.mean(abs_diff_rgb))
    rmse_rgb = float(np.sqrt(np.mean(np.square(diff_rgb))))
    max_abs_diff_rgb = float(np.max(abs_diff_rgb))

    ref_luma = 0.2126 * ref_rgb[..., 0] + 0.7152 * ref_rgb[..., 1] + 0.0722 * ref_rgb[..., 2]
    cur_luma = 0.2126 * cur_rgb[..., 0] + 0.7152 * cur_rgb[..., 1] + 0.0722 * cur_rgb[..., 2]
    diff_luma = cur_luma - ref_luma
    abs_diff_luma = np.abs(diff_luma)
    mae_luma = float(np.mean(abs_diff_luma))
    rmse_luma = float(np.sqrt(np.mean(np.square(diff_luma))))
    max_abs_diff_luma = float(np.max(abs_diff_luma))
    ref_mean = float(np.mean(ref_luma))
    cur_mean = float(np.mean(cur_luma))
    denom = float(np.sqrt(np.sum(np.square(ref_luma))) * np.sqrt(np.sum(np.square(cur_luma))))
    cosine_similarity = float(np.sum(ref_luma * cur_luma) / denom) if denom > 0.0 else 0.0
    psnr_rgb = float(20.0 * math.log10(1.0 / max(rmse_rgb, 1.0e-8)))
    psnr_luma = float(20.0 * math.log10(1.0 / max(rmse_luma, 1.0e-8)))

    diff_norm = abs_diff_luma / max(max_abs_diff_luma, 1.0e-8)
    heatmap = np.zeros(ref.shape, dtype=np.float32)
    heatmap[..., 0] = diff_norm.astype(np.float32)
    heatmap[..., 1] = np.sqrt(diff_norm).astype(np.float32) * 0.35
    heatmap[..., 2] = (1.0 - diff_norm).astype(np.float32) * 0.15
    heatmap[..., 3] = 1.0
    return (
        {
            "mae_rgb": mae_rgb,
            "rmse_rgb": rmse_rgb,
            "max_abs_diff_rgb": max_abs_diff_rgb,
            "psnr_rgb": psnr_rgb,
            "mae_luma": mae_luma,
            "rmse_luma": rmse_luma,
            "max_abs_diff_luma": max_abs_diff_luma,
            "psnr_luma": psnr_luma,
            "reference_mean_luma": ref_mean,
            "candidate_mean_luma": cur_mean,
            "luma_cosine_similarity": cosine_similarity,
        },
        heatmap,
    )


def save_array_png(path: pathlib.Path, array: np.ndarray) -> None:
    rgba = np.clip(np.asarray(array, dtype=np.float32), 0.0, 1.0)
    height, width, _channels = rgba.shape
    image = bpy.data.images.new(path.stem, width=width, height=height, alpha=True, float_buffer=False)
    try:
        image.filepath_raw = str(path)
        image.file_format = "PNG"
        image.pixels.foreach_set(rgba.reshape(-1))
        image.save()
    finally:
        bpy.data.images.remove(image)


def load_image_array(path: pathlib.Path) -> np.ndarray:
    image = bpy.data.images.load(str(path), check_existing=False)
    try:
        width = image.size[0]
        height = image.size[1]
        pixels = np.array(image.pixels[:], dtype=np.float32).reshape(height, width, 4)
        return pixels
    finally:
        bpy.data.images.remove(image)


def upsert_bpy_image_from_array(name: str, array: np.ndarray) -> bpy.types.Image:
    rgba = np.asarray(array, dtype=np.float32)
    height, width, _channels = rgba.shape
    image = bpy.data.images.get(name)
    if image is None:
        image = bpy.data.images.new(name, width=width, height=height, alpha=True, float_buffer=False)
    else:
        if image.size[0] != width or image.size[1] != height:
            bpy.data.images.remove(image)
            image = bpy.data.images.new(name, width=width, height=height, alpha=True, float_buffer=False)
    image.colorspace_settings.name = "sRGB"
    image.alpha_mode = "STRAIGHT"
    image.pixels.foreach_set(np.clip(rgba, 0.0, 1.0).reshape(-1))
    image.update()
    return image


def find_engine_id(expectation: str) -> str | None:
    engines = []
    for cls in bpy.types.RenderEngine.__subclasses__():
        bl_idname = getattr(cls, "bl_idname", None)
        if bl_idname:
            engines.append(bl_idname)
    lowered = {engine.lower(): engine for engine in engines}
    if expectation == "blackhole":
        return "BLACKHOLE_RT" if "BLACKHOLE_RT" in engines else None
    if expectation == "cycles":
        return lowered.get("cycles")
    if expectation == "octane":
        for engine in engines:
            if "octane" in engine.lower():
                return engine
    return None


def point_camera_at_origin(camera: bpy.types.Object) -> None:
    target = Vector((0.0, 0.0, 0.0))
    direction = target - camera.location
    camera.rotation_euler = direction.to_track_quat("-Z", "Y").to_euler()


def ensure_light_object(scene: bpy.types.Scene, name: str) -> bpy.types.Object:
    light = bpy.data.objects.get(name)
    if light is None or light.type != "LIGHT":
        light_data = bpy.data.lights.new(name, type="POINT")
        if light is not None and light.name in bpy.data.objects:
            bpy.data.objects.remove(light, do_unlink=True)
        light = bpy.data.objects.new(name, light_data)
        scene.collection.objects.link(light)
    return light


def remove_object_if_present(name: str) -> None:
    obj = bpy.data.objects.get(name)
    if obj is not None:
        bpy.data.objects.remove(obj, do_unlink=True)


def configure_scene_profile(scene: bpy.types.Scene, scene_profile: str) -> None:
    key_light = ensure_light_object(scene, "Light")
    rim_light = ensure_light_object(scene, "BenchmarkRimLight")
    top_light = ensure_light_object(scene, "BenchmarkTopLight")

    key_light.hide_render = False
    rim_light.hide_render = False
    top_light.hide_render = False

    if scene_profile == "harsh_lighting":
        scene.blackhole.spin = 0.0
        scene.blackhole.inclination_deg = 82.0
        scene.blackhole.observer_distance = 8.0
        key_light.location = (1.5, -3.5, 1.0)
        key_light.data.energy = 14000.0
        key_light.data.color = (1.0, 0.91, 0.82)
        rim_light.location = (-6.0, 4.0, 5.5)
        rim_light.data.energy = 9000.0
        rim_light.data.color = (0.72, 0.82, 1.0)
        top_light.location = (0.0, 0.0, 10.0)
        top_light.data.energy = 4500.0
        top_light.data.color = (0.95, 0.97, 1.0)
    else:
        scene.blackhole.spin = 0.0
        scene.blackhole.inclination_deg = 90.0
        scene.blackhole.observer_distance = 10.0
        key_light.location = (4.08, 1.01, 5.9)
        key_light.data.energy = 4000.0
        key_light.data.color = (1.0, 1.0, 1.0)
        rim_light.hide_render = True
        top_light.hide_render = True


def ensure_benchmark_scene(width: int, height: int, scene_profile: str) -> bpy.types.Scene:
    scene = bpy.context.scene
    remove_object_if_present("Cube")
    if scene.camera is None:
        camera_data = bpy.data.cameras.new("BenchmarkCamera")
        camera_obj = bpy.data.objects.new("BenchmarkCamera", camera_data)
        scene.collection.objects.link(camera_obj)
        scene.camera = camera_obj
    camera = scene.camera
    camera.data.lens = 18.0
    camera.data.sensor_width = 36.0
    camera.data.clip_start = 0.01
    camera.data.clip_end = 100000.0
    props = scene.blackhole
    props.spin = 0.9375
    props.mass_msun = 6.5e9
    props.texture_width = width
    props.texture_height = height
    scene.render.resolution_x = width
    scene.render.resolution_y = height
    scene.render.resolution_percentage = 100
    scene.render.use_compositing = False
    scene.render.use_sequencer = False
    configure_scene_profile(scene, scene_profile)
    camera.location = blender_position_for_observer(
        float(props.observer_distance),
        math.radians(float(props.inclination_deg)),
    )
    point_camera_at_origin(camera)
    return scene


def suppress_external_scene_lighting(scene: bpy.types.Scene) -> None:
    for obj in scene.objects:
        if getattr(obj, "type", "") == "LIGHT":
            obj.hide_render = True
            obj.hide_viewport = True
            if getattr(obj, "data", None) is not None and hasattr(obj.data, "energy"):
                obj.data.energy = 0.0
    world = scene.world
    if world is None:
        return
    world.use_nodes = True
    nodes = world.node_tree.nodes if world.node_tree is not None else None
    if nodes is None:
        return
    background = nodes.get("Background")
    if background is not None:
        if "Color" in background.inputs:
            background.inputs["Color"].default_value = (0.0, 0.0, 0.0, 1.0)
        if "Strength" in background.inputs:
            background.inputs["Strength"].default_value = 0.0


def build_orbit_poses(scene: bpy.types.Scene, total_frames: int) -> list[tuple[float, float, float]]:
    observer_r = float(scene.blackhole.observer_distance)
    inclination_rad = math.radians(float(scene.blackhole.inclination_deg))
    cylindrical = observer_r * math.sin(inclination_rad)
    z = observer_r * math.cos(inclination_rad)
    poses: list[tuple[float, float, float]] = []
    for index in range(total_frames):
        phase = (2.0 * math.pi * index) / max(total_frames, 1)
        poses.append((cylindrical * math.cos(phase), cylindrical * math.sin(phase), z))
    return poses


def current_params(scene: bpy.types.Scene) -> dict[str, float]:
    from blackhole_physics import render_engine

    return render_engine._blender_camera_to_params(scene, None)


def frame_signature(array: np.ndarray) -> dict[str, object]:
    rgba = np.asarray(array, dtype=np.float64)
    mean_rgba = [float(x) for x in np.mean(rgba, axis=(0, 1))]
    return {
        "shape": list(rgba.shape),
        "mean_rgba": mean_rgba,
        "checksum": float(np.sum(rgba)),
    }


def benchmark_loop(
    name: str,
    backend: str,
    scene: bpy.types.Scene,
    poses: list[tuple[float, float, float]],
    warmup_frames: int,
    measured_frames: int,
    render_frame,
    artifact_dir: pathlib.Path | None,
) -> dict[str, object]:
    total_frames = warmup_frames + measured_frames
    if total_frames <= 0:
        raise RuntimeError("Benchmark requires at least one frame")
    frame_times_ms: list[float] = []
    last_signature: dict[str, object] = {}
    last_image: np.ndarray | None = None
    artifact_path = ""
    quality_metrics: dict[str, float] = {}
    for index in range(total_frames):
        camera = scene.camera
        camera.location = poses[index]
        point_camera_at_origin(camera)
        bpy.context.view_layer.update()
        start = time.perf_counter()
        result = render_frame(index)
        signature = result["signature"]
        elapsed_ms = (time.perf_counter() - start) * 1000.0
        if index >= warmup_frames:
            frame_times_ms.append(float(elapsed_ms))
            last_signature = signature
            last_image = result.get("image")
    metrics = compute_metrics(frame_times_ms)
    if artifact_dir is not None and last_image is not None:
        artifact_dir.mkdir(parents=True, exist_ok=True)
        artifact_file = artifact_dir / f"{name}.png"
        save_array_png(artifact_file, last_image)
        artifact_path = str(artifact_file)
        quality_metrics = compute_image_quality_metrics(last_image)
    return {
        "name": name,
        "backend": backend,
        "width": int(scene.render.resolution_x),
        "height": int(scene.render.resolution_y),
        "warmup_frames": warmup_frames,
        "measured_frames": measured_frames,
        "frame_times_ms": frame_times_ms,
        "metrics": metrics,
        "result_signature": last_signature,
        "artifact_path": artifact_path,
        "quality_metrics": quality_metrics,
    }


def build_comparison_artifact_name(reference_name: str, candidate_name: str) -> str:
    return f"{candidate_name}_vs_{reference_name}_diff"


def main() -> int:
    label = os.environ.get("BLACKHOLE_BENCHMARK_LABEL", "blender-interactive")
    scenario = os.environ.get("BLACKHOLE_BENCHMARK_SCENARIO", "all")
    expect_engine = os.environ.get("BLACKHOLE_BENCHMARK_EXPECT_ENGINE", "blackhole")
    quality_tier = os.environ.get("BLACKHOLE_BENCHMARK_QUALITY_TIER", "auto")
    scene_profile = os.environ.get("BLACKHOLE_BENCHMARK_SCENE_PROFILE", "baseline")
    artifact_dir_value = os.environ.get("BLACKHOLE_BENCHMARK_ARTIFACT_DIR", "")
    skip_final_render = os.environ.get("BLACKHOLE_BENCHMARK_SKIP_FINAL_RENDER", "") == "1"
    skip_final_render_reason = os.environ.get("BLACKHOLE_BENCHMARK_SKIP_FINAL_RENDER_REASON", "")
    width = get_env_int("BLACKHOLE_BENCHMARK_WIDTH", 640)
    height = get_env_int("BLACKHOLE_BENCHMARK_HEIGHT", 360)
    measured_frames = get_env_int("BLACKHOLE_BENCHMARK_MEASURED_FRAMES", 4)
    warmup_frames = get_env_int("BLACKHOLE_BENCHMARK_WARMUP_FRAMES", 1)
    report_path = os.environ.get("BLACKHOLE_BENCHMARK_REPORT_JSON", "")
    report = {
        "label": label,
        "scenario": scenario,
        "width": width,
        "height": height,
        "warmup_frames": warmup_frames,
        "measured_frames": measured_frames,
        "expect_engine": expect_engine,
        "quality_tier": quality_tier,
        "scene_profile": scene_profile,
        "available_render_engines": [],
        "bridge_library_path": "",
        "bridge_version": [],
        "bridge_capabilities": {},
        "benchmarks": [],
        "skipped_benchmarks": [],
        "status": "started",
    }

    try:
        addon_utils.enable("blackhole_physics", default_set=False, persistent=False)

        import blackhole_physics  # noqa: F401
        from blackhole_physics import bridge, materials, quality

        artifact_dir = pathlib.Path(artifact_dir_value).resolve() if artifact_dir_value else None
        report["available_render_engines"] = sorted(
            [
                cls.bl_idname
                for cls in bpy.types.RenderEngine.__subclasses__()
                if getattr(cls, "bl_idname", None)
            ]
        )
        report["bridge_library_path"] = bridge.get_library_path() or ""
        if not hasattr(bpy.context.scene, "blackhole"):
            raise RuntimeError("Addon did not register scene.blackhole")
        if not bridge.is_loaded():
            raise RuntimeError("Bridge library did not load inside Blender")
        report["bridge_version"] = list(bridge.get_version_tuple())
        report["bridge_capabilities"] = bridge.get_capabilities()

        scene = ensure_benchmark_scene(width, height, scene_profile)
        target_engine_id = find_engine_id(expect_engine)
        if expect_engine and target_engine_id is None:
            raise RuntimeError(f"Required benchmark render engine '{expect_engine}' is unavailable")
        if expect_engine == "octane":
            suppress_external_scene_lighting(scene)
        report["selected_engine"] = target_engine_id or ""
        report["studio_quality"] = quality.apply_studio_quality(
            scene,
            target_engine=target_engine_id,
            quality_tier=quality_tier,
        )
        if expect_engine == "octane":
            disk_texture_result = bpy.ops.blackhole.render_disk_texture()
            lensing_map_result = bpy.ops.blackhole.render_lensing_map()
            report["disk_texture_result"] = list(disk_texture_result)
            report["lensing_map_result"] = list(lensing_map_result)
            result = bpy.ops.blackhole.setup_octane_materials()
            if "FINISHED" not in result:
                raise RuntimeError(f"setup_octane_materials operator returned {result}")
            report["octane_disk_material_state"] = materials.inspect_octane_disk_material_state()
        total_frames = warmup_frames + measured_frames
        poses = build_orbit_poses(scene, total_frames)
        capabilities = report["bridge_capabilities"]
        captured_images: dict[str, np.ndarray] = {}

        def run_bridge_lensing(_index: int) -> dict[str, object]:
            params = current_params(scene)
            data = bridge.render_lensing_map(
                a_star=scene.blackhole.spin,
                observer_r=params["observer_r"],
                inclination_rad=params["inclination_rad"],
                width=width,
                height=height,
            )
            return {"signature": frame_signature(data), "image": data}

        if scenario in {"all", "bridge_lensing"}:
            result = benchmark_loop(
                name="bridge_lensing_preview",
                backend="bridge_cpu",
                scene=scene,
                poses=poses,
                warmup_frames=warmup_frames,
                measured_frames=measured_frames,
                render_frame=run_bridge_lensing,
                artifact_dir=artifact_dir,
            )
            report["benchmarks"].append(result)
            if result.get("artifact_path"):
                captured_images[result["name"]] = load_image_array(pathlib.Path(result["artifact_path"]))

        lib = bridge.get_lib()

        def run_bridge_cuda(_index: int) -> dict[str, object]:
            params = current_params(scene)
            framebuffer = np.zeros((height, width, 4), dtype=np.float32)
            rc = lib.bhb_cuda_render_raytraced(
                ctypes.c_float(scene.blackhole.spin),
                ctypes.c_float(params["observer_r"]),
                ctypes.c_float(params["inclination_rad"]),
                width,
                height,
                framebuffer.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            )
            if rc != 0:
                raise RuntimeError(f"bhb_cuda_render_raytraced failed with rc={rc}")
            signature = frame_signature(framebuffer)
            signature["rc"] = rc
            return {"signature": signature, "image": framebuffer}

        backplate_name = "BlackholeOctaneBridgeBackplate"

        if scenario in {"all", "bridge_cuda"}:
            if capabilities.get("cuda"):
                report["benchmarks"].append(
                    benchmark_loop(
                        name="bridge_cuda_preview",
                        backend="bridge_cuda",
                        scene=scene,
                        poses=poses,
                        warmup_frames=warmup_frames,
                        measured_frames=measured_frames,
                        render_frame=run_bridge_cuda,
                        artifact_dir=artifact_dir,
                    )
                )
                latest = report["benchmarks"][-1]
                if latest.get("artifact_path"):
                    captured_images[latest["name"]] = load_image_array(pathlib.Path(latest["artifact_path"]))
                    if expect_engine == "octane":
                        upsert_bpy_image_from_array(backplate_name, captured_images[latest["name"]])
                        report["cuda_reset_before_octane"] = bridge.cuda_reset_device()
            else:
                report["skipped_benchmarks"].append(
                    {"name": "bridge_cuda_preview", "reason": "CUDA bridge path unavailable"}
                )

        def run_render_engine(_index: int) -> dict[str, object]:
            render_engine_id = target_engine_id or scene.render.engine
            scene.render.engine = render_engine_id
            render_path = None
            if artifact_dir is not None:
                artifact_dir.mkdir(parents=True, exist_ok=True)
                render_path = artifact_dir / f"{expect_engine}_render_frame.png"
                scene.render.image_settings.file_format = "PNG"
                scene.render.filepath = str(render_path)
            result = bpy.ops.render.render(write_still=render_path is not None, use_viewport=False)
            if "FINISHED" not in result:
                raise RuntimeError(f"Render operator returned {result}")
            pixels: np.ndarray | None = None
            render_result = bpy.data.images.get("Render Result")
            if render_result is not None and len(render_result.pixels) >= width * height * 4:
                pixel_count = width * height * 4
                pixels = np.array(render_result.pixels[:pixel_count], dtype=np.float32).reshape(height, width, 4)
            elif render_path is not None and render_path.exists():
                pixels = load_image_array(render_path)
            if pixels is None:
                signature = {
                    "shape": [height, width, 4],
                    "engine": scene.render.engine,
                    "render_result_access": False,
                }
                pixels = np.zeros((height, width, 4), dtype=np.float32)
            else:
                signature = frame_signature(pixels)
                signature["engine"] = scene.render.engine
                signature["render_result_access"] = True
            return {"signature": signature, "image": pixels}

        if scenario in {"all", "render_engine"}:
            required_engine_available = target_engine_id is not None
            if skip_final_render:
                report["skipped_benchmarks"].append(
                    {"name": "render_engine_final", "reason": skip_final_render_reason or "Final render skipped"}
                )
            elif capabilities.get("cuda") and required_engine_available:
                if expect_engine == "octane":
                    report["native_proxy_render"] = quality.configure_octane_native_proxy_render(
                        scene,
                        quality_tier=quality_tier,
                    )
                    report["benchmarks"].append(
                        benchmark_loop(
                            name="render_engine_native_final",
                            backend="octane_native_proxy",
                            scene=scene,
                            poses=poses,
                            warmup_frames=warmup_frames,
                            measured_frames=measured_frames,
                            render_frame=run_render_engine,
                            artifact_dir=artifact_dir,
                        )
                    )
                    latest = report["benchmarks"][-1]
                    if latest.get("artifact_path"):
                        captured_images[latest["name"]] = load_image_array(pathlib.Path(latest["artifact_path"]))
                    if "bridge_cuda_preview" in captured_images:
                        report["hybrid_backplate"] = quality.configure_octane_cuda_hybrid_compositor(
                            scene,
                            backplate_name,
                            quality_tier=quality_tier,
                        )
                    report["benchmarks"].append(
                        benchmark_loop(
                            name="render_engine_final",
                            backend="octane_hybrid_render_engine",
                            scene=scene,
                            poses=poses,
                            warmup_frames=warmup_frames,
                            measured_frames=measured_frames,
                            render_frame=run_render_engine,
                            artifact_dir=artifact_dir,
                        )
                    )
                    latest = report["benchmarks"][-1]
                    if latest.get("artifact_path"):
                        captured_images[latest["name"]] = load_image_array(pathlib.Path(latest["artifact_path"]))
                else:
                    report["benchmarks"].append(
                        benchmark_loop(
                            name="render_engine_final",
                            backend=f"{expect_engine}_render_engine",
                            scene=scene,
                            poses=poses,
                            warmup_frames=warmup_frames,
                            measured_frames=measured_frames,
                            render_frame=run_render_engine,
                            artifact_dir=artifact_dir,
                        )
                    )
                    latest = report["benchmarks"][-1]
                    if latest.get("artifact_path"):
                        captured_images[latest["name"]] = load_image_array(pathlib.Path(latest["artifact_path"]))
            else:
                reason = f"{expect_engine} render engine unavailable"
                if not capabilities.get("cuda"):
                    reason = "CUDA bridge path unavailable"
                report["skipped_benchmarks"].append({"name": "render_engine_final", "reason": reason})

        report["comparisons"] = []
        comparison_pairs = [
            ("bridge_cuda_preview", "render_engine_final"),
            ("bridge_cuda_preview", "render_engine_native_final"),
            ("render_engine_native_final", "render_engine_final"),
            ("bridge_lensing_preview", "render_engine_final"),
            ("bridge_lensing_preview", "bridge_cuda_preview"),
        ]
        for reference_name, candidate_name in comparison_pairs:
            if reference_name not in captured_images or candidate_name not in captured_images:
                continue
            metrics, heatmap = compute_comparison_metrics(captured_images[reference_name], captured_images[candidate_name])
            comparison_artifact_path = ""
            if artifact_dir is not None:
                comparison_artifact = artifact_dir / f"{build_comparison_artifact_name(reference_name, candidate_name)}.png"
                save_array_png(comparison_artifact, heatmap)
                comparison_artifact_path = str(comparison_artifact)
            report["comparisons"].append(
                {
                    "reference": reference_name,
                    "candidate": candidate_name,
                    "artifact_path": comparison_artifact_path,
                    "metrics": metrics,
                }
            )

        if not report["benchmarks"]:
            raise RuntimeError("No benchmarks were executed successfully")
        report["status"] = "success"
        print(f"[blackhole-benchmark] {label}: success")
        return 0
    except Exception as exc:
        report["status"] = "failure"
        report["error"] = str(exc)
        report["traceback"] = traceback.format_exc()
        raise
    finally:
        if report_path:
            with open(report_path, "w", encoding="utf-8") as handle:
                json.dump(report, handle, indent=2, sort_keys=True)
                handle.write("\n")


if __name__ == "__main__":
    raise SystemExit(main())
