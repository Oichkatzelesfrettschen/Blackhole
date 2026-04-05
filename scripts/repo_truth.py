#!/usr/bin/env python3
"""Generate a measured repo-truth report for the current source/build tree."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import re
import shutil
import subprocess
import sys
from typing import Any


INTERESTING_CACHE_KEYS = (
    "CMAKE_BUILD_TYPE",
    "CMAKE_CXX_STANDARD",
    "ENABLE_WERROR",
    "ENABLE_CUDA",
    "ENABLE_BLENDER_BRIDGE",
    "ENABLE_DESKTOP_VARIANTS",
    "ENABLE_RMLUI",
    "ENABLE_DESKTOP_APP",
    "ENABLE_BENCHMARKS",
    "ENABLE_GOOGLE_BENCHMARK",
    "ENABLE_MIMALLOC",
    "ENABLE_DOXYGEN",
    "ENABLE_DOXYGEN_WARN_AS_ERROR",
    "ENABLE_TOOLS",
    "BUILD_TESTING",
)

INTERESTING_PACKAGES = (
    "blender-git-nvidia",
    "blender-mcp-git",
    "octane-blender-prime",
    "octane-server-prime",
    "cuda",
    "cudnn",
    "cutensor",
    "nccl",
    "nsight-compute",
    "nsight-systems",
    "nvidia-utils",
    "opencl-nvidia",
    "optix-dev-headers",
    "renderdoc",
    "shaderc",
    "spirv-cross",
    "spirv-tools",
    "glslang",
    "vulkan-tools",
    "vulkan-validation-layers",
    "tensorrt",
)

TOOL_COMMANDS = (
    "blender",
    "OctaneBlender",
    "blender-mcp",
    "nvcc",
    "nvidia-smi",
    "glslangValidator",
    "glslc",
    "spirv-val",
    "spirv-cross",
    "doxygen",
    "dot",
    "vulkaninfo",
    "renderdoccmd",
    "ncu",
    "nsys",
    "cuobjdump",
    "nvdisasm",
    "ptxas",
    "compute-sanitizer",
    "cuda-gdb",
)

REPORT_FILENAMES = {
    "dream_textures_blender_install": "dream_textures_blender_install.json",
    "dream_textures_blender_report": "dream_textures_blender_verified.json",
    "dream_textures_blender_direct_report": "dream_textures_blender_direct_verified.json",
    "dream_textures_blender_background_direct_report": "dream_textures_blender_background_direct_verified.json",
    "dream_textures_blender_conditioned_direct_report": "dream_textures_blender_conditioned_direct_verified.json",
    "dream_textures_blender_depth_direct_report": "dream_textures_blender_depth_direct_verified.json",
    "dream_textures_blender_image_depth_direct_report": "dream_textures_blender_image_depth_direct_verified.json",
    "dream_textures_blender_conditioning_sweep_report": "dream_textures_blender_conditioning_sweep_verified.json",
    "dream_textures_blender_harsh_conditioning_sweep_report": "dream_textures_blender_harsh_conditioning_sweep_verified.json",
    "dream_textures_blender_conditioning_policy_report": "dream_textures_blender_conditioning_policy.json",
    "dream_textures_blender_harsh_conditioning_policy_report": "dream_textures_blender_harsh_conditioning_policy.json",
    "dream_textures_blender_policy_generation_report": "dream_textures_blender_policy_generation_verified.json",
    "dream_textures_blender_policy_background_report": "dream_textures_blender_policy_background_prepare_verified.json",
    "dream_textures_blender_policy_production_report": "dream_textures_blender_policy_production_prepare_verified.json",
    "dream_textures_blender_policy_stale_refresh_report": "dream_textures_blender_policy_stale_refresh_verified.json",
    "dream_textures_octane_install": "dream_textures_octane_install.json",
    "dream_textures_octane_report": "dream_textures_octane_verified.json",
    "dream_textures_octane_direct_report": "dream_textures_octane_direct_verified.json",
    "dream_textures_octane_background_direct_report": "dream_textures_octane_background_direct_verified.json",
    "dream_textures_octane_conditioned_direct_report": "dream_textures_octane_conditioned_direct_verified.json",
    "dream_textures_octane_depth_direct_report": "dream_textures_octane_depth_direct_verified.json",
    "dream_textures_octane_image_depth_direct_report": "dream_textures_octane_image_depth_direct_verified.json",
    "dream_textures_octane_conditioning_sweep_report": "dream_textures_octane_conditioning_sweep_verified.json",
    "dream_textures_octane_harsh_conditioning_sweep_report": "dream_textures_octane_harsh_conditioning_sweep_verified.json",
    "dream_textures_octane_conditioning_policy_report": "dream_textures_octane_conditioning_policy.json",
    "dream_textures_octane_harsh_conditioning_policy_report": "dream_textures_octane_harsh_conditioning_policy.json",
    "dream_textures_octane_policy_generation_report": "dream_textures_octane_policy_generation_verified.json",
    "dream_textures_octane_policy_background_report": "dream_textures_octane_policy_background_prepare_verified.json",
    "dream_textures_octane_policy_production_report": "dream_textures_octane_policy_production_prepare_verified.json",
    "dream_textures_octane_policy_stale_refresh_report": "dream_textures_octane_policy_stale_refresh_verified.json",
    "dream_textures_conditioning_parity_report": "dream_textures_conditioning_baseline_parity.json",
    "dream_textures_harsh_conditioning_parity_report": "dream_textures_conditioning_harsh_parity.json",
    "dream_textures_conditioning_trends_report": "dream_textures_conditioning_trends.json",
    "blender_showcase_render": "blender_showcase_render.json",
    "octane_showcase_render": "octane_showcase_render.json",
    "blender_addon_manifest": "blender_addon_manifest.json",
    "blender_bridge_abi": "blender_bridge_abi.json",
    "blender_addon_package": "blender_addon_package.json",
    "blender_addon_stage": "blender_addon_stage.json",
    "blender_smoke": "blender_smoke.json",
    "blender_smoke_report": "blender_smoke_verified.json",
    "blender_interactive_benchmark": "blender_interactive_benchmark.json",
    "blender_interactive_benchmark_report": "blender_interactive_benchmark_verified.json",
    "blender_harsh_benchmark": "blender_harsh_benchmark.json",
    "blender_harsh_benchmark_report": "blender_harsh_benchmark_verified.json",
    "octane_readiness": "octane_readiness.json",
    "octane_interactive_benchmark": "octane_interactive_benchmark.json",
    "octane_interactive_benchmark_report": "octane_interactive_benchmark_verified.json",
    "octane_harsh_benchmark": "octane_harsh_benchmark.json",
    "octane_harsh_benchmark_report": "octane_harsh_benchmark_verified.json",
    "octane_quality_sweep": "octane_quality_sweep.json",
    "octane_quality_sweep_report": "octane_quality_sweep_verified.json",
    "octane_smoke": "octane_smoke.json",
    "octane_smoke_report": "octane_smoke_verified.json",
}


def run_command(command: list[str], timeout_seconds: float = 10.0) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode("utf-8", errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return subprocess.CompletedProcess(command, 124, stdout=stdout, stderr=stderr)


def parse_cmake_cache(cache_path: pathlib.Path) -> dict[str, str]:
    cache: dict[str, str] = {}
    if not cache_path.exists():
        return cache
    for line in cache_path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith(("//", "#")) or "=" not in line:
            continue
        left, value = line.split("=", 1)
        if ":" not in left:
            continue
        name, _type_name = left.split(":", 1)
        cache[name] = value
    return cache


def parse_ctest_listing(build_dir: pathlib.Path) -> dict[str, Any]:
    names: list[str] = []
    total = 0
    ctest = shutil.which("ctest")
    if ctest is None:
        return {"available": False, "total": 0, "tests": [], "raw_output": ""}

    proc = run_command([ctest, "--test-dir", str(build_dir), "-N"])
    output = proc.stdout.strip()
    test_pattern = re.compile(r"^\s*Test\s+#?\d+:\s+(.+?)\s*$")
    total_pattern = re.compile(r"^Total Tests:\s+(\d+)\s*$")
    for line in output.splitlines():
        test_match = test_pattern.match(line)
        if test_match:
            names.append(test_match.group(1))
            continue
        total_match = total_pattern.match(line)
        if total_match:
            total = int(total_match.group(1))
    if total == 0:
        total = len(names)
    return {
        "available": proc.returncode == 0,
        "returncode": proc.returncode,
        "total": total,
        "tests": names,
        "raw_output": output,
    }


def load_presets(presets_path: pathlib.Path) -> list[dict[str, Any]]:
    if not presets_path.exists():
        return []
    raw = json.loads(presets_path.read_text(encoding="utf-8"))
    presets = raw.get("configurePresets", [])
    output: list[dict[str, Any]] = []
    for preset in presets:
        if preset.get("hidden"):
            continue
        cache_vars = preset.get("cacheVariables", {})
        output.append(
            {
                "name": preset.get("name"),
                "displayName": preset.get("displayName", preset.get("name")),
                "description": preset.get("description", ""),
                "binaryDir": preset.get("binaryDir", ""),
                "cacheVariables": {
                    key: cache_vars[key]
                    for key in (
                        "CMAKE_BUILD_TYPE",
                        "ENABLE_CUDA",
                        "ENABLE_BLENDER_BRIDGE",
                        "ENABLE_DESKTOP_VARIANTS",
                        "ENABLE_DESKTOP_APP",
                        "ENABLE_BENCHMARKS",
                        "ENABLE_GOOGLE_BENCHMARK",
                        "ENABLE_MIMALLOC",
                        "ENABLE_DOXYGEN",
                        "ENABLE_TOOLS",
                        "BUILD_TESTING",
                        "ENABLE_RMLUI",
                        "ENABLE_WERROR",
                    )
                    if key in cache_vars
                },
            }
        )
    return output


def detect_tools() -> dict[str, dict[str, Any]]:
    tools: dict[str, dict[str, Any]] = {}
    for command in TOOL_COMMANDS:
        path = shutil.which(command)
        tool_info: dict[str, Any] = {"path": path}
        if path is None:
            tools[command] = tool_info
            continue
        version_output = ""
        if command in {"blender", "OctaneBlender"}:
            proc = run_command([command, "--version"])
            version_output = proc.stdout.splitlines()[0] if proc.stdout else ""
        elif command == "nvcc":
            proc = run_command([command, "--version"])
            lines = proc.stdout.splitlines()
            version_output = next((line.strip() for line in lines if "release" in line), "")
        elif command == "nvidia-smi":
            proc = run_command([command, "--query-gpu=name,driver_version", "--format=csv,noheader"])
            version_output = proc.stdout.strip()
        else:
            proc = run_command([command, "--version"])
            version_output = (proc.stdout or proc.stderr).splitlines()[0] if (proc.stdout or proc.stderr) else ""
        tool_info["returncode"] = proc.returncode
        tool_info["timed_out"] = proc.returncode == 124
        tool_info["version"] = version_output
        tools[command] = tool_info
    return tools


def detect_packages() -> dict[str, str]:
    pacman = shutil.which("pacman")
    if pacman is None:
        return {}
    packages: dict[str, str] = {}
    for package in INTERESTING_PACKAGES:
        proc = run_command([pacman, "-Q", package])
        if proc.returncode != 0:
            continue
        line = proc.stdout.strip()
        if not line:
            continue
        parts = line.split(maxsplit=1)
        if len(parts) == 2:
            packages[parts[0]] = parts[1]
    return packages


def detect_declared_cxx_standard(source_dir: pathlib.Path) -> str | None:
    cmake_lists = source_dir / "CMakeLists.txt"
    if not cmake_lists.exists():
        return None
    text = cmake_lists.read_text(encoding="utf-8")
    match = re.search(r"set\(BLACKHOLE_CXX_STANDARD\s+(\d+)\)", text)
    if match:
        return match.group(1)
    return None


def load_optional_report(path: pathlib.Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def summarize_configured_build(cache: dict[str, str], source_dir: pathlib.Path) -> dict[str, str]:
    summary = {key: cache.get(key, "UNSET") for key in INTERESTING_CACHE_KEYS}
    if summary["CMAKE_CXX_STANDARD"] == "UNSET":
        blackhole_standard = cache.get("BLACKHOLE_CXX_STANDARD") or detect_declared_cxx_standard(source_dir)
        if blackhole_standard:
            summary["CMAKE_CXX_STANDARD"] = blackhole_standard
    return summary


def render_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Repo Truth Report")
    lines.append("")
    lines.append(f"- Generated: `{report['generated_at']}`")
    lines.append(f"- Source directory: `{report['source_dir']}`")
    lines.append(f"- Build directory: `{report['build_dir']}`")
    lines.append("")
    lines.append("## Configured Build")
    lines.append("")
    for key, value in report["configured_build"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## CTest Inventory")
    lines.append("")
    ctest = report["ctest"]
    lines.append(f"- `ctest -N` available: `{ctest['available']}`")
    lines.append(f"- Total tests: `{ctest['total']}`")
    if ctest["tests"]:
        lines.append("- Test names:")
        for name in ctest["tests"]:
            lines.append(f"  - `{name}`")
    lines.append("")
    lines.append("## Configure Presets")
    lines.append("")
    for preset in report["configure_presets"]:
        lines.append(f"### `{preset['name']}`")
        lines.append("")
        if preset["description"]:
            lines.append(f"- Description: {preset['description']}")
        if preset["binaryDir"]:
            lines.append(f"- Binary dir: `{preset['binaryDir']}`")
        if preset["cacheVariables"]:
            for key, value in preset["cacheVariables"].items():
                lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.append("## Local Toolchain")
    lines.append("")
    for command, info in report["tools"].items():
        if info["path"] is None:
            continue
        lines.append(f"- `{command}`: `{info['path']}`")
        if info.get("version"):
            lines.append(f"  - Version: `{info['version']}`")
    lines.append("")
    if report["packages"]:
        lines.append("## Local Packages")
        lines.append("")
        for package, version in report["packages"].items():
            lines.append(f"- `{package}`: `{version}`")
        lines.append("")
    generated_reports = report.get("generated_reports", {})
    if generated_reports:
        lines.append("## Generated Reports")
        lines.append("")
        for name, payload in generated_reports.items():
            if payload is None:
                continue
            lines.append(f"### `{name}`")
            lines.append("")
            if name == "blender_bridge_abi":
                lines.append(
                    f"- Missing Python exports: `{len(payload.get('missing_python_exports', []))}`"
                )
                lines.append(
                    f"- Missing header exports: `{len(payload.get('missing_header_exports', []))}`"
                )
                lines.append(
                    f"- Missing ctypes argtypes: `{len(payload.get('missing_argtypes', []))}`"
                )
            elif name == "blender_addon_package":
                lines.append(f"- File count: `{payload.get('file_count', 0)}`")
                lines.append(f"- Zip sha256: `{payload.get('zip_sha256', '')}`")
                bl_info = payload.get("bl_info", {})
                if bl_info:
                    lines.append(f"- Addon version: `{bl_info.get('version', [])}`")
                    lines.append(f"- Blender minimum: `{bl_info.get('blender', [])}`")
            elif name == "blender_addon_manifest":
                lines.append(f"- File count: `{payload.get('file_count', 0)}`")
                lines.append(f"- Zip sha256: `{payload.get('zip_sha256', '')}`")
            elif name == "blender_addon_stage":
                lines.append(f"- Target dir: `{payload.get('target_dir', '')}`")
                lines.append(f"- File count: `{payload.get('file_count', 0)}`")
            elif name in {"blender_smoke", "octane_smoke"}:
                lines.append(f"- Return code: `{payload.get('returncode', -1)}`")
                inner = payload.get("inner_report", {})
                if inner:
                    lines.append(f"- Status: `{inner.get('status', '')}`")
                    lines.append(f"- Selected engine: `{inner.get('selected_engine', '')}`")
                    lines.append(f"- Bridge path: `{inner.get('bridge_library_path', '')}`")
            elif name in {"blender_smoke_report", "octane_smoke_report"}:
                inner = payload.get("inner_report", {})
                lines.append(f"- Return code: `{payload.get('returncode', -1)}`")
                lines.append(f"- Status: `{inner.get('status', '')}`")
            elif name == "octane_readiness":
                lines.append(f"- Return code: `{payload.get('returncode', -1)}`")
                lines.append(f"- Classification: `{payload.get('readiness', '')}`")
                lines.append(f"- Ready for automation: `{bool(payload.get('ready_for_automation', False))}`")
                lines.append(f"- Reason: `{payload.get('reason', '')}`")
            elif name in {
                "blender_interactive_benchmark",
                "blender_interactive_benchmark_report",
                "blender_harsh_benchmark",
                "blender_harsh_benchmark_report",
                "octane_interactive_benchmark",
                "octane_interactive_benchmark_report",
                "octane_harsh_benchmark",
                "octane_harsh_benchmark_report",
            }:
                inner = payload.get("inner_report", {})
                benchmarks = inner.get("benchmarks", [])
                mcp_scene = payload.get("mcp_scene_report", {})
                lines.append(f"- Return code: `{payload.get('returncode', -1)}`")
                lines.append(f"- Status: `{inner.get('status', '')}`")
                lines.append(f"- Resolution: `{inner.get('width', 0)}x{inner.get('height', 0)}`")
                lines.append(f"- Expected engine: `{payload.get('expect_engine', '')}`")
                if mcp_scene:
                    final_scene = mcp_scene.get("final_scene_info", {}).get("result", {})
                    lines.append(f"- MCP scene enabled: `{bool(payload.get('mcp_scene_enabled', False))}`")
                    lines.append(f"- MCP scene objects: `{final_scene.get('object_count', 0)}`")
                octane_readiness = payload.get("octane_readiness", {})
                if octane_readiness:
                    lines.append(f"- Octane readiness: `{octane_readiness.get('readiness', '')}`")
                    lines.append(f"- Octane ready for automation: `{bool(octane_readiness.get('ready_for_automation', False))}`")
                lines.append(f"- Benchmarks: `{len(benchmarks)}`")
                for benchmark in benchmarks:
                    metrics = benchmark.get("metrics", {})
                    quality_metrics = benchmark.get("quality_metrics", {})
                    lines.append(
                        f"  - `{benchmark.get('name', '')}` median `{metrics.get('median_ms', 0.0):.3f}` ms / `{metrics.get('median_fps', 0.0):.3f}` FPS"
                    )
                    lines.append(
                        f"    artifact `{benchmark.get('artifact_path', '')}` max-luma `{quality_metrics.get('max_luma', 0.0):.4f}` edge `{quality_metrics.get('edge_energy', 0.0):.4f}`"
                    )
            elif name in {"octane_quality_sweep", "octane_quality_sweep_report"}:
                lines.append(f"- Tiers: `{payload.get('tiers', [])}`")
                for tier_name, tier_payload in payload.get("results", {}).items():
                    summary = tier_payload.get("summary", {})
                    octane = summary.get("octane_settings", {})
                    final_metrics = summary.get("final_metrics", {})
                    comparison = summary.get("preview_to_final_comparison", {})
                    lines.append(
                        f"  - `{tier_name}` rc `{tier_payload.get('returncode', -1)}` "
                        f"max-samples `{octane.get('max_samples', '')}` "
                        f"noise `{octane.get('adaptive_noise_threshold', '')}` "
                        f"final `{final_metrics.get('median_ms', 0.0):.3f}` ms "
                        f"psnr `{comparison.get('psnr_rgb', 0.0):.3f}`"
                    )
            elif name in {"dream_textures_blender_report", "dream_textures_octane_report"}:
                inner = payload.get("inner_report", {})
                lines.append(
                    f"- `{name}` status `{inner.get('status', '')}` device `{inner.get('device', '')}` "
                    f"shape `{inner.get('shape', [])}` mean `{inner.get('mean', 0.0):.6f}`"
                )
            elif name in {
                "dream_textures_blender_direct_report",
                "dream_textures_octane_direct_report",
                "dream_textures_blender_background_direct_report",
                "dream_textures_octane_background_direct_report",
                "dream_textures_blender_conditioned_direct_report",
                "dream_textures_octane_conditioned_direct_report",
                "dream_textures_blender_depth_direct_report",
                "dream_textures_octane_depth_direct_report",
                "dream_textures_blender_image_depth_direct_report",
                "dream_textures_octane_image_depth_direct_report",
            }:
                inner = payload.get("inner_report", {})
                lines.append(
                    f"- `{name}` status `{inner.get('status', '')}` backend `{inner.get('selected_backend', '')}` "
                    f"slot `{inner.get('slot', '')}` image `{inner.get('image_name', '')}` "
                    f"conditioning `{inner.get('conditioning_policy', {}).get('effective_mode', 'text_to_image')}` "
                    f"shape `{inner.get('shape', [])}` mean `{inner.get('mean', 0.0):.6f}` "
                    f"hash `{inner.get('asset_digest', {}).get('sha256', '')[:12]}`"
                )
            elif name in {
                "dream_textures_blender_conditioning_sweep_report",
                "dream_textures_octane_conditioning_sweep_report",
                "dream_textures_blender_harsh_conditioning_sweep_report",
                "dream_textures_octane_harsh_conditioning_sweep_report",
            }:
                lines.append(
                    f"- Scene `{payload.get('scene_profile', '')}` modes `{payload.get('modes', [])}` "
                    f"memory `{payload.get('memory_profile', '')}`"
                )
                for comparison in payload.get("comparisons", []):
                    metrics = comparison.get("metrics", {})
                    lines.append(
                        f"  - `{comparison.get('candidate', '')}` vs `{comparison.get('reference', '')}` "
                        f"psnr `{metrics.get('psnr_rgb', 0.0):.3f}` "
                        f"luma-cos `{metrics.get('luma_cosine_similarity', 0.0):.6f}`"
                    )
            elif name in {
                "dream_textures_blender_conditioning_policy_report",
                "dream_textures_blender_harsh_conditioning_policy_report",
                "dream_textures_octane_conditioning_policy_report",
                "dream_textures_octane_harsh_conditioning_policy_report",
            }:
                lines.append(
                    f"- Host `{payload.get('host_label', '')}` scene `{payload.get('scene_profile', '')}` "
                    f"interactive `{payload.get('recommended_interactive_mode', '')}` "
                    f"production `{payload.get('recommended_production_mode', '')}`"
                )
                elapsed = payload.get("elapsed_seconds", {})
                lines.append(
                    f"  - image `{elapsed.get('image', 0.0):.3f}` s depth `{elapsed.get('depth', 0.0):.3f}` s "
                    f"image_depth `{elapsed.get('image_depth', 0.0):.3f}` s"
                )
            elif name in {
                "dream_textures_blender_policy_generation_report",
                "dream_textures_blender_policy_background_report",
                "dream_textures_blender_policy_production_report",
                "dream_textures_octane_policy_generation_report",
                "dream_textures_octane_policy_background_report",
                "dream_textures_octane_policy_production_report",
                "dream_textures_blender_policy_stale_refresh_report",
                "dream_textures_octane_policy_stale_refresh_report",
            }:
                cold = payload.get("cold_prepare", {})
                warm = payload.get("warm_prepare", {})
                stale = payload.get("stale_prepare", {})
                lines.append(
                    f"- Host policy slot `{payload.get('slot', '')}` intent `{payload.get('intent', '')}` "
                    f"resolved `{warm.get('resolved_mode', cold.get('resolved_mode', ''))}` "
                    f"cold `{cold.get('timing', {}).get('total_seconds', 0.0):.3f}` s "
                    f"warm `{warm.get('timing', {}).get('total_seconds', 0.0):.3f}` s "
                    f"warm reused `{warm.get('preparation_summary', {}).get('reused', 0)}`"
                )
                if stale:
                    lines.append(
                        f"  - stale `{stale.get('timing', {}).get('total_seconds', 0.0):.3f}` s "
                        f"updated `{stale.get('preparation_summary', {}).get('updated', 0)}` "
                        f"created `{stale.get('preparation_summary', {}).get('created', 0)}` "
                        f"resolved `{stale.get('resolved_mode', '')}`"
                    )
            elif name in {
                "dream_textures_conditioning_parity_report",
                "dream_textures_harsh_conditioning_parity_report",
            }:
                lines.append(
                    f"- Scene `{payload.get('scene_profile', '')}` memory `{payload.get('memory_profile', '')}`"
                )
                for mode_parity in payload.get("mode_parity", []):
                    lines.append(
                        f"  - mode `{mode_parity.get('mode', '')}` mean-delta `{mode_parity.get('mean_delta', 0.0):.6f}`"
                    )
            elif name == "dream_textures_conditioning_trends_report":
                for scene_name, scene_payload in payload.get("scenes", {}).items():
                    lines.append(
                        f"- Scene `{scene_name}` consensus interactive `{scene_payload.get('consensus_interactive_mode', '')}` "
                        f"production `{scene_payload.get('consensus_production_mode', '')}`"
                    )
                    parity = scene_payload.get("parity", {})
                    lines.append(
                        f"  - max mean delta `{parity.get('max_mode_mean_delta', 0.0):.6f}` "
                        f"max psnr delta `{parity.get('max_psnr_rgb_delta', 0.0):.6f}`"
                    )
            elif name in {"blender_showcase_render", "octane_showcase_render"}:
                lines.append(
                    f"- Showcase status `{payload.get('status', '')}` engine `{payload.get('selected_engine', '')}`"
                )
                for item in payload.get("scenes", []):
                    lines.append(
                        f"  - `{item.get('scene_profile', '')}` path `{item.get('render_path', '')}` "
                        f"median `{item.get('render_metrics', {}).get('median_ms', 0.0):.3f}` ms "
                        f"psnr `{item.get('comparison_metrics', {}).get('psnr_rgb', 0.0):.3f}`"
                    )
            lines.append("")
    return "\n".join(lines).strip() + "\n"


def build_report(source_dir: pathlib.Path, build_dir: pathlib.Path) -> dict[str, Any]:
    cache = parse_cmake_cache(build_dir / "CMakeCache.txt")
    report = {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_dir": str(source_dir),
        "build_dir": str(build_dir),
        "configured_build": summarize_configured_build(cache, source_dir),
        "ctest": parse_ctest_listing(build_dir),
        "configure_presets": load_presets(source_dir / "CMakePresets.json"),
        "tools": detect_tools(),
        "packages": detect_packages(),
        "generated_reports": {
            name: load_optional_report(build_dir / "reports" / filename)
            for name, filename in REPORT_FILENAMES.items()
        },
    }
    return report


def write_output(path: pathlib.Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True, type=pathlib.Path)
    parser.add_argument("--build-dir", required=True, type=pathlib.Path)
    parser.add_argument("--json-out", required=True, type=pathlib.Path)
    parser.add_argument("--md-out", required=True, type=pathlib.Path)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report = build_report(args.source_dir.resolve(), args.build_dir.resolve())
    write_output(args.json_out.resolve(), json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_output(args.md_out.resolve(), render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
