#!/usr/bin/env python3
"""Install and configure Dream Textures for Blender 5.2 or OctaneBlender."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import pathlib
import shutil
import subprocess
import sys


DEFAULT_PACKAGES = (
    "numpy",
    "pillow",
    "huggingface_hub",
    "safetensors",
    "accelerate",
    "transformers",
    "diffusers",
    "opencv-python-headless",
    "onnxruntime-gpu",
)

TORCH_PACKAGES = (
    "torch",
    "torchvision",
)

HOSTS = {
    "blender52": {
        "blender_version": "5.2",
        "python_executable": "python3.14",
        "python_version": "3.14",
        "venv_dir": "~/.cache/blackhole/dream_textures_py314",
        "runtime_mode": "blackhole-py314-venv",
        "readme": "Blender 5.2 Dream Textures runtime uses the Blackhole-managed Python 3.14 venv.\n",
    },
    "octane45": {
        "blender_version": "4.5",
        "python_executable": "python3.11",
        "python_version": "3.11",
        "venv_dir": "~/.cache/blackhole/dream_textures_py311",
        "runtime_mode": "blackhole-py311-venv",
        "readme": "OctaneBlender Dream Textures runtime uses the Blackhole-managed Python 3.11 venv.\n",
    },
}

AUTOMATION_DEPTH_MODEL_ID = "carsonkatri/stable-diffusion-2-depth-diffusers"


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", choices=sorted(HOSTS), required=True)
    parser.add_argument("--addon-source", type=pathlib.Path)
    parser.add_argument("--addon-dir", type=pathlib.Path)
    parser.add_argument("--venv-dir", type=pathlib.Path)
    parser.add_argument("--model-id", default="stabilityai/sdxl-turbo")
    parser.add_argument("--extra-model-id", action="append", default=[])
    parser.add_argument("--json-out", type=pathlib.Path)
    return parser.parse_args(argv)


def run(command: list[str], *, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, check=True, capture_output=True, text=True, env=env)


def resolve_paths(args: argparse.Namespace) -> tuple[dict[str, str], pathlib.Path, pathlib.Path]:
    host = HOSTS[args.host]
    addon_source = args.addon_source
    if addon_source is None:
        addon_source = pathlib.Path(f"/usr/share/blender/5.2/scripts/addons/dream_textures")
    addon_dir = args.addon_dir
    if addon_dir is None:
        addon_dir = pathlib.Path.home() / ".config" / "blender" / host["blender_version"] / "scripts" / "addons" / "dream_textures"
    venv_dir = args.venv_dir
    if venv_dir is None:
        venv_dir = pathlib.Path(host["venv_dir"]).expanduser()
    return host, addon_source.resolve(), addon_dir.resolve(), venv_dir.resolve()


def ensure_addon_copy(addon_source: pathlib.Path, addon_dir: pathlib.Path) -> None:
    if not addon_source.exists():
        raise SystemExit(f"Dream Textures addon source not found: {addon_source}")
    addon_dir.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(addon_source, addon_dir, dirs_exist_ok=True)


def patch_huggingface_hub(addon_dir: pathlib.Path) -> bool:
    target = addon_dir / "generator_process" / "actions" / "huggingface_hub.py"
    if not target.exists():
        raise SystemExit(f"Dream Textures huggingface_hub.py not found: {target}")
    text = target.read_text(encoding="utf-8")
    fallback = (
        "    try:\n"
        "        from diffusers.utils.hub_utils import old_diffusers_cache\n"
        "    except ImportError:\n"
        "        try:\n"
        "            from diffusers.utils.constants import DIFFUSERS_CACHE as old_diffusers_cache\n"
        "        except ImportError:\n"
        "            old_diffusers_cache = HF_HUB_CACHE\n"
    )
    if "DIFFUSERS_CACHE as old_diffusers_cache" in text:
        return False
    needle = (
        "    from diffusers.utils.hub_utils import old_diffusers_cache\n"
    )
    if needle not in text:
        return False
    text = text.replace(needle, fallback, 1)
    target.write_text(text, encoding="utf-8")
    return True


def patch_load_model_fp16_fallback(addon_dir: pathlib.Path) -> bool:
    target = addon_dir / "generator_process" / "actions" / "load_model.py"
    if not target.exists():
        raise SystemExit(f"Dream Textures load_model.py not found: {target}")
    text = target.read_text(encoding="utf-8")
    old = (
        '    if "main" in revisions:\n'
        '        strategies.append({"model_path": revisions["main"], "variant": "fp16" if half_precision else None})\n'
        '        if not half_precision:\n'
        '            # fp16 variant can automatically use fp32 files, but fp32 won\'t automatically use fp16 files\n'
        '            strategies.append({"model_path": revisions["main"], "variant": "fp16", "_warn_precision_fallback": True})\n'
    )
    new = (
        '    if "main" in revisions:\n'
        '        strategies.append({"model_path": revisions["main"], "variant": "fp16" if half_precision else None})\n'
        '        if half_precision:\n'
        '            # Some public diffusers conversions expose only main-weight files.\n'
        '            strategies.append({"model_path": revisions["main"], "_warn_precision_fallback": True})\n'
        '        else:\n'
        '            # fp16 variant can automatically use fp32 files, but fp32 won\'t automatically use fp16 files\n'
        '            strategies.append({"model_path": revisions["main"], "variant": "fp16", "_warn_precision_fallback": True})\n'
    )
    if new in text:
        return False
    if old not in text:
        return False
    text = text.replace(old, new, 1)
    target.write_text(text, encoding="utf-8")
    return True


def ensure_venv(python_executable: str, venv_dir: pathlib.Path) -> pathlib.Path:
    python_path = shutil.which(python_executable)
    if python_path is None:
        raise SystemExit(f"Required Python executable not found: {python_executable}")
    venv_python = venv_dir / "bin" / "python"
    if not venv_python.exists():
        run([python_path, "-m", "venv", str(venv_dir)])
    return venv_python


def imports_present(venv_python: pathlib.Path, modules: tuple[str, ...]) -> dict[str, bool]:
    code = (
        "import importlib.util, json\n"
        f"mods={list(modules)!r}\n"
        "print(json.dumps({m: bool(importlib.util.find_spec(m)) for m in mods}))\n"
    )
    proc = run([str(venv_python), "-c", code])
    return json.loads(proc.stdout)


def ensure_packages(venv_python: pathlib.Path) -> dict[str, object]:
    import_status = imports_present(
        venv_python,
        ("torch", "torchvision", "diffusers", "transformers", "onnxruntime", "cv2", "numpy", "huggingface_hub"),
    )
    installed = []
    if not all(import_status.values()):
        run([str(venv_python), "-m", "pip", "install", "--upgrade", "pip", "setuptools", "wheel"])
        run([str(venv_python), "-m", "pip", "install", *DEFAULT_PACKAGES])
        run([str(venv_python), "-m", "pip", "install", *TORCH_PACKAGES, "--index-url", "https://download.pytorch.org/whl/cu128"])
        installed = [*DEFAULT_PACKAGES, *TORCH_PACKAGES]
        import_status = imports_present(
            venv_python,
            ("torch", "torchvision", "diffusers", "transformers", "onnxruntime", "cv2", "numpy", "huggingface_hub"),
        )
    if not all(import_status.values()):
        raise SystemExit(f"Dream Textures runtime imports still missing: {import_status}")
    return {
        "installed_packages": installed,
        "import_status": import_status,
    }


def ensure_runtime_marker(
    addon_dir: pathlib.Path,
    python_version: str,
    runtime_mode: str,
    readme: str,
    venv_dir: pathlib.Path,
) -> pathlib.Path:
    deps_dir = addon_dir / ".python_dependencies"
    deps_dir.mkdir(parents=True, exist_ok=True)
    for path in deps_dir.iterdir():
        if path.name.endswith(".pth") or "pth" in path.name:
            try:
                path.unlink()
            except FileNotFoundError:
                pass
    pth_name = f"{runtime_mode.replace('/', '_')}.pth"
    site_packages = venv_dir / "lib" / f"python{python_version}" / "site-packages"
    if not site_packages.exists():
        raise SystemExit(f"Dream Textures site-packages path not found: {site_packages}")
    (deps_dir / pth_name).write_text(str(site_packages) + "\n", encoding="utf-8")
    (deps_dir / "README.blackhole.txt").write_text(readme, encoding="utf-8")
    runtime_json = {
        "mode": runtime_mode,
        "site_packages": str(site_packages),
    }
    (deps_dir / "runtime.json").write_text(json.dumps(runtime_json, indent=2) + "\n", encoding="utf-8")
    return site_packages


def ensure_model_cache(venv_python: pathlib.Path, model_id: str) -> dict[str, object]:
    cache_root = pathlib.Path(os.environ.get("HF_HUB_CACHE", pathlib.Path.home() / ".cache" / "huggingface" / "hub")).expanduser()
    repo_folder = "models--" + model_id.replace("/", "--")
    cache_dir = cache_root / repo_folder
    downloaded = False
    snapshot_path = None
    if not cache_dir.exists():
        code = (
            "from huggingface_hub import snapshot_download\n"
            f"path = snapshot_download({model_id!r})\n"
            "print(path)\n"
        )
        proc = run([str(venv_python), "-c", code])
        snapshot_path = proc.stdout.strip()
        downloaded = True
    else:
        refs_main = cache_dir / "refs" / "main"
        if refs_main.exists():
            snapshot = refs_main.read_text(encoding="utf-8").strip()
            snapshot_path = str(cache_dir / "snapshots" / snapshot)
        else:
            snapshot_path = str(cache_dir)
    return {
        "model_id": model_id,
        "cache_dir": str(cache_dir),
        "snapshot_path": snapshot_path,
        "downloaded": downloaded,
    }


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    host, addon_source, addon_dir, venv_dir = resolve_paths(args)
    ensure_addon_copy(addon_source, addon_dir)
    patched = patch_huggingface_hub(addon_dir)
    patched_fp16_fallback = patch_load_model_fp16_fallback(addon_dir)
    venv_python = ensure_venv(host["python_executable"], venv_dir)
    package_info = ensure_packages(venv_python)
    site_packages = ensure_runtime_marker(
        addon_dir,
        host["python_version"],
        host["runtime_mode"],
        host["readme"],
        venv_dir,
    )
    requested_models = [args.model_id, *args.extra_model_id]
    if AUTOMATION_DEPTH_MODEL_ID not in requested_models:
        requested_models.append(AUTOMATION_DEPTH_MODEL_ID)
    unique_models: list[str] = []
    for model_id in requested_models:
        if model_id not in unique_models:
            unique_models.append(model_id)
    model_infos = [ensure_model_cache(venv_python, model_id) for model_id in unique_models]
    model_info = next(info for info in model_infos if info["model_id"] == args.model_id)
    report = {
        "host": args.host,
        "addon_source": str(addon_source),
        "addon_dir": str(addon_dir),
        "venv_dir": str(venv_dir),
        "venv_python": str(venv_python),
        "site_packages": str(site_packages),
        "runtime_mode": host["runtime_mode"],
        "patched_huggingface_hub": patched,
        "patched_fp16_fallback": patched_fp16_fallback,
        "model_id": args.model_id,
        "model_cache": model_info,
        "model_caches": model_infos,
        **package_info,
    }
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
