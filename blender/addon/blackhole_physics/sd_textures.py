# sd_textures.py -- Generative texture synthesis for the Blackhole addon.
#
# WHY: Generates physically-inspired accretion disk and starfield background textures
#      and feeds them into Blender images consumed by Blackhole materials
#      ("BlackholeDiskTexture", world environment) and the CUDA render engine.
#
# WHAT:
#   Backend A -- stable-diffusion.cpp subprocess:
#     Calls the 'sd' binary (stable-diffusion.cpp-cublas-git) with a .gguf model path.
#     Out-of-process: zero CUDA context conflict with the Blackhole CUDA kernel.
#     Writes a temporary PNG; reads it back via bpy.data.images.load().
#
#   Backend B -- python-diffusers (HuggingFace):
#     Uses StableDiffusionPipeline with a local model directory or HF model ID.
#     Pipeline is cached across calls to avoid reload overhead (~10 s cold-start).
#     Requires the 'diffusers' and 'torch' packages inside Blender's Python environment.
#   Backend C -- Dream Textures:
#     Uses Blender's Dream Textures addon and its background Generator actor.
#     Supports seamless tiling for the accretion disk lane and leaves room for
#     future image/depth-conditioned refinement driven by Blackhole render passes.
#
# HOW:
#   generate(props)               -> np.ndarray (H, W, 4) float32, sRGB
#   build_prompt(props)           -> str  (physics-conditioned prompt for inspection)
#   build_negative_prompt(props)  -> str
#   available_backends()          -> list[str]

from __future__ import annotations

import hashlib
import importlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
from typing import Any, Protocol

import bpy
import numpy as np


# ---------------------------------------------------------------------------
# _SDProps Protocol
#
# WHY: Decouples sd_textures from bpy.types.PropertyGroup.
#   - Enables pyright to typecheck this module without bpy stubs.
#   - Lets the pytest suite pass a dataclass mock instead of a Blender object.
#   - Makes the consumed interface explicit: if BlackholeProperties renames a
#     field, pyright will flag the Protocol mismatch immediately.
# ---------------------------------------------------------------------------
class _SDProps(Protocol):
    """Minimal interface consumed by sd_textures -- structurally satisfied by
    BlackholeProperties (panels.py) and by the pytest dataclass mock."""

    sd_model_path: str
    sd_target_slot: str     # "disk" | "background"
    sd_backend: str         # "auto" | "sd_cpp" | "diffusers"
    sd_prompt_prefix: str
    sd_negative_prompt: str
    sd_steps: int
    sd_seed: int
    sd_guidance_scale: float
    sd_prompt_style: str    # "scientific" | "hybrid" | "cinematic"
    sd_conditioning_mode: str
    sd_conditioning_strength: float
    texture_width: int
    texture_height: int
    spin: float             # Kerr spin parameter a* in [0, 1) -- used for prompt conditioning
    inclination_deg: float
    mass_msun: float
    mdot_edd: float


# ---------------------------------------------------------------------------
# Pipeline cache for the diffusers backend (avoids reload on every generate).
# Keyed by (model_id, device_str) so a model change forces a fresh load.
# ---------------------------------------------------------------------------
_diffusers_cache: dict[tuple[str, str], Any] = {}
PROMPT_CHARACTER_BUDGET = 320
OFFICIAL_DEPTH_MODEL_ID = "stabilityai/stable-diffusion-2-depth"
AUTOMATION_DEPTH_MODEL_ID = "carsonkatri/stable-diffusion-2-depth-diffusers"
AUTO_INTERACTIVE_MODE = "auto_interactive"
AUTO_PRODUCTION_MODE = "auto_production"


def available_backends() -> list[str]:
    """Return which backends can actually run on this machine."""
    result = []
    if shutil.which("sd") is not None:
        result.append("sd_cpp")
    if _dream_textures_available():
        result.append("dream_textures")
    try:
        import diffusers  # noqa: F401 -- existence check only
        result.append("diffusers")
    except ImportError:
        pass
    return result


def _dream_textures_available() -> bool:
    """Return whether Blender can load the Dream Textures addon."""
    try:
        import addon_utils
    except ImportError:
        addon_utils = None  # type: ignore[assignment]

    if addon_utils is not None:
        try:
            for mod in addon_utils.modules():
                if getattr(mod, "__name__", "") == "dream_textures":
                    return True
        except Exception:
            pass
        try:
            loaded_default, loaded_enabled = addon_utils.check("dream_textures")
            if loaded_default or loaded_enabled:
                return True
        except Exception:
            pass

    return importlib.util.find_spec("dream_textures") is not None


def _enable_dream_textures() -> None:
    """Enable the Dream Textures addon when running inside Blender."""
    try:
        import addon_utils
    except ImportError as exc:
        raise RuntimeError("Dream Textures requires Blender addon support") from exc

    try:
        addon_utils.enable("dream_textures", default_set=False, persistent=False)
    except Exception as exc:
        raise RuntimeError(f"Failed to enable Dream Textures: {exc}") from exc


def _format_parameter(label: str, value: float, unit: str = "") -> str:
    """Format a short scientific parameter token for prompt injection."""
    suffix = f" {unit}" if unit else ""
    if abs(value) >= 1000.0:
        return f"{label}={value:.3e}{suffix}"
    if abs(value) >= 100.0:
        return f"{label}={value:.1f}{suffix}"
    return f"{label}={value:.3f}{suffix}"


def _style_terms(style: str, slot: str) -> list[str]:
    """Return style-specific prompt qualifiers for the selected target slot."""
    if slot == "disk":
        table = {
            "scientific": [
                "scientific visualization",
                "emission map",
            ],
            "hybrid": [
                "scientific visualization",
                "cinematic plasma glow",
            ],
            "cinematic": [
                "cinematic astrophotography",
                "dramatic relativistic plasma filaments",
            ],
        }
    else:
        table = {
            "scientific": [
                "astronomical survey mosaic",
                "point-like stars",
                "clean background plate",
            ],
            "hybrid": [
                "astronomical survey mosaic",
                "JWST-inspired deep field look",
                "lookdev-ready environment plate",
            ],
            "cinematic": [
                "epic deep-space panorama",
                "high dynamic range sky plate",
                "cinematic nebular backscatter",
            ],
        }
    return table.get(style, table["scientific"])


def _seed_policy(seed: int) -> dict[str, Any]:
    """Describe how the current generation seed will behave."""
    if seed < 0:
        return {
            "mode": "randomized",
            "requested_seed": seed,
            "effective_seed": None,
            "deterministic": False,
        }
    return {
        "mode": "fixed",
        "requested_seed": seed,
        "effective_seed": seed,
        "deterministic": True,
    }


def _prompt_budget(prompt: str, negative_prompt: str) -> dict[str, Any]:
    """Summarize prompt footprint for reproducibility and drift checks."""
    prompt_chars = len(prompt)
    negative_chars = len(negative_prompt)
    total_chars = prompt_chars + negative_chars
    warnings: list[str] = []
    if prompt_chars > PROMPT_CHARACTER_BUDGET:
        warnings.append(
            f"prompt_exceeds_budget:{prompt_chars}>{PROMPT_CHARACTER_BUDGET}"
        )
    return {
        "character_budget": PROMPT_CHARACTER_BUDGET,
        "prompt_characters": prompt_chars,
        "negative_prompt_characters": negative_chars,
        "total_characters": total_chars,
        "prompt_terms": len([part for part in prompt.split(",") if part.strip()]),
        "negative_prompt_terms": len(
            [part for part in negative_prompt.split(",") if part.strip()]
        ),
        "within_budget": prompt_chars <= PROMPT_CHARACTER_BUDGET,
        "warnings": warnings,
    }


def _model_cache_state(model_id: str) -> dict[str, Any]:
    """Describe where the selected model resolves from on this machine."""
    model_path = pathlib.Path(model_id).expanduser()
    if model_path.is_file():
        return {
            "kind": "local_file",
            "exists": True,
            "path": str(model_path.resolve()),
        }
    if model_path.is_dir():
        return {
            "kind": "local_directory",
            "exists": True,
            "path": str(model_path.resolve()),
        }
    if "/" in model_id:
        cache_dir = pathlib.Path.home() / ".cache" / "huggingface" / "hub" / (
            "models--" + model_id.replace("/", "--")
        )
        snapshots_dir = cache_dir / "snapshots"
        snapshot_paths: list[pathlib.Path] = []
        if snapshots_dir.exists():
            snapshot_paths = sorted(
                path for path in snapshots_dir.iterdir()
                if path.is_dir()
            )
        snapshot_path = snapshot_paths[-1] if snapshot_paths else None
        return {
            "kind": "huggingface_id",
            "exists": snapshot_path is not None,
            "cache_dir": str(cache_dir),
            "snapshot_path": str(snapshot_path) if snapshot_path is not None else "",
        }
    return {
        "kind": "unresolved",
        "exists": False,
        "path": model_id,
    }


def _backend_capabilities(backend: str) -> dict[str, Any]:
    """Describe what the selected backend currently supports in-repo."""
    return {
        "backend": backend,
        "text_to_image": True,
        "image_conditioning": backend == "dream_textures",
        "depth_conditioning": False,
        "seamless_disk": backend in {"dream_textures", "sd_cpp"},
        "world_environment_binding": True,
    }


def _dream_textures_memory_profile() -> str:
    """Return the active Dream Textures memory profile for this process."""
    profile = os.environ.get("BLACKHOLE_DREAM_TEXTURES_MEMORY_PROFILE", "").strip().lower()
    if not profile:
        return "default"
    return profile


def _dream_textures_optimizations(
    CPUOffload: Any,
    Optimizations: Any,
) -> tuple[Any, dict[str, Any]]:
    """Build Dream Textures optimization settings for the active memory profile."""
    profile = _dream_textures_memory_profile()
    if profile in {"conditioning_sweep", "low_vram"}:
        cpu_offload = CPUOffload.SUBMODULE
        optimizations = Optimizations(
            attention_slicing=True,
            sdp_attention=False,
            half_precision=True,
            cudnn_benchmark=False,
            tf32=False,
            cpu_offload=cpu_offload,
            vae_slicing=True,
        )
    else:
        cpu_offload = CPUOffload.OFF
        optimizations = Optimizations(
            attention_slicing=True,
            sdp_attention=True,
            half_precision=True,
            cudnn_benchmark=True,
            tf32=True,
            cpu_offload=cpu_offload,
        )
    report = {
        "profile": profile,
        "cpu_offload": getattr(cpu_offload, "value", str(cpu_offload)),
        "attention_slicing": bool(getattr(optimizations, "attention_slicing", False)),
        "sdp_attention": bool(getattr(optimizations, "sdp_attention", False)),
        "half_precision": bool(getattr(optimizations, "half_precision", False)),
        "cudnn_benchmark": bool(getattr(optimizations, "cudnn_benchmark", False)),
        "tf32": bool(getattr(optimizations, "tf32", False)),
        "vae_slicing": bool(getattr(optimizations, "vae_slicing", False)),
    }
    return optimizations, report


def _conditioning_policy(props: _SDProps) -> dict[str, Any]:
    """Describe the requested conditioning mode prior to backend resolution."""
    mode = getattr(props, "sd_conditioning_mode", "none")
    strength = float(getattr(props, "sd_conditioning_strength", 0.35))
    return {
        "mode": mode,
        "requested_mode": mode,
        "resolved_mode": mode,
        "scene_profile": _scene_profile_from_props(props),
        "strength": strength,
        "implemented": False,
        "effective_mode": "text_to_image",
        "source_image_name": "",
        "source_depth_name": "",
        "source_origin": "",
        "warnings": [],
    }


def _repo_root() -> pathlib.Path | None:
    """Return the repo root when this addon is running from the checkout."""
    candidate = pathlib.Path(__file__).resolve().parents[3]
    if (candidate / "CMakeLists.txt").exists() and (candidate / "README.md").exists():
        return candidate
    return None


def _scene_profile_from_props(props: _SDProps) -> str:
    """Map live Blackhole properties onto the verified scene-profile vocabulary."""
    inclination = float(getattr(props, "inclination_deg", 17.0))
    observer_distance = float(getattr(props, "observer_distance", 500.0))
    if inclination >= 30.0 or observer_distance <= 32.0:
        return "harsh_lighting"
    return "baseline"


def _load_conditioning_trends() -> dict[str, Any]:
    """Load the generated scene-aware trend summary when it exists locally."""
    repo_root = _repo_root()
    if repo_root is None:
        return {}
    report_path = repo_root / "build" / "Release" / "reports" / "dream_textures_conditioning_trends.json"
    if not report_path.exists():
        return {}
    try:
        return json.loads(report_path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _auto_conditioning_mode_for_scene(scene_profile: str, requested_mode: str) -> str:
    """Resolve auto modes from the generated trend report or measured fallbacks."""
    trends = _load_conditioning_trends()
    scene = trends.get("scenes", {}).get(scene_profile, {})
    if requested_mode == AUTO_INTERACTIVE_MODE:
        return scene.get("consensus_interactive_mode", "") or "image"
    if requested_mode == AUTO_PRODUCTION_MODE:
        return scene.get("consensus_production_mode", "") or "image_depth"
    return requested_mode


def auto_conditioning_summary(props: _SDProps) -> dict[str, Any]:
    """Return the current automatic conditioning decision for UI display."""
    requested_mode = getattr(props, "sd_conditioning_mode", "none")
    scene_profile = _scene_profile_from_props(props)
    return {
        "requested_mode": requested_mode,
        "resolved_mode": _auto_conditioning_mode_for_scene(scene_profile, requested_mode),
        "scene_profile": scene_profile,
        "uses_generated_trends": bool(_load_conditioning_trends()),
    }


def resolve_requested_conditioning_mode(props: _SDProps, requested_mode: str) -> str:
    """Resolve an explicit or auto conditioning mode against the current scene."""
    scene_profile = _scene_profile_from_props(props)
    return _auto_conditioning_mode_for_scene(scene_profile, requested_mode)


def slot_generation_defaults(props: _SDProps, slot: str, intent: str = "production") -> dict[str, Any]:
    """Return reliable slot-specific generation defaults for one-click actions."""
    scene_profile = _scene_profile_from_props(props)
    if slot == "disk":
        mode = AUTO_PRODUCTION_MODE if intent == "production" else AUTO_INTERACTIVE_MODE
    else:
        # Background generation is kept unconditioned by default because it may not
        # have a valid image/depth source yet, and text-to-image is the robust lane.
        mode = "none"
    return {
        "slot": slot,
        "conditioning_mode": mode,
        "scene_profile": scene_profile,
        "intent": intent,
    }


def conditioning_preflight_plan(props: _SDProps, slot: str, intent: str = "production") -> dict[str, Any]:
    """Describe the scene prerequisites needed for a policy-driven generation action."""
    defaults = slot_generation_defaults(props, slot=slot, intent=intent)
    resolved_mode = resolve_requested_conditioning_mode(props, defaults["conditioning_mode"])
    actions: list[str] = []
    if slot == "disk" and resolved_mode in {"image", "image_depth"}:
        actions.append("ensure_lensing_map")
    if slot == "disk" and resolved_mode in {"depth", "image_depth"}:
        actions.extend(
            [
                "ensure_scene_camera",
                "ensure_event_horizon",
                "ensure_accretion_disk",
            ]
        )
    return {
        **defaults,
        "resolved_mode": resolved_mode,
        "actions": actions,
    }


def prerequisite_signature(props: _SDProps, kind: str) -> dict[str, Any]:
    """Build a deterministic signature for cacheable scene prerequisites."""
    base = {
        "kind": kind,
        "spin": round(float(getattr(props, "spin", 0.0)), 6),
        "inclination_deg": round(float(getattr(props, "inclination_deg", 0.0)), 6),
        "observer_distance": round(float(getattr(props, "observer_distance", 0.0)), 6),
        "texture_width": int(getattr(props, "texture_width", 0)),
        "texture_height": int(getattr(props, "texture_height", 0)),
        "scene_profile": _scene_profile_from_props(props),
    }
    if kind == "disk_geometry":
        base |= {
            "mass_msun": round(float(getattr(props, "mass_msun", 0.0)), 3),
            "mdot_edd": round(float(getattr(props, "mdot_edd", 0.0)), 6),
            "disk_r_out": round(float(getattr(props, "disk_r_out", 0.0)), 6),
            "disk_radial_res": int(getattr(props, "disk_radial_res", 0)),
            "disk_azimuthal_res": int(getattr(props, "disk_azimuthal_res", 0)),
        }
    if kind == "horizon_geometry":
        base |= {
            "horizon_theta_res": int(getattr(props, "horizon_theta_res", 0)),
            "horizon_phi_res": int(getattr(props, "horizon_phi_res", 0)),
        }
    return base


def prerequisite_signature_token(props: _SDProps, kind: str) -> str:
    """Return a stable string token for cacheable prerequisite comparisons."""
    payload = prerequisite_signature(props, kind)
    blob = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()


def _image_metadata(data: np.ndarray[Any, np.dtype[np.float32]]) -> dict[str, Any]:
    """Describe the normalized image payload emitted by this module."""
    channels = int(data.shape[2]) if data.ndim == 3 else 0
    alpha_policy = "opaque_appended"
    if channels == 4:
        alpha_plane = data[:, :, 3]
        alpha_policy = "present"
        if np.allclose(alpha_plane, 1.0):
            alpha_policy = "present_opaque"
    return {
        "shape": list(data.shape),
        "dtype": str(data.dtype),
        "channel_count": channels,
        "colorspace": "sRGB",
        "range": [0.0, 1.0],
        "alpha_policy": alpha_policy,
    }


def _scalar_field_metadata(data: np.ndarray[Any, np.dtype[np.float32]]) -> dict[str, Any]:
    """Summarize a normalized scalar field such as a staged depth map."""
    arr = np.ascontiguousarray(np.asarray(data, dtype=np.float32))
    return {
        "shape": list(arr.shape),
        "dtype": str(arr.dtype),
        "range": [float(arr.min(initial=0.0)), float(arr.max(initial=0.0))],
        "mean": float(arr.mean()) if arr.size else 0.0,
    }


def _asset_digest(data: np.ndarray[Any, np.dtype[np.float32]]) -> dict[str, Any]:
    """Compute a deterministic digest for a generated RGBA float image."""
    arr = np.ascontiguousarray(data, dtype=np.float32)
    return {
        "sha256": hashlib.sha256(arr.tobytes()).hexdigest(),
        "byte_length": int(arr.nbytes),
    }


def _prompt_provenance(props: _SDProps, prompt: str, negative_prompt: str) -> dict[str, Any]:
    """Capture the exact inputs used to construct the current prompts."""
    return {
        "slot": props.sd_target_slot,
        "prompt_style": getattr(props, "sd_prompt_style", "scientific"),
        "prompt_prefix": props.sd_prompt_prefix,
        "user_negative_prompt": props.sd_negative_prompt,
        "prompt": prompt,
        "negative_prompt": negative_prompt,
        "model_id": props.sd_model_path.strip(),
        "width": int(props.texture_width),
        "height": int(props.texture_height),
        "steps_requested": int(props.sd_steps),
        "guidance_scale_requested": float(props.sd_guidance_scale),
        "conditioning_mode": getattr(props, "sd_conditioning_mode", "none"),
        "conditioning_strength": float(getattr(props, "sd_conditioning_strength", 0.35)),
        "spin": float(props.spin),
        "inclination_deg": float(props.inclination_deg),
        "mass_msun": float(props.mass_msun),
        "mdot_edd": float(props.mdot_edd),
    }


# ---------------------------------------------------------------------------
# Physics-informed prompt builders
# ---------------------------------------------------------------------------

def build_prompt(props: _SDProps) -> str:
    """Build a parameterized scientific prompt from scene Blackhole properties."""
    slot = props.sd_target_slot
    prefix = props.sd_prompt_prefix.strip()
    style = getattr(props, "sd_prompt_style", "scientific")

    spin_param = _format_parameter("a*", props.spin)
    inclination_param = _format_parameter("i", props.inclination_deg, "deg")
    mdot_param = _format_parameter("mdot", props.mdot_edd, "Edd")

    if slot == "disk":
        a = props.spin
        if a < 0.3:
            spin_desc = "slow-spin broad ring"
        elif a < 0.7:
            spin_desc = "moderate-spin bright inner ring"
        else:
            spin_desc = "near-extremal spin, tight photon ring"
        terms = [
            "Kerr accretion disk emissive texture",
            spin_param,
            inclination_param,
            mdot_param,
            spin_desc,
            "synchrotron plasma",
            "Doppler-bright crescent",
            "seamless tileable texture",
        ] + _style_terms(style, slot)
    else:  # background
        terms = [
            "equirectangular deep-space environment map",
            "deep extragalactic starfield",
            "distant galaxies",
            "sparse nebular haze",
            "no planets",
            "no spacecraft",
            "no foreground objects",
        ] + _style_terms(style, slot)

    base = ", ".join(terms)
    return f"{prefix} {base}".strip() if prefix else base


def build_negative_prompt(props: _SDProps) -> str:
    """Return user-configured negative prompt or a sensible default."""
    user_neg = props.sd_negative_prompt.strip()
    slot = props.sd_target_slot
    style = getattr(props, "sd_prompt_style", "scientific")
    if slot == "disk":
        default_neg = (
            "blurry, low quality, watermark, text, logo, people, faces, planets, "
            "spacecraft, city lights, horizon line, border frame"
        )
    else:
        default_neg = (
            "blurry, low quality, watermark, text, logo, planets, moons, spacecraft, "
            "asteroids, buildings, landscape horizon, foreground silhouette"
        )
    if style == "scientific":
        default_neg += ", fantasy, surreal illustration, cartoon brush strokes"
    return user_neg if user_neg else default_neg


# ---------------------------------------------------------------------------
# Backend A: stable-diffusion.cpp subprocess
# ---------------------------------------------------------------------------

def _generate_via_sd_cpp(
    prompt: str,
    negative: str,
    width: int,
    height: int,
    seed: int,
    steps: int,
    model_path: str,
) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Run the 'sd' binary in a subprocess and load the output PNG.

    WHY subprocess: the sd.cpp binary manages its own CUDA context.  Running it
    in a child process avoids any interaction with the CUDA allocations already
    held by the Blackhole CUDA kernel (libcudart.so via ctypes).
    """
    tmpdir = tempfile.mkdtemp(prefix="bh_sd_")
    out_png = os.path.join(tmpdir, "output.png")

    cmd = [
        "sd",
        "-M", "txt2img",
        "-m", model_path,
        "-p", prompt,
        "-n", negative,
        "-W", str(width),
        "-H", str(height),
        "--seed", str(seed),
        "--steps", str(steps),
        "-o", out_png,
    ]

    try:
        result = subprocess.run(
            cmd, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=300,
        )
        _ = result  # captured; not needed
    except subprocess.CalledProcessError as exc:
        stderr = exc.stderr.decode(errors="replace")
        raise RuntimeError(f"sd.cpp failed (exit {exc.returncode}): {stderr[:400]}") from exc
    except FileNotFoundError:
        raise RuntimeError(
            "'sd' binary not found in PATH.  Install stable-diffusion.cpp-cublas-git "
            "or set Backend to 'diffusers'."
        )
    except subprocess.TimeoutExpired:
        raise RuntimeError("sd.cpp timed out after 300 s")

    if not os.path.isfile(out_png):
        raise RuntimeError(f"sd.cpp did not produce output at {out_png}")

    arr = _load_png_via_blender(out_png, width, height)

    # Clean up temp directory
    try:
        import shutil as _sh
        _sh.rmtree(tmpdir, ignore_errors=True)
    except Exception:
        pass

    return arr


def _load_png_via_blender(path: str, expected_w: int, expected_h: int) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Load a PNG from disk into a numpy (H, W, 4) float32 array via bpy.

    Uses bpy.data.images.load() which is always available in Blender.  The pixels
    are stored bottom-to-top in Blender; we flip to top-to-bottom before returning.
    """
    img_name = "_bh_sd_tmp_load_"
    # Remove stale temporary image if present
    if img_name in bpy.data.images:
        bpy.data.images.remove(bpy.data.images[img_name])

    img = bpy.data.images.load(path)
    img.name = img_name

    w, h = img.size
    pixels = np.empty(w * h * 4, dtype=np.float32)
    img.pixels.foreach_get(pixels)

    # Blender stores images bottom-to-top; flip to top-to-bottom
    arr = np.flipud(pixels.reshape(h, w, 4))

    bpy.data.images.remove(img)
    return np.ascontiguousarray(arr, dtype=np.float32)


# ---------------------------------------------------------------------------
# Backend B: python-diffusers (HuggingFace)
# ---------------------------------------------------------------------------

def _get_or_load_diffusers_pipeline(model_id: str) -> Any:
    """Load and cache a StableDiffusionPipeline.  Returns the pipeline object."""
    try:
        import torch
        from diffusers import StableDiffusionPipeline, DPMSolverMultistepScheduler
    except ImportError as exc:
        raise RuntimeError(
            "python-diffusers or torch not available in Blender's Python. "
            "Install them via 'pip install diffusers torch' inside Blender's Python, "
            "or use the sd_cpp backend instead."
        ) from exc

    device = "cuda" if torch.cuda.is_available() else "cpu"
    cache_key = (model_id, device)

    if cache_key in _diffusers_cache:
        return _diffusers_cache[cache_key]

    dtype = torch.float16 if device == "cuda" else torch.float32

    pipe = StableDiffusionPipeline.from_pretrained(
        model_id,
        torch_dtype=dtype,
        safety_checker=None,       # disable; astrophysics images are not NSFW
        requires_safety_checker=False,
    )
    pipe.scheduler = DPMSolverMultistepScheduler.from_config(pipe.scheduler.config)
    pipe = pipe.to(device)

    if device == "cuda":
        try:
            pipe.enable_xformers_memory_efficient_attention()
        except Exception:
            pass  # xformers optional

    _diffusers_cache[cache_key] = pipe
    return pipe


def _generate_via_diffusers(
    prompt: str,
    negative: str,
    width: int,
    height: int,
    seed: int,
    steps: int,
    model_id: str,
    guidance_scale: float,
) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Generate an image using the diffusers pipeline and return (H, W, 4) float32."""
    try:
        import torch
    except ImportError as exc:
        raise RuntimeError("torch not available") from exc

    pipe = _get_or_load_diffusers_pipeline(model_id)

    # SD 1.x requires dimensions that are multiples of 64
    w_aligned = max(64, (width  // 64) * 64)
    h_aligned = max(64, (height // 64) * 64)

    generator = torch.Generator(
        device="cuda" if torch.cuda.is_available() else "cpu"
    ).manual_seed(seed)

    result = pipe(
        prompt=prompt,
        negative_prompt=negative,
        width=w_aligned,
        height=h_aligned,
        num_inference_steps=steps,
        guidance_scale=guidance_scale,
        generator=generator,
    )

    pil_img = result.images[0]

    # Resize to requested size if alignment changed dimensions
    if (w_aligned, h_aligned) != (width, height):
        pil_img = pil_img.resize((width, height))

    # PIL RGBA float32 -> numpy (H, W, 4) float32 in [0, 1]
    pil_rgba = pil_img.convert("RGBA")
    arr = np.array(pil_rgba, dtype=np.float32) / 255.0
    return arr


# ---------------------------------------------------------------------------
# Backend C: Dream Textures
# ---------------------------------------------------------------------------

def _extract_first_dream_textures_image(payload: Any) -> tuple[np.ndarray[Any, np.dtype[np.float32]], str]:
    """Extract a Dream Textures image array from its result container."""
    if isinstance(payload, list):
        if not payload:
            raise RuntimeError("Dream Textures returned an empty result list")
        payload = payload[-1]

    if hasattr(payload, "image"):
        image = payload.image
        return np.asarray(image), type(payload).__name__
    if hasattr(payload, "images") and payload.images:
        image = payload.images[0]
        return np.asarray(image), type(payload).__name__
    raise RuntimeError(f"Unsupported Dream Textures result container: {type(payload)!r}")


def _to_rgba_float_array(image: np.ndarray[Any, np.dtype[Any]]) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Normalize a Dream Textures image array to RGBA float32 in [0, 1]."""
    arr = np.asarray(image, dtype=np.float32)
    if arr.ndim == 2:
        arr = np.repeat(arr[..., None], 3, axis=2)
    if arr.ndim != 3:
        raise RuntimeError(f"Unexpected Dream Textures image rank: {arr.ndim}")
    if arr.shape[2] == 1:
        arr = np.repeat(arr, 3, axis=2)
    if arr.shape[2] > 4:
        arr = arr[:, :, :4]
    if arr.max(initial=0.0) > 1.0:
        arr = arr / 255.0
    arr = np.clip(arr, 0.0, 1.0)
    if arr.shape[2] == 3:
        alpha = np.ones((arr.shape[0], arr.shape[1], 1), dtype=np.float32)
        arr = np.concatenate([arr, alpha], axis=2)
    return np.ascontiguousarray(arr[:, :, :4], dtype=np.float32)


def _dream_textures_generation_policy(
    model_id: str,
    steps: int,
    guidance_scale: float,
    negative_prompt: str,
    conditioning_mode: str = "none",
) -> tuple[int, float, str, bool]:
    """Normalize generation knobs for model-specific Dream Textures policy."""
    model_lower = model_id.lower()
    if (
        ("sdxl-turbo" in model_lower or "sd-turbo" in model_lower)
        and conditioning_mode == "none"
    ):
        # The official model card recommends one-step generation with CFG disabled.
        return 1, 0.0, "", False
    return steps, guidance_scale, negative_prompt, bool(negative_prompt)


def _negative_prompt_policy(
    backend: str,
    model_id: str,
    requested_negative_prompt: str,
) -> dict[str, Any]:
    """Report whether the negative prompt is honored or suppressed."""
    effective_negative = requested_negative_prompt
    use_negative_prompt = bool(requested_negative_prompt)
    if backend == "dream_textures":
        _, _, effective_negative, use_negative_prompt = _dream_textures_generation_policy(
            model_id,
            1,
            1.0,
            requested_negative_prompt,
            "none",
        )
    return {
        "requested": requested_negative_prompt,
        "effective": effective_negative,
        "mode": "used" if use_negative_prompt else "suppressed",
    }


def _blender_image_to_rgba_float_array(
    image: Any,
) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Read a Blender image datablock into top-to-bottom RGBA float32."""
    width, height = image.size
    pixels = np.empty(width * height * 4, dtype=np.float32)
    image.pixels.foreach_get(pixels)
    arr = np.flipud(pixels.reshape(height, width, 4))
    return np.ascontiguousarray(arr, dtype=np.float32)


def _find_world_environment_image() -> Any | None:
    """Return the currently bound world environment image, if one exists."""
    world = getattr(bpy.context.scene, "world", None)
    if world is None or not world.use_nodes or world.node_tree is None:
        return None
    env_node = next(
        (node for node in world.node_tree.nodes if node.type == "TEX_ENVIRONMENT"),
        None,
    )
    if env_node is None:
        return None
    return getattr(env_node, "image", None)


def _ensure_bridge_lensing_source(
    props: _SDProps,
) -> tuple[np.ndarray[Any, np.dtype[np.float32]], dict[str, Any]]:
    """Ensure a Blackhole lensing image exists for Dream Textures conditioning."""
    token = prerequisite_signature_token(props, "lensing_map")
    existing = bpy.data.images.get("BlackholeLensingMap")
    if (
        existing is not None
        and list(existing.size) == [props.texture_width, props.texture_height]
        and str(existing.get("bh_signature_token", "")) == token
    ):
        return _blender_image_to_rgba_float_array(existing), {
            "source_image_name": existing.name,
            "source_origin": "reused_blackhole_lensing_map",
        }

    from . import bridge  # local import avoids unnecessary bridge loading on text-only lanes
    from . import operators

    if not bridge.try_load_library():
        raise RuntimeError(
            "Image-conditioned disk generation requires the Blackhole bridge library "
            "to render a lensing source image, but libblackhole_bridge.so could not be loaded."
        )

    data = bridge.render_lensing_map(
        a_star=props.spin,
        observer_r=getattr(props, "observer_distance", 1000.0),
        inclination_rad=np.deg2rad(props.inclination_deg),
        width=props.texture_width,
        height=props.texture_height,
    )
    operators._image_from_array(
        "BlackholeLensingMap",
        data,
        props.texture_width,
        props.texture_height,
    )
    image = bpy.data.images.get("BlackholeLensingMap")
    if image is not None:
        image["bh_signature_token"] = token
        image["bh_signature_payload"] = json.dumps(
            prerequisite_signature(props, "lensing_map"),
            sort_keys=True,
        )
    return np.ascontiguousarray(data, dtype=np.float32), {
        "source_image_name": "BlackholeLensingMap",
        "source_origin": "generated_bridge_lensing_map",
    }


def _conditioning_collection() -> Any | None:
    """Prefer Blackhole collections when rendering scene depth for conditioning."""
    for name in ("Blackhole Disk", "Blackhole Structure"):
        coll = bpy.data.collections.get(name)
        if coll is not None and len(coll.objects) > 0:
            return coll
    return None


def _render_scene_depth_map(
    collection: Any,
    width: int,
    height: int,
    invert: bool = True,
) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Render a normalized depth map for the selected collection.

    The automated lane uses a small software z-buffer instead of Blender's GPU
    offscreen path so it remains stable in headless Blender 5.2 alpha and
    OctaneBlender runs.
    """

    def rasterize_triangle(
        zbuffer: np.ndarray[Any, np.dtype[np.float32]],
        tri_xy: np.ndarray[Any, np.dtype[np.float32]],
        tri_depth: np.ndarray[Any, np.dtype[np.float32]],
    ) -> None:
        area = (
            (tri_xy[1, 0] - tri_xy[0, 0]) * (tri_xy[2, 1] - tri_xy[0, 1])
            - (tri_xy[1, 1] - tri_xy[0, 1]) * (tri_xy[2, 0] - tri_xy[0, 0])
        )
        if abs(float(area)) <= 1.0e-8:
            return

        min_x = max(int(np.floor(float(np.min(tri_xy[:, 0])))), 0)
        max_x = min(int(np.ceil(float(np.max(tri_xy[:, 0])))), width - 1)
        min_y = max(int(np.floor(float(np.min(tri_xy[:, 1])))), 0)
        max_y = min(int(np.ceil(float(np.max(tri_xy[:, 1])))), height - 1)
        if min_x > max_x or min_y > max_y:
            return

        for py in range(min_y, max_y + 1):
            sample_y = py + 0.5
            for px in range(min_x, max_x + 1):
                sample_x = px + 0.5
                w0 = (
                    (tri_xy[1, 0] - sample_x) * (tri_xy[2, 1] - sample_y)
                    - (tri_xy[1, 1] - sample_y) * (tri_xy[2, 0] - sample_x)
                ) / area
                w1 = (
                    (tri_xy[2, 0] - sample_x) * (tri_xy[0, 1] - sample_y)
                    - (tri_xy[2, 1] - sample_y) * (tri_xy[0, 0] - sample_x)
                ) / area
                w2 = 1.0 - w0 - w1
                if w0 < 0.0 or w1 < 0.0 or w2 < 0.0:
                    continue
                depth = float(w0 * tri_depth[0] + w1 * tri_depth[1] + w2 * tri_depth[2])
                if depth < zbuffer[py, px]:
                    zbuffer[py, px] = depth

    context = bpy.context
    depsgraph = context.evaluated_depsgraph_get()
    camera = context.scene.camera
    if camera is None:
        raise RuntimeError("Depth-conditioned generation requires an active scene camera.")

    view_matrix = camera.matrix_world.inverted()
    projection_matrix = camera.calc_matrix_camera(
        depsgraph,
        x=width,
        y=height,
    )
    view_projection = np.asarray(projection_matrix @ view_matrix, dtype=np.float32)
    zbuffer = np.full((height, width), np.inf, dtype=np.float32)

    for source_object in collection.objects:
        if source_object.type != "MESH":
            continue
        eval_object = source_object.evaluated_get(depsgraph)
        mesh = eval_object.to_mesh()
        if mesh is None:
            continue
        try:
            mesh.calc_loop_triangles()
            if len(mesh.vertices) == 0 or len(mesh.loop_triangles) == 0:
                continue

            vertices = np.empty((len(mesh.vertices), 3), dtype=np.float32)
            indices = np.empty((len(mesh.loop_triangles), 3), dtype=np.int32)
            mesh.vertices.foreach_get("co", vertices.reshape(-1))
            mesh.loop_triangles.foreach_get("vertices", indices.reshape(-1))

            transform = np.asarray(eval_object.matrix_world, dtype=np.float32)
            vertices_h = np.concatenate(
                [vertices, np.ones((len(vertices), 1), dtype=np.float32)],
                axis=1,
            )
            world_vertices = (transform @ vertices_h.T).T
            clip_vertices = (view_projection @ world_vertices.T).T
            w = clip_vertices[:, 3:4]
            valid = np.abs(w[:, 0]) > 1.0e-8
            if not np.any(valid):
                continue

            ndc = np.empty((len(vertices), 3), dtype=np.float32)
            ndc[:] = np.nan
            ndc[valid] = clip_vertices[valid, :3] / w[valid]
            screen_xy = np.empty((len(vertices), 2), dtype=np.float32)
            screen_xy[:, 0] = (ndc[:, 0] * 0.5 + 0.5) * width
            screen_xy[:, 1] = (1.0 - (ndc[:, 1] * 0.5 + 0.5)) * height
            screen_depth = np.clip(ndc[:, 2] * 0.5 + 0.5, 0.0, 1.0)

            for tri in indices:
                tri = np.asarray(tri, dtype=np.int32)
                if not np.all(valid[tri]):
                    continue
                tri_xy = screen_xy[tri]
                tri_depth = screen_depth[tri]
                if not np.isfinite(tri_xy).all():
                    continue
                rasterize_triangle(zbuffer, tri_xy, tri_depth)
        finally:
            eval_object.to_mesh_clear()

    depth = zbuffer.copy()
    depth[~np.isfinite(depth)] = 1.0
    if invert:
        depth = 1.0 - depth
        depth[~np.isfinite(zbuffer)] = 0.0

    nonzero = np.ma.masked_equal(depth, 0.0, copy=False)
    if nonzero.count() == 0:
        return np.zeros((height, width), dtype=np.float32)
    depth = np.interp(
        depth,
        [float(nonzero.min()), float(depth.max())],
        [0.0, 1.0],
    ).clip(0.0, 1.0)
    return np.ascontiguousarray(depth, dtype=np.float32)


def _capture_scene_depth(
    props: _SDProps,
) -> tuple[np.ndarray[Any, np.dtype[np.float32]] | None, dict[str, Any]]:
    """Render a normalized scene depth map for conditioning when geometry exists."""
    collection = _conditioning_collection()
    if collection is None:
        return None, {
            "source_depth_name": "",
            "source_origin": "scene_depth_unavailable",
        }

    depth = _render_scene_depth_map(
        collection=collection,
        invert=True,
        width=props.texture_width,
        height=props.texture_height,
    )
    depth = np.ascontiguousarray(np.clip(depth, 0.0, 1.0), dtype=np.float32)
    if depth.size == 0 or not np.isfinite(depth).all() or float(np.ptp(depth)) <= 1.0e-6:
        return None, {
            "source_depth_name": "",
            "source_origin": "scene_depth_unavailable",
        }
    return depth, {
        "source_depth_name": "DreamTexturesSceneDepth",
        "source_origin": "dream_textures_scene_depth",
    }


def _depth_model_ready(model_id: str) -> bool:
    """Best-effort gate for models that clearly advertise depth conditioning."""
    model_lower = model_id.lower()
    return "depth" in model_lower


def _resolve_conditioning_inputs(
    props: _SDProps,
    backend: str,
    model_id: str,
) -> dict[str, Any]:
    """Resolve requested conditioning into executable Dream Textures inputs."""
    requested_mode = getattr(props, "sd_conditioning_mode", "none")
    scene_profile = _scene_profile_from_props(props)
    resolved_mode = _auto_conditioning_mode_for_scene(scene_profile, requested_mode)
    strength = float(getattr(props, "sd_conditioning_strength", 0.35))
    resolved = {
        "mode": resolved_mode,
        "requested_mode": requested_mode,
        "resolved_mode": resolved_mode,
        "scene_profile": scene_profile,
        "strength": strength,
        "implemented": resolved_mode == "none",
        "effective_mode": "text_to_image",
        "source_image": None,
        "source_depth": None,
        "source_image_name": "",
        "source_depth_name": "",
        "source_origin": "",
        "warnings": [],
        "source_depth_metadata": {},
        "source_depth_digest": {},
    }

    if resolved_mode == "none":
        resolved["implemented"] = True
        return resolved

    if backend != "dream_textures":
        raise RuntimeError(
            f"Conditioning mode '{requested_mode}' currently requires the Dream Textures backend."
        )

    if requested_mode != resolved_mode:
        resolved["warnings"].append(f"auto_mode_resolved:{requested_mode}->{resolved_mode}")

    if resolved_mode in {"image", "image_depth"}:
        if props.sd_target_slot == "disk":
            source_image, source_meta = _ensure_bridge_lensing_source(props)
        else:
            world_image = _find_world_environment_image()
            source_image = None
            source_meta = {
                "source_image_name": "",
                "source_origin": "world_environment_missing",
            }
            if world_image is None:
                bg_image = bpy.data.images.get("BH_SD_Background")
                if bg_image is not None:
                    world_image = bg_image
                    source_meta = {
                        "source_image_name": bg_image.name,
                        "source_origin": "existing_background_image",
                    }
            else:
                source_meta = {
                    "source_image_name": world_image.name,
                    "source_origin": "world_environment_image",
                }
            if world_image is None:
                raise RuntimeError(
                    "Background image conditioning requires an existing BH_SD_Background "
                    "image or a bound world environment image."
                )
            source_image = _blender_image_to_rgba_float_array(world_image)
        resolved["source_image"] = np.ascontiguousarray(source_image[:, :, :3], dtype=np.float32)
        resolved["source_image_name"] = str(source_meta["source_image_name"])
        resolved["source_origin"] = str(source_meta["source_origin"])

    if resolved_mode in {"depth", "image_depth"}:
        if not _depth_model_ready(model_id):
            raise RuntimeError(
                "Depth-conditioned Dream Textures generation requires a depth-capable model "
                f"such as '{OFFICIAL_DEPTH_MODEL_ID}' or the automation-compatible "
                f"'{AUTOMATION_DEPTH_MODEL_ID}'."
            )
        depth_map, depth_meta = _capture_scene_depth(props)
        if resolved_mode == "depth" and depth_map is None:
            raise RuntimeError(
                "Depth-conditioned generation requested, but no usable scene depth map was available. "
                "Generate Blackhole geometry first or switch to image conditioning."
            )
        resolved["source_depth"] = depth_map
        resolved["source_depth_name"] = str(depth_meta["source_depth_name"])
        if resolved["source_origin"]:
            resolved["source_origin"] += "+"
        resolved["source_origin"] += str(depth_meta["source_origin"])
        if depth_map is None and resolved_mode == "image_depth":
            resolved["warnings"].append("scene_depth_unavailable_using_model_inferred_depth")
        if depth_map is not None:
            resolved["source_depth_metadata"] = _scalar_field_metadata(depth_map)
            resolved["source_depth_digest"] = _asset_digest(depth_map)

    resolved["implemented"] = True
    match resolved_mode:
        case "image":
            resolved["effective_mode"] = "image_to_image"
        case "depth" | "image_depth":
            resolved["effective_mode"] = "depth_to_image"
        case _:
            resolved["effective_mode"] = "text_to_image"
    return resolved


def _conditioning_report(conditioning: dict[str, Any]) -> dict[str, Any]:
    """Drop non-serializable payloads and keep only report-safe conditioning state."""
    return {
        "mode": conditioning["mode"],
        "requested_mode": conditioning.get("requested_mode", conditioning["mode"]),
        "resolved_mode": conditioning.get("resolved_mode", conditioning["mode"]),
        "scene_profile": conditioning.get("scene_profile", ""),
        "strength": conditioning["strength"],
        "implemented": conditioning["implemented"],
        "effective_mode": conditioning["effective_mode"],
        "source_image_name": conditioning["source_image_name"],
        "source_depth_name": conditioning["source_depth_name"],
        "source_origin": conditioning["source_origin"],
        "warnings": list(conditioning["warnings"]),
        "has_source_image": conditioning["source_image"] is not None,
        "has_source_depth": conditioning["source_depth"] is not None,
        "source_depth_metadata": dict(conditioning["source_depth_metadata"]),
        "source_depth_digest": dict(conditioning["source_depth_digest"]),
    }


def _generate_via_dream_textures(
    prompt: str,
    negative: str,
    width: int,
    height: int,
    seed: int,
    steps: int,
    model_id: str,
    guidance_scale: float,
    seamless_axes: str,
    conditioning: dict[str, Any],
) -> tuple[np.ndarray[Any, np.dtype[np.float32]], dict[str, Any]]:
    """Generate an image via the Dream Textures addon and return RGBA float32."""
    _enable_dream_textures()
    try:
        from dream_textures.generator_process import Generator
        from dream_textures.generator_process.models import CPUOffload, Optimizations, Scheduler
        from dream_textures.api.models.seamless_axes import SeamlessAxes
        from dream_textures.api.models.step_preview_mode import StepPreviewMode
    except Exception as exc:
        raise RuntimeError(f"Dream Textures import failed: {exc}") from exc

    steps, guidance_scale, negative, use_negative_prompt = _dream_textures_generation_policy(
        model_id, steps, guidance_scale, negative, conditioning["mode"]
    )

    gen = Generator.shared()
    optimizations, optimization_report = _dream_textures_optimizations(
        CPUOffload,
        Optimizations,
    )

    common_kwargs = dict(
        model=model_id,
        scheduler=Scheduler.DDIM,
        optimizations=optimizations,
        prompt=prompt,
        steps=steps,
        width=width,
        height=height,
        seed=seed if seed >= 0 else None,
        cfg_scale=guidance_scale,
        use_negative_prompt=use_negative_prompt,
        negative_prompt=negative,
        seamless_axes=SeamlessAxes(seamless_axes),
        iterations=1,
        step_preview_mode=StepPreviewMode.NONE,
        sdxl_refiner_model=None,
    )

    match conditioning["effective_mode"]:
        case "image_to_image":
            payload = gen.image_to_image(
                image=conditioning["source_image"],
                fit=True,
                strength=conditioning["strength"],
                **common_kwargs,
            ).result(last_only=True)
        case "depth_to_image":
            payload = gen.depth_to_image(
                depth=conditioning["source_depth"],
                image=conditioning["source_image"],
                strength=conditioning["strength"],
                **common_kwargs,
            ).result(last_only=True)
        case _:
            payload = gen.prompt_to_image(**common_kwargs).result(last_only=True)
    image, _container_type = _extract_first_dream_textures_image(payload)
    return _to_rgba_float_array(image), optimization_report


# ---------------------------------------------------------------------------
# Auto-backend selection
# ---------------------------------------------------------------------------

def _select_backend(props: _SDProps) -> str:
    """Resolve 'auto' to a concrete backend name."""
    backend = props.sd_backend
    if backend != "auto":
        return backend

    model = props.sd_model_path.strip()
    # If path ends with a known binary format, prefer sd.cpp
    if model.lower().endswith((".gguf", ".bin", ".safetensors")) and shutil.which("sd"):
        return "sd_cpp"
    if _dream_textures_available():
        return "dream_textures"
    # If it looks like a HuggingFace ID (no file extension) or a directory, use diffusers
    return "diffusers"


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def generate_with_metadata(
    props: _SDProps,
) -> tuple[np.ndarray[Any, np.dtype[np.float32]], dict[str, Any]]:
    """Generate an SD texture and return both image data and reproducibility metadata."""
    model = props.sd_model_path.strip()
    if not model:
        raise RuntimeError(
            "No model configured. Set 'SD Model' in the Blackhole > Stable Diffusion "
            "panel to a .gguf path or a HuggingFace model ID such as "
            "'stabilityai/sdxl-turbo'."
        )

    prompt = build_prompt(props)
    negative = build_negative_prompt(props)
    width = props.texture_width
    height = props.texture_height
    seed = props.sd_seed
    steps = props.sd_steps
    guidance = props.sd_guidance_scale

    backend = _select_backend(props)
    seamless_axes = "xy" if props.sd_target_slot == "disk" else "off"
    negative_policy = _negative_prompt_policy(backend, model, negative)
    effective_negative = str(negative_policy["effective"])
    effective_steps = int(steps)
    effective_guidance = float(guidance)
    conditioning = _resolve_conditioning_inputs(props, backend, model)
    if backend == "dream_textures":
        effective_steps, effective_guidance, _, _ = _dream_textures_generation_policy(
            model,
            steps,
            guidance,
            negative,
            conditioning["mode"],
        )

    if backend == "sd_cpp":
        if conditioning["mode"] != "none":
            raise RuntimeError(
                f"Conditioning mode '{conditioning['mode']}' is not yet implemented for the sd_cpp backend."
            )
        data = _generate_via_sd_cpp(
            prompt, effective_negative, width, height, seed, effective_steps, model
        )
    elif backend == "dream_textures":
        data, dream_textures_runtime = _generate_via_dream_textures(
            prompt,
            effective_negative,
            width,
            height,
            seed,
            effective_steps,
            model,
            effective_guidance,
            seamless_axes,
            conditioning,
        )
    elif backend == "diffusers":
        if conditioning["mode"] != "none":
            raise RuntimeError(
                f"Conditioning mode '{conditioning['mode']}' is not yet implemented for the diffusers backend."
            )
        data = _generate_via_diffusers(
            prompt,
            effective_negative,
            width,
            height,
            seed,
            effective_steps,
            model,
            effective_guidance,
        )
    else:
        raise RuntimeError(f"Unknown SD backend: {backend!r}")

    metadata = {
        "selected_backend": backend,
        "prompt": prompt,
        "negative_prompt": negative,
        "negative_prompt_policy": negative_policy,
        "prompt_budget": _prompt_budget(prompt, effective_negative),
        "prompt_provenance": _prompt_provenance(props, prompt, negative),
        "model_cache": _model_cache_state(model),
        "seed_policy": _seed_policy(seed),
        "backend_capabilities": _backend_capabilities(backend) | {
            "depth_conditioning": backend == "dream_textures" and _depth_model_ready(model),
        },
        "conditioning_policy": _conditioning_report(conditioning),
        "image_metadata": _image_metadata(data),
        "asset_digest": _asset_digest(data),
        "seamless_axes": seamless_axes,
        "effective_steps": effective_steps,
        "effective_guidance_scale": effective_guidance,
    }
    if backend == "dream_textures":
        metadata["dream_textures_runtime"] = dream_textures_runtime
    return data, metadata


def generate(props: _SDProps) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Generate an SD texture from scene Blackhole properties.

    Returns a numpy float32 array of shape (H, W, 4) in sRGB [0, 1].
    Raises RuntimeError with a user-readable message on failure.
    """
    data, _metadata = generate_with_metadata(props)
    return data


def clear_pipeline_cache() -> None:
    """Free cached diffusers pipelines and reclaim VRAM."""
    try:
        import torch
    except ImportError:
        pass
    else:
        for pipe in _diffusers_cache.values():
            try:
                pipe.to("cpu")
                del pipe
            except Exception:
                pass
        torch.cuda.empty_cache() if torch.cuda.is_available() else None
    _diffusers_cache.clear()
