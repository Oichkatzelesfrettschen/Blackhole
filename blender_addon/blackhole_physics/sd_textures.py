# sd_textures.py -- Stable Diffusion texture generation for Blackhole addon.
#
# WHY: Generates physically-inspired accretion disk and starfield background textures
#      using SD inference and feeds them into Blender images consumed by Blackhole
#      materials ("BlackholeDiskTexture", world environment) and the CUDA render engine.
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
#
# HOW:
#   generate(props)               -> np.ndarray (H, W, 4) float32, sRGB
#   build_prompt(props)           -> str  (physics-conditioned prompt for inspection)
#   build_negative_prompt(props)  -> str
#   available_backends()          -> list[str]

from __future__ import annotations

import os
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
    texture_width: int
    texture_height: int
    spin: float             # Kerr spin parameter a* in [0, 1) -- used for prompt conditioning


# ---------------------------------------------------------------------------
# Pipeline cache for the diffusers backend (avoids reload on every generate).
# Keyed by (model_id, device_str) so a model change forces a fresh load.
# ---------------------------------------------------------------------------
_diffusers_cache: dict[tuple[str, str], Any] = {}


def available_backends() -> list[str]:
    """Return which backends can actually run on this machine."""
    result = []
    if shutil.which("sd") is not None:
        result.append("sd_cpp")
    try:
        import diffusers  # noqa: F401 -- existence check only
        result.append("diffusers")
    except ImportError:
        pass
    return result


# ---------------------------------------------------------------------------
# Physics-informed prompt builders
# ---------------------------------------------------------------------------

def build_prompt(props: _SDProps) -> str:
    """Build a physics-conditioned SD prompt from scene Blackhole properties.

    WHY: Conditioning on spin and inclination nudges the model toward images that
    qualitatively resemble the expected accretion morphology, even though SD has no
    GR knowledge.  The physics descriptions function as style keywords rather than
    hard constraints.
    """
    slot = props.sd_target_slot
    prefix = props.sd_prompt_prefix.strip()

    if slot == "disk":
        a = props.spin
        if a < 0.3:
            spin_desc = "slow spinning, broad luminous ring, gentle plasma flow"
        elif a < 0.7:
            spin_desc = "moderate spin, bright inner accretion ring, spiral plasma arms"
        else:
            spin_desc = (
                "near-extremal spin, tight photon orbit, ultra-bright inner edge, "
                "relativistic plasma jets"
            )
        base = (
            f"accretion disk synchrotron emission, polar top-down equatorial view, "
            f"{spin_desc}, hot plasma vortex, orange and white thermal glow, "
            f"magnetic turbulence, GRMHD simulation, astrophysics visualization, "
            f"photorealistic, 8k"
        )
    else:  # background
        base = (
            "deep space starfield, distant spiral galaxies and nebulae, "
            "James Webb Space Telescope photograph, blue and white stars, "
            "photorealistic, ultra-detailed, 8k"
        )

    return f"{prefix} {base}".strip() if prefix else base


def build_negative_prompt(props: _SDProps) -> str:
    """Return user-configured negative prompt or a sensible default."""
    user_neg = props.sd_negative_prompt.strip()
    default_neg = "blurry, low quality, watermark, text, logo, cartoon, painting"
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
    # If it looks like a HuggingFace ID (no file extension) or a directory, use diffusers
    return "diffusers"


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def generate(props: _SDProps) -> np.ndarray[Any, np.dtype[np.float32]]:
    """Generate an SD texture from scene Blackhole properties.

    Returns a numpy float32 array of shape (H, W, 4) in sRGB [0, 1].
    Raises RuntimeError with a user-readable message on failure.
    """
    model = props.sd_model_path.strip()
    if not model:
        raise RuntimeError(
            "No model configured.  Set 'SD Model' in the Blackhole > Stable Diffusion "
            "panel to a .gguf file path or a HuggingFace model ID."
        )

    prompt = build_prompt(props)
    negative = build_negative_prompt(props)
    width = props.texture_width
    height = props.texture_height
    seed = props.sd_seed
    steps = props.sd_steps
    guidance = props.sd_guidance_scale

    backend = _select_backend(props)

    if backend == "sd_cpp":
        return _generate_via_sd_cpp(
            prompt, negative, width, height, seed, steps, model
        )
    if backend == "diffusers":
        return _generate_via_diffusers(
            prompt, negative, width, height, seed, steps, model, guidance
        )

    raise RuntimeError(f"Unknown SD backend: {backend!r}")


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
