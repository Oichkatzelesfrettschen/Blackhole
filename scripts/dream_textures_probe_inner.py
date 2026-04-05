#!/usr/bin/env python3
"""Inner Dream Textures runtime probe for Blender background execution."""

from __future__ import annotations

import json
import os
import pathlib
import sys

import addon_utils

sys.modules["__main__"].__file__ = "<blender string>"

addon_utils.enable("dream_textures", default_set=False, persistent=False)

from dream_textures.generator_process import Generator
from dream_textures.generator_process.models import Optimizations, Scheduler
from dream_textures.api.models.step_preview_mode import StepPreviewMode


def extract_first_image(payload):
    if isinstance(payload, list):
        if not payload:
            raise ValueError("Dream Textures returned an empty list")
        payload = payload[-1]
    if hasattr(payload, "image"):
        return payload.image, type(payload).__name__
    if hasattr(payload, "images") and payload.images:
        return payload.images[0], type(payload).__name__
    raise TypeError(f"Unsupported Dream Textures result container: {type(payload)!r}")


def main() -> int:
    report_path = pathlib.Path(os.environ["BLACKHOLE_DREAM_TEXTURES_REPORT_JSON"])
    model_id = os.environ.get("BLACKHOLE_DREAM_TEXTURES_MODEL_ID", "stabilityai/sdxl-turbo")
    prompt = os.environ.get("BLACKHOLE_DREAM_TEXTURES_PROMPT", "cinematic black hole accretion disk")
    width = int(os.environ.get("BLACKHOLE_DREAM_TEXTURES_WIDTH", "64"))
    height = int(os.environ.get("BLACKHOLE_DREAM_TEXTURES_HEIGHT", "64"))
    steps = int(os.environ.get("BLACKHOLE_DREAM_TEXTURES_STEPS", "1"))
    seed = int(os.environ.get("BLACKHOLE_DREAM_TEXTURES_SEED", "1"))

    report = {
        "status": "failure",
        "model_id": model_id,
        "prompt": prompt,
        "width": width,
        "height": height,
        "steps": steps,
        "seed": seed,
    }

    try:
        gen = Generator.shared()
        optimizations = Optimizations()
        installed_models = gen.hf_list_installed_models().result()
        device = gen.choose_device(optimizations).result()
        output = gen.prompt_to_image(
            model=model_id,
            scheduler=Scheduler.DDIM,
            optimizations=optimizations,
            prompt=prompt,
            steps=steps,
            width=width,
            height=height,
            seed=seed,
            cfg_scale=1.0,
            use_negative_prompt=False,
            negative_prompt="",
            seamless_axes=False,
            iterations=1,
            step_preview_mode=StepPreviewMode.NONE,
            sdxl_refiner_model=None,
        ).result(last_only=True)
        image, container_type = extract_first_image(output)
        report.update(
            {
                "status": "success",
                "device": str(device),
                "installed_model_count": len(installed_models),
                "result_type": type(output).__name__,
                "container_type": container_type,
                "shape": list(image.shape),
                "mean": float(image.mean()),
                "min": float(image.min()),
                "max": float(image.max()),
            }
        )
    except Exception as exc:  # pragma: no cover - exercised through Blender
        report["error"] = repr(exc)

    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
