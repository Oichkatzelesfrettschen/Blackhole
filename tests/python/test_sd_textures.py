# tests/python/test_sd_textures.py
#
# WHY: sd_textures.py contains pure-Python logic (prompt building, backend
#      selection) that can be tested outside Blender.  These tests verify
#      correctness of the physics-informed prompt conditioning and backend
#      dispatch without requiring Blender, a GPU, or a real model.
#
# WHAT:
#   - MockSDProps dataclass satisfies the _SDProps Protocol without bpy.
#   - build_prompt / build_negative_prompt tests cover all spin tiers, slot
#     variants, and user-prefix concatenation.
#   - _select_backend tests verify auto-dispatch rules.
#   - Hypothesis property tests check invariants over the full spin range.
#
# HOW (run from repo root):
#   pytest tests/python -v
#   pytest tests/python --cov=blender/addon/blackhole_physics --cov-report=term

from __future__ import annotations

import importlib
import sys
import types
import unittest.mock
from dataclasses import dataclass, field

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Blender stub -- sd_textures imports bpy at module level for _load_png_via_blender.
# We inject a minimal stub before importing sd_textures so the module loads
# in a plain Python environment.
# ---------------------------------------------------------------------------

def _make_bpy_stub() -> types.ModuleType:
    """Build a minimal bpy stub that satisfies sd_textures module-level imports."""
    bpy = types.ModuleType("bpy")
    data = types.SimpleNamespace(
        images={}
    )
    bpy.data = data  # type: ignore[attr-defined]
    return bpy


def _install_bpy_stub() -> None:
    if "bpy" not in sys.modules:
        sys.modules["bpy"] = _make_bpy_stub()


_install_bpy_stub()

# Now safe to import sd_textures
import importlib.util  # noqa: E402 -- after stub install
_spec = importlib.util.spec_from_file_location(
    "sd_textures",
    "/home/eirikr/Github/Blackhole/blender/addon/blackhole_physics/sd_textures.py",
)
assert _spec is not None and _spec.loader is not None
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)  # type: ignore[union-attr]

build_prompt = _mod.build_prompt
build_negative_prompt = _mod.build_negative_prompt
_select_backend = _mod._select_backend
_prompt_budget = _mod._prompt_budget
_scene_profile_from_props = _mod._scene_profile_from_props
_auto_conditioning_mode_for_scene = _mod._auto_conditioning_mode_for_scene
auto_conditioning_summary = _mod.auto_conditioning_summary
resolve_requested_conditioning_mode = _mod.resolve_requested_conditioning_mode
slot_generation_defaults = _mod.slot_generation_defaults
conditioning_preflight_plan = _mod.conditioning_preflight_plan
prerequisite_signature = _mod.prerequisite_signature
prerequisite_signature_token = _mod.prerequisite_signature_token
available_backends = _mod.available_backends
generate_with_metadata = _mod.generate_with_metadata
_SDProps = _mod._SDProps


# ---------------------------------------------------------------------------
# MockSDProps -- satisfies _SDProps Protocol via dataclass
# ---------------------------------------------------------------------------

@dataclass
class MockSDProps:
    """Dataclass mock of BlackholeProperties that satisfies _SDProps Protocol."""

    spin: float = 0.9375
    texture_width: int = 512
    texture_height: int = 512
    sd_model_path: str = "/models/flux.gguf"
    sd_target_slot: str = "disk"
    sd_backend: str = "auto"
    sd_prompt_prefix: str = ""
    sd_negative_prompt: str = ""
    sd_steps: int = 25
    sd_seed: int = 42
    sd_guidance_scale: float = 7.5
    sd_prompt_style: str = "scientific"
    sd_conditioning_mode: str = "none"
    sd_conditioning_strength: float = 0.35
    inclination_deg: float = 17.0
    mass_msun: float = 6.5e9
    mdot_edd: float = 0.1
    observer_distance: float = 500.0


# ---------------------------------------------------------------------------
# build_prompt tests
# ---------------------------------------------------------------------------

class TestBuildPrompt:
    def test_disk_slot_contains_accretion(self) -> None:
        props = MockSDProps(sd_target_slot="disk", spin=0.5)
        prompt = build_prompt(props)
        assert "accretion" in prompt.lower()
        assert "texture" in prompt.lower()

    def test_background_slot_contains_deep_space(self) -> None:
        props = MockSDProps(sd_target_slot="background")
        prompt = build_prompt(props)
        assert "environment map" in prompt.lower()
        assert "starfield" in prompt.lower()

    def test_low_spin_disk_prompt(self) -> None:
        props = MockSDProps(sd_target_slot="disk", spin=0.1)
        prompt = build_prompt(props)
        # Slow-spin branch: should mention broad ring / slow rotation
        assert any(kw in prompt.lower() for kw in ("slow", "broad", "gentle"))

    def test_medium_spin_disk_prompt(self) -> None:
        props = MockSDProps(sd_target_slot="disk", spin=0.5)
        prompt = build_prompt(props)
        assert any(kw in prompt.lower() for kw in ("moderate", "spiral", "ring"))

    def test_high_spin_disk_prompt(self) -> None:
        props = MockSDProps(sd_target_slot="disk", spin=0.95)
        prompt = build_prompt(props)
        assert any(kw in prompt.lower() for kw in ("extremal", "jet", "photon"))

    def test_prefix_prepended(self) -> None:
        props = MockSDProps(sd_prompt_prefix="cinematic,", sd_target_slot="disk", spin=0.5)
        prompt = build_prompt(props)
        assert prompt.startswith("cinematic,")

    def test_empty_prefix_no_leading_space(self) -> None:
        props = MockSDProps(sd_prompt_prefix="", sd_target_slot="disk", spin=0.5)
        prompt = build_prompt(props)
        assert not prompt.startswith(" ")

    def test_returns_non_empty_string(self) -> None:
        for slot in ("disk", "background"):
            props = MockSDProps(sd_target_slot=slot)
            assert isinstance(build_prompt(props), str)
            assert len(build_prompt(props)) > 20

    def test_background_no_spin_conditioning(self) -> None:
        """Background prompts should not mention spin -- they are spin-independent."""
        props_low = MockSDProps(sd_target_slot="background", spin=0.1)
        props_high = MockSDProps(sd_target_slot="background", spin=0.99)
        # Background prompt content must be identical regardless of spin
        assert build_prompt(props_low) == build_prompt(props_high)

    def test_scientific_style_injects_parameters(self) -> None:
        props = MockSDProps(sd_target_slot="disk", sd_prompt_style="scientific", spin=0.9375)
        prompt = build_prompt(props)
        assert "a*=" in prompt
        assert "mdot=" in prompt
        assert "emission map" in prompt.lower()

    def test_cinematic_style_keeps_target_topology(self) -> None:
        props = MockSDProps(sd_target_slot="disk", sd_prompt_style="cinematic")
        prompt = build_prompt(props)
        assert "emissive texture" in prompt.lower()
        assert "cinematic astrophotography" in prompt.lower()

    def test_background_prompt_mentions_equirectangular(self) -> None:
        props = MockSDProps(sd_target_slot="background", sd_prompt_style="scientific")
        prompt = build_prompt(props)
        assert "equirectangular" in prompt.lower()
        assert "no planets" in prompt.lower()


# ---------------------------------------------------------------------------
# build_negative_prompt tests
# ---------------------------------------------------------------------------

class TestBuildNegativePrompt:
    def test_default_negative_prompt_non_empty(self) -> None:
        props = MockSDProps(sd_negative_prompt="")
        neg = build_negative_prompt(props)
        assert len(neg) > 0

    def test_default_contains_quality_keywords(self) -> None:
        props = MockSDProps(sd_negative_prompt="")
        neg = build_negative_prompt(props)
        assert any(kw in neg.lower() for kw in ("blurry", "low quality", "watermark"))

    def test_user_negative_prompt_overrides_default(self) -> None:
        custom = "no stars, no galaxies"
        props = MockSDProps(sd_negative_prompt=custom)
        neg = build_negative_prompt(props)
        assert neg == custom

    def test_user_negative_prompt_whitespace_stripped(self) -> None:
        props = MockSDProps(sd_negative_prompt="  bad quality  ")
        neg = build_negative_prompt(props)
        assert neg == "bad quality"

    def test_sdxl_turbo_dream_textures_suppresses_negative_prompt_in_metadata(self) -> None:
        props = MockSDProps(
            sd_backend="dream_textures",
            sd_model_path="stabilityai/sdxl-turbo",
        )
        fake = np.full((64, 64, 4), 0.5, dtype=np.float32)
        with unittest.mock.patch.object(
            _mod,
            "_generate_via_dream_textures",
            return_value=(fake, {"profile": "default"}),
        ):
            data, metadata = generate_with_metadata(props)
        assert data.shape == (64, 64, 4)
        assert metadata["negative_prompt_policy"]["mode"] == "suppressed"
        assert metadata["effective_steps"] == 1
        assert metadata["effective_guidance_scale"] == 0.0


class TestPromptBudget:
    def test_prompt_budget_marks_short_prompt_within_budget(self) -> None:
        budget = _prompt_budget("short prompt", "brief negative")
        assert budget["within_budget"] is True
        assert budget["warnings"] == []

    def test_prompt_budget_warns_when_prompt_is_too_long(self) -> None:
        prompt = "x" * (_mod.PROMPT_CHARACTER_BUDGET + 1)
        budget = _prompt_budget(prompt, "")
        assert budget["within_budget"] is False
        assert budget["warnings"]


class TestAutoConditioningPolicy:
    def test_scene_profile_uses_baseline_defaults(self) -> None:
        props = MockSDProps(inclination_deg=17.0, observer_distance=500.0)
        assert _scene_profile_from_props(props) == "baseline"

    def test_scene_profile_uses_harsh_lighting_defaults(self) -> None:
        props = MockSDProps(inclination_deg=34.0, observer_distance=24.0)
        assert _scene_profile_from_props(props) == "harsh_lighting"

    def test_auto_interactive_mode_falls_back_to_image(self) -> None:
        assert _auto_conditioning_mode_for_scene("baseline", "auto_interactive") == "image"

    def test_auto_production_mode_falls_back_to_image_depth(self) -> None:
        assert _auto_conditioning_mode_for_scene("baseline", "auto_production") == "image_depth"

    def test_auto_conditioning_summary_resolves_mode(self) -> None:
        props = MockSDProps(sd_conditioning_mode="auto_production")
        summary = auto_conditioning_summary(props)
        assert summary["requested_mode"] == "auto_production"
        assert summary["resolved_mode"] == "image_depth"
        assert summary["scene_profile"] == "baseline"

    def test_resolve_requested_conditioning_mode_keeps_explicit_mode(self) -> None:
        props = MockSDProps(sd_conditioning_mode="image")
        assert resolve_requested_conditioning_mode(props, "image") == "image"

    def test_resolve_requested_conditioning_mode_resolves_auto_mode(self) -> None:
        props = MockSDProps(sd_conditioning_mode="auto_production")
        assert resolve_requested_conditioning_mode(props, "auto_production") == "image_depth"

    def test_slot_generation_defaults_disk_production_uses_auto_production(self) -> None:
        props = MockSDProps()
        defaults = slot_generation_defaults(props, slot="disk", intent="production")
        assert defaults["slot"] == "disk"
        assert defaults["conditioning_mode"] == "auto_production"
        assert defaults["scene_profile"] == "baseline"

    def test_slot_generation_defaults_disk_interactive_uses_auto_interactive(self) -> None:
        props = MockSDProps()
        defaults = slot_generation_defaults(props, slot="disk", intent="interactive")
        assert defaults["conditioning_mode"] == "auto_interactive"

    def test_slot_generation_defaults_background_uses_text_to_image_safe_default(self) -> None:
        props = MockSDProps()
        defaults = slot_generation_defaults(props, slot="background", intent="production")
        assert defaults["slot"] == "background"
        assert defaults["conditioning_mode"] == "none"

    def test_conditioning_preflight_plan_for_disk_production_builds_all_prereqs(self) -> None:
        props = MockSDProps()
        plan = conditioning_preflight_plan(props, slot="disk", intent="production")
        assert plan["resolved_mode"] == "image_depth"
        assert plan["actions"] == [
            "ensure_lensing_map",
            "ensure_scene_camera",
            "ensure_event_horizon",
            "ensure_accretion_disk",
        ]

    def test_conditioning_preflight_plan_for_disk_interactive_only_needs_lensing(self) -> None:
        props = MockSDProps()
        plan = conditioning_preflight_plan(props, slot="disk", intent="interactive")
        assert plan["resolved_mode"] == "image"
        assert plan["actions"] == ["ensure_lensing_map"]

    def test_conditioning_preflight_plan_for_background_has_no_scene_prereqs(self) -> None:
        props = MockSDProps()
        plan = conditioning_preflight_plan(props, slot="background", intent="production")
        assert plan["resolved_mode"] == "none"
        assert plan["actions"] == []

    def test_prerequisite_signature_token_is_stable_for_same_inputs(self) -> None:
        props = MockSDProps()
        assert (
            prerequisite_signature_token(props, "lensing_map")
            == prerequisite_signature_token(props, "lensing_map")
        )

    def test_prerequisite_signature_token_changes_when_scene_changes(self) -> None:
        props_a = MockSDProps(inclination_deg=17.0)
        props_b = MockSDProps(inclination_deg=34.0)
        assert (
            prerequisite_signature_token(props_a, "lensing_map")
            != prerequisite_signature_token(props_b, "lensing_map")
        )

    def test_prerequisite_signature_includes_geometry_specific_fields(self) -> None:
        props = MockSDProps()
        sig = prerequisite_signature(props, "disk_geometry")
        assert "mass_msun" in sig
        assert "disk_r_out" in sig
        assert sig["kind"] == "disk_geometry"


class TestGenerateWithMetadata:
    def test_generate_with_metadata_reports_reproducibility_fields(self) -> None:
        props = MockSDProps(
            sd_backend="dream_textures",
            sd_model_path="stabilityai/sdxl-turbo",
        )
        fake = np.full((64, 64, 4), 0.25, dtype=np.float32)
        with unittest.mock.patch.object(
            _mod,
            "_generate_via_dream_textures",
            return_value=(fake, {"profile": "default"}),
        ):
            _data, metadata = generate_with_metadata(props)
        assert metadata["selected_backend"] == "dream_textures"
        assert metadata["seed_policy"]["mode"] == "fixed"
        assert metadata["backend_capabilities"]["text_to_image"] is True
        assert metadata["backend_capabilities"]["image_conditioning"] is True
        assert metadata["image_metadata"]["channel_count"] == 4
        assert len(metadata["asset_digest"]["sha256"]) == 64
        assert metadata["prompt_provenance"]["slot"] == "disk"
        assert metadata["conditioning_policy"]["mode"] == "none"
        assert metadata["conditioning_policy"]["effective_mode"] == "text_to_image"

    def test_generate_with_metadata_reports_image_conditioning(self) -> None:
        props = MockSDProps(
            sd_backend="dream_textures",
            sd_model_path="stabilityai/sdxl-turbo",
            sd_conditioning_mode="image",
        )
        fake = np.full((64, 64, 4), 0.75, dtype=np.float32)
        conditioning = {
            "mode": "image",
            "strength": props.sd_conditioning_strength,
            "implemented": True,
            "effective_mode": "image_to_image",
            "source_image": np.zeros((64, 64, 3), dtype=np.float32),
            "source_depth": None,
            "source_image_name": "BlackholeLensingMap",
            "source_depth_name": "",
            "source_origin": "existing_blackhole_lensing_map",
            "warnings": [],
            "source_depth_metadata": {},
            "source_depth_digest": {},
        }
        with unittest.mock.patch.object(_mod, "_resolve_conditioning_inputs", return_value=conditioning), \
             unittest.mock.patch.object(
                 _mod,
                 "_generate_via_dream_textures",
                 return_value=(fake, {"profile": "default"}),
             ):
            _data, metadata = generate_with_metadata(props)
        assert metadata["conditioning_policy"]["implemented"] is True
        assert metadata["conditioning_policy"]["effective_mode"] == "image_to_image"
        assert metadata["conditioning_policy"]["source_image_name"] == "BlackholeLensingMap"
        assert metadata["effective_steps"] == props.sd_steps

    def test_depth_capability_is_model_gated(self) -> None:
        assert _mod._depth_model_ready("stabilityai/stable-diffusion-2-depth") is True
        assert _mod._depth_model_ready("carsonkatri/stable-diffusion-2-depth-diffusers") is True
        assert _mod._depth_model_ready("stabilityai/sdxl-turbo") is False


# ---------------------------------------------------------------------------
# _select_backend tests
# ---------------------------------------------------------------------------

class TestSelectBackend:
    def test_explicit_sd_cpp(self) -> None:
        props = MockSDProps(sd_backend="sd_cpp", sd_model_path="/m/model.gguf")
        assert _select_backend(props) == "sd_cpp"

    def test_explicit_diffusers(self) -> None:
        props = MockSDProps(sd_backend="diffusers", sd_model_path="stabilityai/sd-2-1")
        assert _select_backend(props) == "diffusers"

    def test_auto_gguf_with_sd_binary(self) -> None:
        props = MockSDProps(sd_backend="auto", sd_model_path="/m/flux.gguf")
        with unittest.mock.patch("shutil.which", return_value="/usr/bin/sd"):
            result = _select_backend(props)
        assert result == "sd_cpp"

    def test_auto_gguf_without_sd_binary_falls_back_to_diffusers(self) -> None:
        props = MockSDProps(sd_backend="auto", sd_model_path="/m/flux.gguf")
        with unittest.mock.patch("shutil.which", return_value=None):
            result = _select_backend(props)
        assert result == "diffusers"

    def test_auto_hf_model_id_uses_diffusers(self) -> None:
        """HuggingFace model IDs prefer Dream Textures when available."""
        props = MockSDProps(sd_backend="auto", sd_model_path="stabilityai/stable-diffusion-2-1")
        with unittest.mock.patch("shutil.which", return_value="/usr/bin/sd"), \
             unittest.mock.patch.object(_mod, "_dream_textures_available", return_value=True):
            result = _select_backend(props)
        assert result == "dream_textures"

    def test_auto_hf_model_id_falls_back_to_diffusers_when_dream_absent(self) -> None:
        props = MockSDProps(sd_backend="auto", sd_model_path="stabilityai/stable-diffusion-2-1")
        with unittest.mock.patch("shutil.which", return_value="/usr/bin/sd"), \
             unittest.mock.patch.object(_mod, "_dream_textures_available", return_value=False):
            result = _select_backend(props)
        assert result == "diffusers"

    def test_auto_safetensors_with_sd_binary(self) -> None:
        props = MockSDProps(sd_backend="auto", sd_model_path="/m/sd21.safetensors")
        with unittest.mock.patch("shutil.which", return_value="/usr/bin/sd"):
            result = _select_backend(props)
        assert result == "sd_cpp"


# ---------------------------------------------------------------------------
# Hypothesis property tests
# ---------------------------------------------------------------------------

try:
    from hypothesis import given, settings
    from hypothesis import strategies as st
    _HYPOTHESIS_AVAILABLE = True
except ImportError:
    _HYPOTHESIS_AVAILABLE = False

if _HYPOTHESIS_AVAILABLE:
    @given(spin=st.floats(min_value=0.0, max_value=0.9999, allow_nan=False))
    @settings(max_examples=200)
    def test_prompt_always_non_empty_for_any_spin(spin: float) -> None:
        """build_prompt must return a non-empty string for all valid spin values."""
        props = MockSDProps(sd_target_slot="disk", spin=spin)
        with np.errstate(all="raise"):
            result = build_prompt(props)
        assert isinstance(result, str)
        assert len(result) > 0

    @given(spin=st.floats(min_value=0.0, max_value=0.9999, allow_nan=False))
    @settings(max_examples=200)
    def test_prompt_spin_tier_boundaries(spin: float) -> None:
        """The spin tier branch boundaries must not raise or produce empty output."""
        props = MockSDProps(sd_target_slot="disk", spin=spin)
        result = build_prompt(props)
        # Exactly one of the three spin-tier keywords must appear
        low_kw = any(k in result.lower() for k in ("slow", "broad", "gentle"))
        med_kw = any(k in result.lower() for k in ("moderate", "spiral"))
        high_kw = any(k in result.lower() for k in ("extremal", "jet", "photon"))
        assert low_kw or med_kw or high_kw, f"No spin-tier keyword in prompt for spin={spin}"

    @given(prefix=st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=80))
    @settings(max_examples=100)
    def test_prefix_always_appears_in_prompt(prefix: str) -> None:
        """Non-empty stripped prefix must appear at the start of the returned prompt."""
        stripped = prefix.strip()
        props = MockSDProps(sd_prompt_prefix=prefix, sd_target_slot="disk", spin=0.5)
        result = build_prompt(props)
        if stripped:
            assert result.startswith(stripped), (
                f"prefix {stripped!r} not at start of {result!r}"
            )
        else:
            # Empty prefix: prompt must not start with a space
            assert not result.startswith(" ")
