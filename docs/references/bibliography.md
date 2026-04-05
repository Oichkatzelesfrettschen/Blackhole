# Bibliography And External References

This is the running external-reference ledger for Blackhole.

## Policy

- Add sources here when they directly inform implemented code, benchmark policy,
  verification policy, packaging, or user-facing technical guidance.
- Prefer primary or official sources.
- Keep each entry short and practical: what it is, why we used it, and when it
  was last checked.
- Do not treat presence here as proof that a claim is implemented. For that,
  use `docs/physics/claims-evidence.md` and `claims_evidence.json`.

## Current References

| Date checked | Area | Title | URL | Why it matters here |
|---|---|---|---|---|
| 2026-03-22 | Octane | Octane Blender manual PDF | `https://docs.otoy.com/BlenderP/BlenderPluginManual.pdf` | Official Octane Blender reference used for optimization and workflow guidance. |
| 2026-03-22 | Octane | Installation Process | `https://docs.otoy.com/blender/InstallationProcess.html` | Official install flow used while reconciling local package upgrades. |
| 2026-03-22 | Octane | Octane Server | `https://docs.otoy.com/blender/OctaneServer.html` | Official server-side workflow reference for activation/readiness handling. |
| 2026-03-22 | OTOY | Prime / Free tier signup | `https://render.otoy.com/shop/prime.php` | Official free-tier signup page needed for local Octane activation. |
| 2026-03-22 | Dream Textures | Dream Textures repository | `https://github.com/carson-katri/dream-textures` | Upstream addon provenance and feature reference for seamless textures and depth-to-image scene projection. |
| 2026-03-22 | Diffusion Models | SDXL Turbo model card | `https://huggingface.co/stabilityai/sdxl-turbo` | Official model guidance for one-step generation with `guidance_scale=0.0`, used to set Blackhole's Dream Textures defaults. |
| 2026-03-23 | Diffusion Models | Stable Diffusion 2 Depth | `https://huggingface.co/stabilityai/stable-diffusion-2-depth` | Official upstream depth-capable model Dream Textures recommends for depth-to-image. It is gated on this machine without a Hugging Face login, so Blackhole documents it as canonical upstream but does not depend on anonymous access to it. |
| 2026-03-23 | Diffusion Models | stable-diffusion-2-depth-diffusers | `https://huggingface.co/carsonkatri/stable-diffusion-2-depth-diffusers` | Public diffusers-format conversion of the official SD2 depth model. Blackhole uses this mirror for unattended depth-conditioned verification because it is automation-compatible on this machine. |

## Repo surfaces that currently consume these references

- `docs/developer-guide/octane-optimization.md`
- `docs/developer-guide/dream-textures-integration.md`
- `docs/requirements/octane.md`
- `docs/requirements/blender.md`

## Update rule

Whenever a new external source changes repo policy or implementation, add it
here in the same change that updates the code or docs that rely on it.
