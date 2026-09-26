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
| 2026-09-25 | Kerr geodesics | Gralla and Lupsasca, "The Null Geodesics of the Kerr Exterior", PRD 101 044032 (2020) | `https://arxiv.org/abs/1910.12881` | Carter-separated R and Theta that the audit's Kerr null-geodesic fix and potential-consistency test use (audit 01 F1-F2). |
| 2026-09-25 | Kerr ray tracing | James, von Tunzelmann, Franklin, Thorne, CQG 32 065001 (2015) (DNGR) | `https://arxiv.org/abs/1502.03808` | FIDO-frame camera, arriving-photon tracing, ray bundles, and the Interstellar spin and no-Doppler choices (audit 01 F3, F9, F11; audit 03 canon). |
| 2026-09-25 | Kerr ray tracing | Chan et al., GRay2 | `https://arxiv.org/abs/1706.07062` | Kerr-Schild Cartesian Hamiltonian integrator named as a fix option for the turning-point stall (audit 01 F2). |
| 2026-09-25 | Kerr ray tracing | Bozzola, Chan, Paschalidis, "Not all spacetime coordinates for general-relativistic ray tracing are created equal", PRD 108 084004 (2023) | `https://arxiv.org/abs/2310.02321` | Corrects the `lacunae.md` attribution and scope (audit 01 F12). |
| 2026-09-25 | Kerr ray tracing | Cardenas-Avendano, Lupsasca, Zhu, PRD 107 043030 (2023) (AART) | `https://arxiv.org/abs/2211.07469` | Adaptive analytic ray tracing for photon rings and the Fe K transfer function (audit 01 F7, gap map). |
| 2026-09-25 | Kerr geodesics | Dyson and van de Meent, "Kerr-fully Diving into the Abyss: Analytic Solutions to Plunging Geodesics in Kerr" | `https://arxiv.org/abs/2302.03704` | Corrects the `lacunae.md` attribution; timelike plunges only (audit 01 F12). |
| 2026-09-25 | Polarized GRRT | Huang, Zheng, Guo, Chen (Coport) | `https://arxiv.org/abs/2407.10431` | Covariant polarized transport reference for the Stokes path (audit 01 F8). |
| 2026-09-25 | Polarized GRRT | Prather et al., ApJ 950 35 (2023) | `https://arxiv.org/abs/2303.12004` | EHT polarized code-comparison analytic model and NMSE gates proposed for verification (audit 01 F8). |
| 2026-09-25 | GRRT verification | Gold et al., EHT GRRT code comparison, ApJ 897 148 (2020) | `https://doi.org/10.3847/1538-4357/ab96c6` | Published GRRT benchmark suite proposed as a verification gate (audit 01 F13, gap map). |
| 2026-09-25 | EHT observations | "First Sagittarius A* EHT Results. VIII. Physical Interpretation of the Polarized Ring", ApJL 964 L26 (2024) | `https://doi.org/10.3847/2041-8213/ad2df1` | Corrects the `lacunae.md` paper number (audit 01 F12). |
| 2026-09-25 | EHT observations | M87* ring across 2017/2018/2021 (EHT) | `https://arxiv.org/abs/2509.24593` | Observational anchor for ring diameter and EVPA helicity (audit 01 gap map). |
| 2026-09-25 | Photon rings | Johnson et al., Sci. Adv. 6 eaaz1310 (2020) | `https://arxiv.org/abs/1907.04329` | Photon subring decay that sets the step-control and anti-aliasing requirement (audit 01 F11). |
| 2026-09-25 | Photon rings | BHEX mission | `https://arxiv.org/abs/2406.12917` | Subring science target (audit 01 gap map). |
| 2026-09-25 | VLBI | Raymond et al., AJ 168 130 (2024) | `https://arxiv.org/abs/2410.07453` | First 870 um VLBI detections; higher-frequency target (audit 01 gap map). |
| 2026-09-25 | GPU precision | Moscibrodzka and Yfantis | `https://arxiv.org/abs/2302.02733` | FP64 speedup evidence behind the precision strategy (audit 01 F11). |
| 2026-09-25 | Gravitational waves | Blanchet, Faye, Henry, Larrouturou, Trestini, "Gravitational-Wave Phasing of Quasi-Circular Compact Binary Systems to the Fourth-and-a-Half post-Newtonian Order", PRL 131 121402 (2023) | `https://arxiv.org/abs/2304.11185` | Corrects the `lacunae.md` attribution (audit 01 F12). |
| 2026-09-25 | Game canon | Opatrny, Richterek, Bakala, "Life under a black sun" | `https://arxiv.org/abs/1601.02897` | Gargantua spin `1 - 1.3e-14` and Miller orbit radius used for the canon dilation (audit 03 F4). |
| 2026-09-25 | Game canon | Dhingra, Dhurandhar, Mitra | `https://arxiv.org/abs/2606.01921` | Independent Miller's-planet spin, ISCO, and Roche estimates (audit 03 F4). |

## Repo surfaces that currently consume these references

- `docs/developer-guide/octane-optimization.md`
- `docs/developer-guide/dream-textures-integration.md`
- `docs/requirements/octane.md`
- `docs/requirements/blender.md`
- `docs/audits/physics-and-game-engine/`

## Update rule

Whenever a new external source changes repo policy or implementation, add it
here in the same change that updates the code or docs that rely on it.
