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
| 2026-09-25 | Game canon | Thorne, "The Science of Interstellar", W.W. Norton (2014) | `https://wwnorton.com/books/the-science-of-interstellar/` | Sets the Interstellar time-dilation setting the game engine targets (audit 00 scope). |
| 2026-09-25 | Game canon | "Interstellar (2014) Transcript" | `https://scrapsfromtheloft.com/movies/interstellar-2014-transcript/` | Primary source for the "23 years" dialogue the audit's focused-colony clock recommendation turns into a mechanic (audit 00 recommended architecture, 03 sections 4, 9). |
| 2026-09-25 | Kerr metric | Kerr, "Gravitational Field of a Spinning Mass as an Example of Algebraically Special Metrics", Phys. Rev. Lett. 11 237 (1963) | `https://doi.org/10.1103/PhysRevLett.11.237` | Horizon radius reference value in the audit's numeric cross-check table (audit 02, numeric table). |
| 2026-09-25 | Kerr geodesics | Carter, "Global Structure of the Kerr Family of Gravitational Fields", Phys. Rev. 174 1559 (1968) | `https://doi.org/10.1103/PhysRev.174.1559` | Carter's fourth constant of motion and null Theta separation that `referee.py` and the audit's null-Theta fix use (audit 02 F4, F8). |
| 2026-09-25 | Kerr geodesics | Carter, "Hamilton-Jacobi and Schrodinger Separable Solutions of Einstein's Equations", Commun. Math. Phys. 10 280 (1968) | `https://doi.org/10.1007/BF03399503` | Carter's general separable metric form (`Delta_r`, `Delta_theta`, `Xi`, including the cosmological constant) that `referee.py` and the audit's Kerr-de Sitter fix use (audit 02 F5). |
| 2026-09-25 | Kerr geodesics | Bardeen, "Timelike and null geodesics in the Kerr metric", in Black Holes (Les Astres Occlus), Gordon and Breach (1973), 215-239 | `https://ui.adsabs.harvard.edu/abs/1973blho.conf..215B/abstract` | Closed-form Kerr critical curve the audit's P0 item 1 falsifier and photon-ring Lyapunov recommendation use (audit 00 item 1, 02 recommendation 8, 05 M5). |
| 2026-09-25 | Accretion disk flux | Page and Thorne, "Disk-Accretion onto a Black Hole. Time-Averaged Structure of Accretion Disk", ApJ 191 499 (1974) | `https://doi.org/10.1086/152990` | Closed-form disk flux the audit's Page-Thorne fix implements (audit 00 item 5, 01 F6, 02 F1). |
| 2026-09-25 | Accretion disk | Novikov and Thorne, "Astrophysics of Black Holes", in Black Holes (Les Astres Occlus), Gordon and Breach (1973), 343-450 | `https://ui.adsabs.harvard.edu/abs/1973blho.conf..343N/abstract` | One of the two disk models the shipped code mislabels a Newtonian profile as (audit 01 F6). |
| 2026-09-25 | Accretion disk | Shakura and Sunyaev, "Black holes in binary systems. Observational appearance", Astron. Astrophys. 24 337 (1973) | `https://ui.adsabs.harvard.edu/abs/1973A%26A....24..337S/abstract` | The Newtonian disk profile the shipped code actually implements while labeled Page-Thorne or Novikov-Thorne (audit 01 summary, 02 F1). |
| 2026-09-25 | Accretion disk efficiency | Bardeen, "Kerr Metric Black Holes", Nature 226 64 (1970) | `https://doi.org/10.1038/226064a0` | Disk radiative efficiency reference value the audit's Novikov-Thorne cross-check uses (audit 02, numeric table). |
| 2026-09-25 | Kerr disk transfer | Bardeen, Press, and Teukolsky, "Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation", ApJ 178 347 (1972) | `https://doi.org/10.1086/151796` | ZAMO frame and `u^t` the audit's orbiting-emitter g-factor and disk-velocity fixes use (audit 00 item 6, 01 F5, F7, 02 F11, F12). |
| 2026-09-25 | Kerr disk transfer | Laor, "Line profiles from a disk around a rotating black hole", ApJ 376 90 (1991) | `https://doi.org/10.1086/170257` | Ray-traced transfer function `iron_kline.h` names but does not implement (audit 00 item 7, 01 F7, 02 F11). |
| 2026-09-25 | Kerr disk transfer | Cunningham, "The effects of redshifts and focusing on the spectrum of an accretion disk around a Kerr black hole", ApJ 202 788 (1975) | `https://doi.org/10.1086/154033` | Transfer-function reference the audit's `kerrDiskGFactor` fix targets (audit 00 item 7, 02 F11, 03 F14). |
| 2026-09-25 | Synchrotron emission | Fouka and Ouichaoui, "Analytical fits to the synchrotron functions", RAA 13 680 (2013) | `https://doi.org/10.1088/1674-4527/13/6/007` | Source for the `F(x)`/`G(x)` fit the shipped polynomial cites and does not reproduce (audit 02 F10). |
| 2026-09-25 | Gravitational waves | Blanchet, "Gravitational Radiation from Post-Newtonian Sources and Inspiralling Compact Binaries", Living Rev. Relativ. 17 2 (2014) | `https://doi.org/10.12942/lrr-2014-2` | TaylorF2 phase reference the audit's gr_core 1/eta cross-check uses (audit 02 F9). |
| 2026-09-25 | GRMHD | Komissarov, "A Godunov-type scheme for relativistic magnetohydrodynamics", MNRAS 303 343 (1999) | `https://doi.org/10.1046/j.1365-8711.1999.02244.x` | 1D shock-tube test suite the audit sets as the bar for even an FFI/kernel look at `grmhd_core`; Blackhole's iharm3d/KORAL/BHAC ingestion stays the accuracy path either way (audit 02, recommendation 9). |
| 2026-09-25 | Elliptic integrals | Carlson, "Numerical computation of real or complex elliptic integrals", Numer. Algorithms 10 13 (1995) | `https://arxiv.org/abs/math/9409227` | Carlson duplication stopping rule the audit's `elliptic_integrals.h` rewrite uses (audit 05 M1, N6). |
| 2026-09-25 | Elliptic integrals | NIST Digital Library of Mathematical Functions, Chapter 19 "Elliptic Integrals", Section 19.36 "Methods of Computation" | `https://dlmf.nist.gov/19.36` | R_F/R_D/R_J series coefficients the audit's `elliptic_integrals.h` rewrite uses (audit 05 M1). |
| 2026-09-25 | Kerr metric textbook | Misner, Thorne, and Wheeler, "Gravitation", Princeton University Press (2017 reissue of the 1973 W.H. Freeman edition), eq. 33.2 | `https://press.princeton.edu/books/hardcover/9780691177793/gravitation` | Textbook Kerr `g_tphi` form `referee.py` is written from (audit 02, method). |
| 2026-09-25 | Polarized transfer | Landi Degl'Innocenti and Landi Degl'Innocenti, "On the solution of the radiative transfer equations for polarized radiation", Solar Phys. 97 239 (1985) | `https://doi.org/10.1007/BF00165988` | Closed-form Lorentz-group Stokes propagator the audit recommends porting to GPU (audit 05 N3). |
| 2026-09-25 | Algebra | Cariow and Cariowa, "An algorithm for fast multiplication of sedenions", Inf. Process. Lett. 113 324 (2013) | `https://doi.org/10.1016/j.ipl.2013.02.011` | Hadamard-diagonalized Cayley-Dickson multiplication the audit rates NOT-APPLICABLE to any Blackhole path (audit 05 N2). |
| 2026-09-25 | Signal processing | Loeffler, Ligtenberg, and Moschytz, "Practical fast 1-D DCT algorithms with 11 multiplications", ICASSP 1989, 988-991 | `https://doi.org/10.1109/ICASSP.1989.266596` | State-of-the-art multiply count the audit compares open_gororoba's IDCT8 butterfly against, rating it NOT-APPLICABLE (audit 05 N8). |

## Repo surfaces that currently consume these references

- `docs/developer-guide/octane-optimization.md`
- `docs/developer-guide/dream-textures-integration.md`
- `docs/requirements/octane.md`
- `docs/requirements/blender.md`
- `docs/audits/physics-and-game-engine/`

## Update rule

Whenever a new external source changes repo policy or implementation, add it
here in the same change that updates the code or docs that rely on it.
