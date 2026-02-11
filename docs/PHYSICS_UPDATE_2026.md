# Black Hole Physics Update - January 2026
## Latest Observational Data and Simulation Constraints

**Last Updated:** 2026-01-31
**Data Sources:** EHT, LIGO-Virgo-KAGRA, GRMHD Simulations

---

## Executive Summary

This document consolidates the latest black hole physics observations and theoretical constraints from late 2025 through early 2026, providing guidance for physical accuracy in the Blackhole simulation.

---

## Event Horizon Telescope (EHT) Updates

### M87* Jet Base Detection (January 2026)

**Key Finding:** First direct detection of the M87 jet base approximately 0.09 light-years from the black hole using 230 GHz observations from 2021.

**Technical Details:**
- Detected previously unidentified jet component at 230 GHz
- Spatial resolution: ~0.09 light-years from M87*
- Confirms theoretical predictions of jet launching from ergosphere region

**Implications for Simulation:**
- Update jet emission models with 230 GHz frequency data
- Implement jet base positioning at ~0.09 light-years from horizon
- Add frequency-dependent jet emission profiles

**Source:** [Probing the jet base of M87's supermassive black hole](https://eventhorizontelescope.org/news/2026/01/probing-jet-base-m87s-supermassive-black-hole-0)

### Dynamic Polarization Patterns

**Key Finding:** M87* polarization patterns change significantly between 2017, 2018, and 2021 observations, while ring size remains constant.

**Technical Details:**
- Ring diameter: consistent across 3 observation epochs
- Polarization vector orientation: significant temporal variation
- Indicates dynamic magnetic field configuration in accretion disk

**Implications for Simulation:**
- Implement time-varying magnetic field orientation in disk models
- Add polarization calculation for synthetic observations
- Model magnetic field dynamics with ~yearly timescales

**Source:** [New EHT Images Reveal Unexpected Polarization Flips at M87*](https://eventhorizontelescope.org/new-eht-images-reveal-unexpected-polarization-flips-at-m87)

### Next-Generation 345 GHz Observations

**Key Finding:** EHT achieved first-ever 345 GHz observations from Earth's surface, providing 50% higher resolution than previous 230 GHz data.

**Technical Details:**
- Frequency: 345 GHz (vs. 230 GHz previously)
- Resolution improvement: 50% sharper images
- Multi-color observations of M87* and Sgr A* planned

**Implications for Simulation:**
- Add 345 GHz frequency support to radiative transfer calculations
- Update LUT generation for multi-frequency emission profiles
- Implement wavelength-dependent resolution effects

**Source:** [Event Horizon Telescope Makes Highest-Resolution Black Hole Detections from Earth](https://www.cfa.harvard.edu/news/event-horizon-telescope-makes-highest-resolution-black-hole-detections-earth)

---

## LIGO-Virgo-KAGRA Gravitational Wave Detections

### Fourth Observing Run (O4) Completion - November 2025

**Key Finding:** O4 detected 250 confirmed merger events from May 2023 to November 2025, bringing total confirmed detections to ~300 since 2015.

**Technical Details:**
- Duration: May 24, 2023 - November 18, 2025
- Confirmed mergers: 250 events
- Total catalog (all runs): ~300 black hole mergers
- Next run: Late summer/fall 2026 (6-month duration planned)

**Implications for Simulation:**
- Update mass distribution statistics for black hole populations
- Incorporate O4 spin distribution data
- Validate merger remnant calculations against 250 new events

**Source:** [LIGO-Virgo-KAGRA Complete Fourth Observing Run](https://www.ligo.caltech.edu/news/ligo20251118)

### GW231123 - Most Massive Black Hole Merger (July 2025)

**Key Finding:** Detection of most massive black hole merger ever observed - 225 solar mass final black hole.

**Technical Details:**
- Primary black hole: ~140 solar masses
- Secondary black hole: ~100 solar masses
- Final black hole: ~225 solar masses
- Event detected: November 23, 2023 (GW231123)
- Published: July 2025

**Implications for Simulation:**
- Update upper mass limit for binary black hole systems to 225+ solar masses
- Validate Kerr metric calculations for high-mass remnants
- Implement gravitational wave energy loss for 100+ solar mass systems

**Sources:**
- [LIGO-Virgo-KAGRA Detect Most Massive Black Hole Merger to Date](https://www.ligo.caltech.edu/news/ligo20250715)
- [Gravitational Waves Reveal Most Massive Black Hole Merger Ever Detected](https://www.simonsfoundation.org/2025/07/21/gravitational-waves-reveal-most-massive-black-hole-merger-ever-detected/)

### GW241011 & GW241110 - Unusual Spin Configurations (October 2025)

**Key Finding:** Two merger events with unprecedented spin measurements: one of the fastest rotating black holes observed, and first detection of counter-rotating (retrograde) black hole in binary system.

**Technical Details:**
- **GW241011:** Larger component is one of fastest rotating black holes observed to date
- **GW241110:** Primary black hole spinning opposite to orbital angular momentum (retrograde)
- Detection dates: October 11 and November 10, 2024
- Publication: The Astrophysical Journal Letters, October 28, 2025

**Implications for Simulation:**
- Add support for near-extremal Kerr spins (a* ~ 0.99+)
- Implement retrograde spin calculations for frame dragging
- Update ISCO calculations for counter-rotating black holes
- Model precession effects from misaligned spins

**Sources:**
- [Pair of Distinct Black Hole Mergers Sheds New Light on Nature of Their Formation and Evolution](https://www.ligo.caltech.edu/news/ligo20251028)
- [Pair of distinct black hole mergers sheds new light on their formation and evolution](https://science.ubc.ca/news/2025-10/pair-distinct-black-hole-mergers-sheds-new-light-their-formation-and-evolution)

---

## GRMHD Simulation Advances

### EHT-Constrained Sgr A* Models

**Key Finding:** GRMHD simulations successfully reproduce EHT-measured magnetic field strengths for Sagittarius A* with ~10% accuracy, favoring MAD configuration with spin a* ≈ 0.94.

**Technical Details:**
- Preferred configuration: Magnetically Arrested Disk (MAD)
- Spin parameter: a* ≈ 0.94 (near-extremal rotation)
- Magnetic field accuracy: ~10% match to EHT observations
- Frequency: 230 GHz light curve variability matched

**Implications for Simulation:**
- Update default Kerr spin to a* = 0.94 for Sgr A* preset
- Implement MAD accretion state with strong magnetic fields
- Add magnetic field strength validation against EHT data
- Model 230 GHz variability timescales (~hourly for Sgr A*)

**Sources:**
- [GRMHD modelling of accretion flow around Sagittarius A* constrained by EHT](https://arxiv.org/html/2510.03602)
- [GRMHD modelling of accretion flow around Sagittarius A∗constrained by EHT](https://www.arxiv.org/pdf/2510.03602)

### Dynamo and Jet Interconnections (December 2025)

**Key Finding:** Large-scale magnetic field generation via dynamo action in SANE (Standard Accretion Neglecting Evaporation) disks directly drives jet formation.

**Technical Details:**
- Toroidal magnetic field advection into inner disk regions
- Magnetic reconnection converts toroidal → poloidal fields
- Poloidal fields essential for jet collimation and launching
- Quantified dynamo-jet coupling in 3D GRMHD simulations

**Implications for Simulation:**
- Implement dynamo-driven magnetic field evolution
- Add toroidal-to-poloidal field conversion physics
- Model jet launching as function of poloidal field strength
- Include magnetic reconnection heating in disk thermodynamics

**Source:** [Dynamo and Jet interconnections in GRMHD simulations of black hole accretion disks](https://arxiv.org/html/2512.02129v1)

### MAD/SANE/Intermediate Accretion States

**Key Finding:** High-resolution GRMHD simulations identify three distinct accretion regimes with different jet properties and radiative signatures.

**Technical Details:**
- **MAD (Magnetically Arrested Disk):** Strong B-field, powerful jets, episodic flux eruptions
- **SANE (Standard and Normal Evolution):** Weak B-field, steady accretion, weak jets
- **Intermediate State:** Moderate magnetic support, transitional dynamics

**Implications for Simulation:**
- Add runtime toggle for MAD/SANE/Intermediate accretion states
- Implement state-dependent jet power and collimation
- Model magnetic field strength thresholds for state transitions
- Add episodic flux variations for MAD state

**Source:** [Black hole accretion and radiation variability in GRMHD simulations with Rezzolla-Zhidenko spacetime](https://www.aanda.org/articles/aa/full_html/2025/02/aa52679-24/aa52679-24.html)

---

## Updated Physical Parameters for Simulation

### Schwarzschild Black Holes
- **Mass range:** 1 M☉ - 225+ M☉ (updated upper limit from GW231123)
- **Hawking temperature:** T_H = 6.17×10⁻⁸ K × (M☉/M) (unchanged)
- **Event horizon radius:** r_s = 2GM/c² = 2.95 km × (M/M☉)

### Kerr Black Holes
- **Spin parameter range:** a* = -0.998 to +0.998 (updated for GW241110 retrograde spin)
- **Preferred spin (Sgr A*):** a* ≈ 0.94 (from EHT-constrained GRMHD)
- **ISCO (prograde):** r_ISCO = 1.236 r_s (for a* = 0.94)
- **ISCO (retrograde):** r_ISCO = 9.0 r_s (for a* = -0.998)
- **Ergosphere:** r_erg = r_s [1 + √(1 - a*²cos²θ)]

### Accretion Disk
- **Preferred state (Sgr A*):** MAD with a* = 0.94
- **Magnetic field (Sgr A*):** EHT-calibrated to ~10% accuracy
- **Variability timescale (230 GHz):** ~Hours for Sgr A*
- **Polarization:** Time-varying, ~yearly evolution for M87*

### Jet Physics
- **Jet base (M87):** ~0.09 light-years from event horizon
- **Frequency:** 230 GHz and 345 GHz (new EHT capability)
- **Launching mechanism:** Poloidal magnetic field from dynamo action
- **Collimation:** Strongest in MAD state

---

## Action Items for Code Updates

### High Priority (Physical Accuracy)

1. **Update Kerr spin defaults:**
   - Sgr A* preset: a* = 0.94 (from 0.5 or 0.7)
   - Add retrograde spin support: a* ∈ [-0.998, +0.998]
   - Validate ISCO calculations for extreme spins

2. **Implement MAD accretion state:**
   - Strong magnetic field configuration
   - Episodic flux eruptions
   - Enhanced jet power

3. **Add 345 GHz frequency support:**
   - Update LUT generation scripts
   - Extend emissivity calculations to 345 GHz
   - Implement multi-frequency synthetic observations

4. **Jet base positioning:**
   - M87 preset: jet base at 0.09 light-years
   - Frequency-dependent jet emission
   - Poloidal magnetic field visualization

### Medium Priority (Validation)

5. **Update mass limits:**
   - Upper limit: 225+ M☉ (from GW231123)
   - Validate gravitational wave calculations
   - Test Kerr metric stability for high masses

6. **Time-varying polarization:**
   - Implement magnetic field orientation evolution
   - Add yearly variability for M87*-like systems
   - Generate synthetic polarization maps

7. **GRMHD state selector:**
   - UI toggle: MAD / SANE / Intermediate
   - State-dependent magnetic field strength
   - Jet power scaling

### Low Priority (Documentation)

8. **Update validation tables:**
   - EHT-constrained magnetic fields
   - O4 mass/spin distributions
   - 345 GHz observational capabilities

9. **Add 2026 references:**
   - Update PHYSICS_ARCHITECTURE.md
   - Add citations to latest papers
   - Document parameter changes

---

## References (Chronological)

### 2025

1. **July 2025:** LIGO-Virgo-KAGRA detection of GW231123 (225 M☉ black hole merger)
   - [LIGO-Virgo-KAGRA Detect Most Massive Black Hole Merger to Date](https://www.ligo.caltech.edu/news/ligo20250715)

2. **October 2025:** GW241011 & GW241110 unusual spin configurations
   - [Pair of Distinct Black Hole Mergers Sheds New Light](https://www.ligo.caltech.edu/news/ligo20251028)

3. **November 2025:** LIGO-Virgo-KAGRA O4 run completion (250 events)
   - [LIGO-Virgo-KAGRA Complete Fourth Observing Run](https://www.ligo.caltech.edu/news/ligo20251118)

4. **December 2025:** Dynamo and jet interconnections in GRMHD simulations
   - [arXiv:2512.02129](https://arxiv.org/html/2512.02129v1)

### 2026

5. **January 2026:** M87* jet base detection and 345 GHz observations
   - [Probing the jet base of M87's supermassive black hole](https://eventhorizontelescope.org/news/2026/01/probing-jet-base-m87s-supermassive-black-hole-0)

6. **January 2026:** M87* polarization evolution study
   - [New EHT Images Reveal Unexpected Polarization Flips](https://eventhorizontelescope.org/new-eht-images-reveal-unexpected-polarization-flips-at-m87)

7. **January 2026:** EHT 345 GHz capability announcement
   - [Event Horizon Telescope Makes Highest-Resolution Detections](https://www.cfa.harvard.edu/news/event-horizon-telescope-makes-highest-resolution-black-hole-detections-earth)

### GRMHD Simulations (2025)

8. **GRMHD modelling of Sgr A* constrained by EHT measurements**
   - [arXiv:2510.03602](https://arxiv.org/html/2510.03602)

9. **Black hole accretion and radiation variability in GRMHD simulations**
   - [Astronomy & Astrophysics](https://www.aanda.org/articles/aa/full_html/2025/02/aa52679-24/aa52679-24.html)

---

## Version History

- **2026-01-31:** Initial document creation with January 2026 EHT data
- **Future:** Update with ongoing O5 run data (expected late summer 2026)
