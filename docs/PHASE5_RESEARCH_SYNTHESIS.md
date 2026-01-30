# Phase 5: Multi-Wavelength Observational Features - Research Synthesis

**Date:** 2026-01-29
**Status:** Research Complete - Ready for Implementation
**Scope:** Synthetic spectra generation, EHT/LIGO comparison, radiative transfer

---

## Existing Infrastructure (COMPLETE)

### 1. Synchrotron Radiation (src/physics/synchrotron.h)
**Status:** ✅ Fully Implemented (383 lines)

**Components:**
- Gyrofrequency and gyroradius calculations
- Synchrotron critical frequency (ν_c)
- Single electron power emission (P = 4/3 σ_T c γ² U_B)
- Cooling time calculations
- Synchrotron functions F(x) and G(x) with Bessel function approximations
- Polarization degree computation
- Power-law electron distribution spectrum
- Self-absorption coefficients
- Self-absorption frequency calculations

**References:**
- Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
- Longair (2011) "High Energy Astrophysics" Ch. 8

**Ready for:** GPU integration in GRMHD ray marching

### 2. Gravitational Waves (src/physics/gravitational_waves.h)
**Status:** ✅ Fully Implemented (569 lines)

**Components:**
- Chirp mass calculations
- GW strain amplitude (Newtonian + 1PN + 3.5PN)
- Plus and cross polarization computation
- Frequency evolution (Peters 1964)
- Time to coalescence formulas
- Orbital separation from frequency
- ISCO frequency calculations
- Post-Newtonian corrections (up to 3.5PN phase)
- Complete inspiral waveform generation
- Ringdown (quasi-normal modes)
- GW luminosity and energy radiated
- Binary system constructors (BNS, BBH)
- Characteristic strain for detector sensitivity

**References:**
- Peters & Mathews (1963)
- Blanchet (2014) Living Reviews
- LIGO Scientific Collaboration (2016)

**Ready for:** HDF5 export to LIGO format

### 3. Spectral LUT Generation (scripts/generate_tardis_lut_stub.py)
**Status:** ✅ Stub Complete (80 lines)

**Features:**
- Mock Gaussian spectrum generator
- TARDIS integration hook (fallback to mock)
- CSV output with wavelength/intensity columns
- JSON metadata generation
- Configurable wavelength range (3000-9000 Å default)
- 256 bins default

**Needs:** Real TARDIS integration or alternative spectral synthesis

---

## Implementation Roadmap

### Phase 5.1: Synchrotron GPU Integration (1-2 weeks)

**Goal:** Integrate synchrotron emission into GRMHD ray marching

**Files to Create:**
1. `shader/include/synchrotron_emission.glsl` (~300 lines)
   - Port synchrotron_F(x) function to GLSL
   - Port power-law spectrum calculation
   - Integrate with grmhd_octree.glsl

2. `shader/include/radiative_transfer.glsl` (~400 lines)
   - Ray marching with emission/absorption
   - Optical depth integration
   - Multi-frequency sampling

3. `src/physics/spectral_channels.h` (~200 lines)
   - Wavelength/frequency band definitions
   - RGB color mapping from spectra
   - EHT observation bands (230 GHz)

**Test Suite:**
4. `tests/synchrotron_spectrum_test.cpp` (~250 lines)
   - Power-law spectrum validation
   - Self-absorption frequency tests
   - Polarization degree tests
   - Comparison with Rybicki & Lightman analytic solutions

**Integration:**
5. Update `grmhd_octree.glsl::grmhdEmission()` (placeholder → real)
6. Update `grmhd_octree.glsl::grmhdAbsorption()` (placeholder → real)

**Estimated Effort:** 250-350 LOC, 1-2 weeks

### Phase 5.2: EHT Shadow Comparison (1 week)

**Goal:** Generate synthetic EHT observations and compare with M87*/Sgr A*

**Files to Create:**
1. `tools/eht_synthetic_image.cpp` (~500 lines)
   - Ray-trace at 230 GHz (EHT frequency)
   - Generate 2D intensity map
   - Apply Gaussian beam convolution
   - Compute shadow diameter
   - Export FITS format

2. `scripts/eht_shadow_metrics.py` (~300 lines)
   - Load synthetic and real EHT images
   - Compute shadow diameter and circularity
   - Generate difference maps
   - Statistical comparison (χ²)
   - Plot overlay visualizations

3. `tests/eht_shadow_test.cpp` (~200 lines)
   - Schwarzschild shadow: 42 microarcsec for M87* (4×10⁶ M_sun)
   - Kerr shadow: asymmetry for a*=0.9
   - Photon ring structure validation

**Data Sources:**
- EHT M87* images (2017-2018): https://eventhorizontelescope.org/for-scientists/data
- EHT Sgr A* images (2022): https://doi.org/10.3847/2041-8213/ac6674

**EHT Observation Parameters:**
- Frequency: 230 GHz (λ = 1.3 mm)
- Angular resolution: ~20 microarcseconds
- M87* mass: (6.5 ± 0.7) × 10⁹ M_sun
- M87* distance: 16.8 ± 0.8 Mpc
- Sgr A* mass: (4.0 ± 0.2) × 10⁶ M_sun
- Sgr A* distance: 8.127 ± 0.016 kpc

**Expected Shadow Diameters:**
- M87*: 42 ± 3 microarcseconds (validated in novikov_thorne_test.cpp)
- Sgr A*: ~52 microarcseconds

**Estimated Effort:** 1000 LOC, 1 week

### Phase 5.3: LIGO Waveform Export (1 week)

**Goal:** Generate LIGO-compatible GW strain data from binary mergers

**Files to Create:**
1. `tools/ligo_waveform_export.cpp` (~400 lines)
   - Use gravitational_waves.h::generate_inspiral_waveform()
   - Add merger and ringdown phases
   - Export to HDF5 format (LIGO standard)
   - Include metadata (masses, spins, distance)

2. `scripts/ligo_comparison.py` (~300 lines)
   - Load synthetic and real LIGO data
   - Matched filtering
   - SNR computation
   - Frequency evolution plots
   - Spectrogram comparisons

3. `tests/gw_waveform_test.cpp` (~250 lines)
   - Validate chirp mass extraction
   - Validate frequency evolution
   - Validate strain amplitude scaling
   - Compare with GW150914 parameters

**LIGO Format Specification:**
- HDF5 structure:
  ```
  /strain/Strain  (dataset: time-series h(t))
  /meta/GPSstart  (GPS time of waveform start)
  /meta/Duration  (waveform duration in seconds)
  /meta/SamplingRate  (samples per second)
  /parameters/mass1  (primary mass in solar masses)
  /parameters/mass2  (secondary mass in solar masses)
  /parameters/spin1z  (primary spin)
  /parameters/spin2z  (secondary spin)
  /parameters/distance  (luminosity distance in Mpc)
  /parameters/inclination  (orbital inclination in radians)
  ```

**Reference Events:**
- GW150914: 36 + 29 M_sun → 62 M_sun, z=0.09 (410 Mpc)
- GW170817: 1.46 + 1.27 M_sun (BNS), z=0.01 (40 Mpc)
- GW190521: 85 + 66 M_sun → 142 M_sun (most massive)

**Estimated Effort:** 950 LOC, 1 week

### Phase 5.4: X-ray Spectral Synthesis (1-2 weeks)

**Goal:** Generate synthetic X-ray spectra including Fe Kα line at 6.4 keV

**Files to Create:**
1. `src/physics/xray_spectrum.h` (~350 lines)
   - Bremsstrahlung (free-free) emission
   - Comptonization (thermal + bulk)
   - Fe Kα fluorescence line (6.4 keV)
   - Relativistic line profile (Laor 1991)
   - Reflection spectrum

2. `shader/include/xray_emission.glsl` (~250 lines)
   - Ray marching with multi-energy sampling
   - Thermal Comptonization
   - Line emission regions
   - Energy-dependent optical depth

3. `scripts/generate_xray_lut.py` (~300 lines)
   - Compute Comptonization tables
   - Fe line strength vs temperature/density
   - Export LUT for GPU

4. `tests/xray_spectrum_test.cpp` (~200 lines)
   - Bremsstrahlung spectrum shape
   - Comptonization y-parameter
   - Fe Kα equivalent width
   - Compare with Chandra/XMM-Newton observations

**X-ray References:**
- Laor (1991) ApJ 376, 90 (relativistic line profiles)
- Reynolds (2014) Space Sci Rev 183, 277 (X-ray reflection)
- Miller (2007) ARAA 45, 441 (Fe Kα observations)

**Key Physics:**
- Fe Kα line energy: 6.4 keV (neutral), 6.7 keV (He-like), 6.9 keV (H-like)
- Equivalent width: 50-500 eV depending on disk geometry
- Relativistic broadening: Doppler + gravitational redshift
- Compton temperature: kT_e ~ 50-100 keV (corona)

**Estimated Effort:** 1100 LOC, 1-2 weeks

---

## Phase 5 Granular TODO List (40 tasks)

### 5.1.1: Synchrotron GPU Integration (Tasks 1-12)

1. ☐ Create shader/include/synchrotron_emission.glsl header
2. ☐ Port synchrotron_F(x) to GLSL with approximations
3. ☐ Port synchrotron_G(x) for polarization
4. ☐ Implement power_law_spectrum() in GLSL
5. ☐ Implement self_absorption_coefficient() in GLSL
6. ☐ Create shader/include/radiative_transfer.glsl
7. ☐ Implement ray marching with emission/absorption
8. ☐ Implement optical depth integration
9. ☐ Create src/physics/spectral_channels.h (band definitions)
10. ☐ Update grmhd_octree.glsl::grmhdEmission() with real formula
11. ☐ Update grmhd_octree.glsl::grmhdAbsorption() with real formula
12. ☐ Create tests/synchrotron_spectrum_test.cpp (8 tests)

### 5.1.2: Spectral Channels & Color Mapping (Tasks 13-16)

13. ☐ Define observational bands (radio, optical, X-ray)
14. ☐ Implement RGB color mapping from multi-wavelength
15. ☐ Add EHT 230 GHz band integration
16. ☐ Add Chandra 0.5-10 keV band integration

### 5.2.1: EHT Shadow Comparison (Tasks 17-24)

17. ☐ Create tools/eht_synthetic_image.cpp
18. ☐ Implement 230 GHz raytracer
19. ☐ Implement Gaussian beam convolution
20. ☐ Implement shadow diameter measurement
21. ☐ Add FITS export support (cfitsio library)
22. ☐ Create scripts/eht_shadow_metrics.py
23. ☐ Download EHT M87* FITS data
24. ☐ Generate comparison plots and statistics

### 5.2.2: EHT Validation Tests (Tasks 25-28)

25. ☐ Create tests/eht_shadow_test.cpp
26. ☐ Test M87* shadow diameter (42 ± 3 μas)
27. ☐ Test Sgr A* shadow diameter (~52 μas)
28. ☐ Test Kerr shadow asymmetry (a*=0.9)

### 5.3.1: LIGO Waveform Export (Tasks 29-34)

29. ☐ Create tools/ligo_waveform_export.cpp
30. ☐ Implement HDF5 export with LIGO schema
31. ☐ Add merger phase (NR fits or phenomenological)
32. ☐ Add ringdown phase (QNM from gravitational_waves.h)
33. ☐ Create scripts/ligo_comparison.py
34. ☐ Download LIGO GW150914 data for validation

### 5.3.2: GW Validation Tests (Tasks 35-37)

35. ☐ Create tests/gw_waveform_test.cpp
36. ☐ Test chirp mass extraction accuracy
37. ☐ Test frequency evolution (df/dt formula)

### 5.4.1: X-ray Spectral Synthesis (Tasks 38-40)

38. ☐ Create src/physics/xray_spectrum.h
39. ☐ Implement Fe Kα line profile (Laor 1991)
40. ☐ Create tests/xray_spectrum_test.cpp

---

## Dependencies & Libraries

### Required Libraries:
- **HDF5:** For LIGO waveform export and GRMHD data
  - Conan: `hdf5/1.14.0` (already available)
- **CFITSIO:** For FITS image export (EHT format)
  - Install: `sudo pacman -S cfitsio` (Arch Linux)
  - Or build from source: https://heasarc.gsfc.nasa.gov/fitsio/
- **NumPy/SciPy:** For Python analysis scripts
  - Already in scripts/requirements.txt
- **Matplotlib:** For plotting
  - Already in scripts/requirements.txt

### Optional Libraries:
- **TARDIS:** Spectral synthesis (optional, fallback to mock)
  - Install: `pip install tardis-sn`
- **Astropy:** FITS file handling in Python
  - Install: `pip install astropy`

---

## Performance Targets

### EHT Synthetic Images:
- Resolution: 2048×2048 pixels (EHT resolution ~20 μas/pixel)
- Ray count: 4M rays (2048²)
- Render time: <10 seconds @ 230 GHz
- Shadow accuracy: ±2 μas (within EHT error bars)

### LIGO Waveforms:
- Sampling rate: 16384 Hz (LIGO standard)
- Duration: 2-10 seconds (f_low = 20 Hz to merger)
- Waveform generation: <1 second
- SNR match: ±5% vs LIGO matched filter

### X-ray Spectra:
- Energy range: 0.5-10 keV (Chandra band)
- Energy bins: 256 (ΔE ~ 40 eV)
- Spectrum generation: <1 second
- Fe Kα line FWHM: ±10% vs Laor profile

---

## Phase 5 Completion Criteria

1. ✅ Synchrotron emission integrated into GPU ray marching
2. ✅ EHT shadow diameter within ±5% of observations
3. ✅ LIGO waveform export in standard HDF5 format
4. ✅ X-ray spectrum with Fe Kα line (6.4 keV)
5. ✅ All 40 tasks complete
6. ✅ 15+ validation tests passing
7. ✅ Performance targets met

---

## Phase 5 Estimated Timeline

- **Week 1-2:** Synchrotron GPU integration (Tasks 1-16)
- **Week 3:** EHT shadow comparison (Tasks 17-28)
- **Week 4:** LIGO waveform export (Tasks 29-37)
- **Week 5-6:** X-ray spectral synthesis (Tasks 38-40)

**Total Duration:** 5-6 weeks
**Total LOC:** ~4,000 lines
**Total Tests:** 15+ validation tests

---

**Research Status:** ✅ COMPLETE
**Implementation Status:** Ready to begin
**Blockers:** None (all infrastructure exists)

**Next Action:** Begin Task #1 (Create synchrotron_emission.glsl)
