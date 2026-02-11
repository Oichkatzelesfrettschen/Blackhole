# Blackhole Simulator - Complete User Guide
**Version:** 2026.1 (EHT-Constrained)
**Last Updated:** 2026-01-31

---

## Quick Start (5 Minutes)

### Launch the Simulator

```bash
cd /path/to/Blackhole
./build/Release/Blackhole
```

The application opens with a real-time black hole renderer and control panel.

### Your First Black Hole: Sgr A*

1. **Click the "Sgr A* (MAD, a*=0.94)" button**
   - This sets all parameters to match our galaxy's supermassive black hole
   - Based on EHT observations from 2025-2026

2. **Observe the visualization**
   - Inner disk edge is very close to the horizon (ISCO at 2.024 M)
   - Strong frame dragging due to high spin (a* = 0.94)
   - Bright inner accretion disk

3. **Experiment with the controls**
   - Drag the camera to rotate view
   - Scroll to zoom in/out
   - Adjust parameters in the control panel

**Congratulations!** You're visualizing the most accurate Sgr A* model as of January 2026.

---

## Understanding the Interface

### Main Viewport
- Real-time ray-traced black hole rendering
- Shows accretion disk, photon sphere, event horizon
- Camera controls: Click+drag to rotate, scroll to zoom

### Control Panel

#### Black Hole Parameters
- **blackHoleMass**: Mass in solar masses (0.1 to 250 M☉)
  - Default: 1.0 M☉
  - Sgr A*: 4.3 × 10⁶ M☉
  - M87: 6.5 × 10⁹ M☉

- **kerrSpin(a/M)**: Dimensionless spin parameter (-0.998 to +0.998)
  - 0.0 = Non-rotating (Schwarzschild)
  - +0.94 = Sgr A* (prograde, EHT-constrained)
  - +0.998 = Near-extremal (smallest ISCO)
  - -0.5 = Retrograde example
  - Orange "Retrograde" label appears for negative values

#### Accretion State
- **SANE (Weak B-field)**: Standard accretion, weak magnetic fields
  - β (P_gas/P_mag) ~ 100
  - Weak jets (~1% efficiency)
  - Steady emission

- **MAD (Strong B-field)**: Magnetically Arrested Disk
  - β ~ 1 (magnetic equipartition)
  - Powerful jets (up to 40% efficiency)
  - Variable emission (30-50%)
  - Preferred state for Sgr A* (EHT observations)

- **Intermediate**: Transitional state
  - β ~ 10
  - Moderate jet power
  - Some variability

#### Magnetic Parameters (MAD/Intermediate only)
- **Beta (P_gas/P_mag)**: Magnetic pressure ratio
  - Lower = stronger magnetic fields
  - 1.0 = Equipartition (MAD)
  - 100.0 = Weak field (SANE)

- **Magnetic Flux**: Dimensionless flux Φ_BH threading horizon
  - Affects jet power
  - 50 = Strong (typical MAD)
  - 5 = Weak (typical SANE)

- **Show Magnetic Field Lines**: Visualization toggle

#### Observing Frequency (EHT)
- **230 GHz (1.3 mm)**: Standard EHT frequency
  - Resolution: ~20 microarcseconds
  - Most EHT observations to date

- **345 GHz (0.87 mm)**: Next-generation EHT (Jan 2026)
  - Resolution: ~13 microarcseconds (50% better!)
  - Shows "Next-gen EHT!" label

- **Dual Frequency**: Both frequencies simultaneously

- **Show Resolution Circle**: Displays angular resolution comparison

#### Relativistic Jets
- **Enable Jet Visualization**: Toggle jet rendering

- **Lorentz Factor (Gamma)**: Bulk jet velocity
  - 2.0 = Mildly relativistic (β ~ 0.87)
  - 10.0 = Sgr A* typical
  - 15.0 = M87 typical
  - 50.0 = Blazar (extreme)

- **Opening Angle (deg)**: Jet cone half-angle
  - 10° = Narrow (MAD collimation)
  - 30° = Moderate
  - 60° = Wide (SANE, weak collimation)

- **Jet Base (ly)**: Distance from horizon
  - 0.09 ly = M87 (EHT measured, Jan 2026)
  - 0.01 ly = Sgr A* (smaller mass)

- **Jet Efficiency**: Displayed for MAD state
  - Shows Blandford-Znajek extraction efficiency

#### Physics Visualization Toggles
- **enablePhotonSphere**: Show photon orbit radius
- **enableRedshift**: Color-code gravitational redshift

---

## Example Workflows

### Example 1: Sgr A* (Our Galaxy)

**Goal:** Visualize the supermassive black hole at the center of the Milky Way with latest EHT constraints.

**Steps:**
1. Click "Sgr A* (MAD, a*=0.94)" preset button
2. Verify parameters:
   - Mass: 4,300,000 M☉
   - Spin: 0.94 (near-extremal)
   - State: MAD
   - Beta: 1.0 (equipartition)
   - Flux: 50

3. Set observing frequency:
   - Select "230 GHz (1.3 mm)" for standard EHT

4. Observe:
   - Very small ISCO (2.024 M)
   - Bright, compact inner disk
   - Strong frame dragging
   - Time variability (if MAD flux eruptions active)

**Physics Notes:**
- Sgr A* is highly sub-Eddington (accretion rate ~ 10⁻⁵ Ṁ_Edd)
- MAD state explains EHT magnetic field measurements
- 230 GHz observations from 2017-2022
- Spin constraint: a* = 0.94 ± 0.05 (arXiv:2510.03602)

---

### Example 2: M87* with Jet

**Goal:** Visualize M87's supermassive black hole with its famous relativistic jet.

**Steps:**
1. Set parameters manually:
   - Mass: 6,500,000,000 M☉ (6.5 billion)
   - Spin: 0.9 (high spin from EHT)
   - State: MAD
   - Beta: 1.0
   - Flux: 50

2. Enable jet visualization:
   - Check "Enable Jet Visualization"
   - Lorentz Factor: 15.0
   - Opening Angle: 10° (narrow, MAD collimated)
   - Jet Base: 0.09 ly (EHT measured, Jan 2026!)

3. Set frequency:
   - "345 GHz (0.87 mm)" for highest resolution

4. Observe:
   - Powerful relativistic jet
   - Jet base ~0.09 light-years from horizon
   - Narrow opening angle (strong collimation)
   - Doppler beaming effects

**Physics Notes:**
- M87 jet base detected by EHT (Jan 2026)
- Jet extends 5000+ light-years
- Lorentz factor Γ ~ 10-20 inferred
- MAD state drives powerful jets via BZ mechanism

---

### Example 3: Retrograde Black Hole (LIGO GW241110)

**Goal:** Explore counter-rotating black hole physics.

**Steps:**
1. Set spin to negative:
   - Spin: -0.9 (retrograde)
   - Orange "Retrograde" label appears

2. Observe differences from prograde:
   - ISCO much larger (~6-9 M vs ~1.5 M)
   - Disk edge further from horizon
   - Opposite frame dragging direction
   - Different appearance

3. Compare ISCO sizes:
   - a* = +0.9: ISCO ~ 1.5 M (prograde)
   - a* = 0.0: ISCO = 6.0 M (Schwarzschild)
   - a* = -0.9: ISCO ~ 6.0 M (retrograde)

**Physics Notes:**
- First retrograde binary detected: LIGO GW241110 (Oct 2025)
- Counter-rotating disk has larger ISCO
- Less efficient energy extraction
- Frame dragging opposes orbital motion

---

### Example 4: Most Massive Black Hole (LIGO GW231123)

**Goal:** Simulate the most massive merger ever detected.

**Steps:**
1. Set parameters:
   - Mass: 225 M☉ (final mass from GW231123)
   - Spin: 0.7 (estimated remnant spin)
   - State: SANE (stellar-mass typically SANE)

2. Observe scaling:
   - Event horizon: ~663 km (vs ~3 km for 1 M☉)
   - Hawking temperature: ~10⁻¹⁰ K (extremely cold)
   - Physics identical but scaled by mass

**Physics Notes:**
- Detected: Nov 23, 2023 (published July 2025)
- Primary: ~140 M☉, Secondary: ~100 M☉
- Final: ~225 M☉ (15 M☉ radiated as gravitational waves)
- Most massive black hole merger to date

---

### Example 5: Multi-Frequency Comparison

**Goal:** Compare 230 GHz vs 345 GHz resolution.

**Steps:**
1. Set up Sgr A*:
   - Use preset button
   - Ensure MAD state

2. Select "230 GHz (1.3 mm)":
   - Check "Show Resolution Circle"
   - Observe standard resolution

3. Switch to "345 GHz (0.87 mm)":
   - Notice resolution circle shrinks
   - 50% smaller = 50% better resolution
   - "Next-gen EHT!" label appears

4. Try "Dual Frequency":
   - Combines both observations
   - Multi-color visualization

**Physics Notes:**
- Resolution θ = λ / D_baseline
- 345 GHz has shorter wavelength → better resolution
- EHT achieved 345 GHz observations in Jan 2026
- Probes different optical depths in accretion flow

---

## Parameter Reference

### Mass (M)
**Range:** 0.1 to 250 M☉

**Physical Scaling:**
- Schwarzschild radius: r_s = 2GM/c² = 2.95 km × (M/M☉)
- ISCO radius (Schwarzschild): r_ISCO = 6 GM/c²
- Orbital period at ISCO: P ∝ M
- Hawking temperature: T_H ∝ 1/M

**Examples:**
- Stellar-mass: 3-100 M☉
- Intermediate-mass: 100-10⁵ M☉
- Supermassive: 10⁶-10¹⁰ M☉

### Spin (a*)
**Range:** -0.998 to +0.998

**Physical Effects:**
- **ISCO radius:**
  - a* = +0.998: r_ISCO = 1.237 M (near-extremal prograde)
  - a* = +0.94: r_ISCO = 2.024 M (Sgr A*)
  - a* = 0.0: r_ISCO = 6.0 M (Schwarzschild)
  - a* = -0.998: r_ISCO = 8.994 M (near-extremal retrograde)

- **Frame dragging:** Ω_ZAMO ∝ a*
- **Ergosphere:** Larger for higher |a*|
- **Jet power:** P_BZ ∝ a*² Φ_BH²

**Sign Convention:**
- Positive: Prograde (disk co-rotating with BH)
- Negative: Retrograde (disk counter-rotating)

### Accretion State

**SANE (Standard and Normal Evolution):**
- Weak magnetic field (β ~ 100)
- Steady accretion
- Weak jets (η_jet ~ 1%)
- Lower variability

**MAD (Magnetically Arrested Disk):**
- Strong magnetic field (β ~ 1)
- Magnetic pressure ~ gas pressure
- Powerful jets (η_jet up to 40%)
- Episodic flux eruptions
- 30-50% variability
- Preferred for Sgr A* (EHT observations)

**Intermediate:**
- Transitional state (β ~ 10)
- Moderate magnetic support
- Moderate jets
- Some variability

### Beta (β = P_gas/P_mag)
**Range:** 0.1 to 100 (logarithmic)

**Values:**
- β = 1: Magnetic equipartition (MAD)
- β = 10: Intermediate
- β = 100: Weak magnetic field (SANE)

**Physics:**
- Lower β → stronger magnetic field
- Stronger B → more collimated jets
- Stronger B → higher synchrotron emission

### Magnetic Flux (Φ_BH)
**Range:** 1 to 100

**Values:**
- Φ = 50: Typical MAD (strong flux)
- Φ = 20: Intermediate
- Φ = 5: Typical SANE (weak flux)

**Physics:**
- Higher Φ → more jet power (P_BZ ∝ Φ²)
- Affects BZ extraction efficiency

---

## Troubleshooting

### Issue: Application won't start

**Check:**
1. GPU drivers installed and up-to-date
2. OpenGL 4.6 support available
3. Run `./Blackhole --help` to test basic functionality

**Solution:**
```bash
# Check OpenGL version
glxinfo | grep "OpenGL version"

# Update Mesa drivers (Linux)
sudo pacman -Sy mesa

# Check GPU
lspci | grep VGA
```

### Issue: Low frame rate / stuttering

**Solutions:**
1. Reduce render resolution (if available in settings)
2. Disable expensive effects:
   - Uncheck "Show Magnetic Field Lines"
   - Disable jet visualization
   - Reduce ray marching steps

3. Check GPU usage:
```bash
intel_gpu_top  # For Intel GPUs
```

### Issue: ISCO seems wrong for spin value

**Verify:**
- Prograde vs retrograde:
  - For a* > 0: ISCO should be small (< 6 M)
  - For a* < 0: ISCO should be large (> 6 M)

**Expected values:**
- a* = +0.998: ISCO = 1.237 M ✓
- a* = +0.94: ISCO = 2.024 M ✓
- a* = 0.0: ISCO = 6.0 M ✓
- a* = -0.998: ISCO = 8.994 M ✓

### Issue: Magnetic field parameters have no effect

**Check:**
- Accretion state must be MAD or Intermediate
- SANE state ignores magnetic parameters
- Beta and flux only affect MAD/Intermediate states

---

## Performance Optimization

### For Intel HD 4400 and Similar GPUs:

1. **Reduce resolution:**
   - Lower window size
   - Fullscreen may be slower

2. **Simplify rendering:**
   - Disable photon sphere
   - Disable redshift coloring
   - Reduce maximum ray marching steps

3. **GPU monitoring:**
```bash
# Monitor GPU usage
intel_gpu_top

# Check temperature
sensors
```

### For High-End GPUs:

1. **Enable all features:**
   - Maximum ray marching steps
   - All visualization toggles
   - Highest resolution

2. **Profile performance:**
   - Use built-in profiling (if available)
   - Monitor frame times

---

## Scientific Validation

### How to Cite

If you use this simulator for research or publications, please cite:

**Software:**
```
Blackhole: Real-time Black Hole Renderer with EHT-Constrained Physics (2026)
https://github.com/Oichkatzelesfrettschen/Blackhole
Version 2026.1, EHT-GRMHD validated parameters
```

**Physics References:**
```
EHT Collaboration et al. (2025). "GRMHD modelling of accretion flow
around Sagittarius A* constrained by EHT." arXiv:2510.03602

LIGO-Virgo-KAGRA Collaboration (2025). "Observation of Gravitational Waves
from the Coalescence of a 140 M☉ and 100 M☉ Black Hole Binary."
Physical Review Letters (GW231123)

Blandford, R. D., & Znajek, R. L. (1977). "Electromagnetic extraction
of energy from Kerr black holes." MNRAS, 179, 433
```

### Validation Checks

**Test 1: Schwarzschild ISCO**
- Set spin = 0.0
- Expected ISCO: 6.0 M
- Verify visually and numerically

**Test 2: Near-Extremal Kerr ISCO**
- Set spin = 0.998
- Expected ISCO: 1.237 M
- Should be very close to horizon

**Test 3: Frame Dragging Direction**
- Set spin = +0.5: Frame dragging co-rotates
- Set spin = -0.5: Frame dragging counter-rotates
- Verify opposite directions

**Test 4: Mass Scaling**
- Double the mass: All lengths scale by 2×
- Halve the mass: All lengths scale by 0.5×
- Schwarzschild radius r_s ∝ M

---

## Advanced Topics

### Understanding MAD Flux Eruptions

MAD states exhibit quasi-periodic flux eruptions:
- Period: ~Orbital period at ISCO
- Duty cycle: ~20% (eruption active 20% of time)
- Amplitude: 30-50% variability

**Observing eruptions:**
1. Set state to MAD
2. Enable time evolution (if available)
3. Watch for brightness variations
4. Period ∝ M (hours for Sgr A*, days for M87)

### Blandford-Znajek Jet Power

Electromagnetic energy extraction:

**Formula:**
```
P_BZ ~ (B_H² r_+² c / 4π) Ω_H² f(a*)
η_BZ = P_BZ / (Ṁ c²)
```

**Efficiency:**
- SANE: η ~ 1%
- MAD: η ~ 10-40%
- Depends on: a*², Φ_BH²

**Observing jet power:**
1. Enable jet visualization
2. Set state to MAD
3. Check "Jet Efficiency" display
4. Typical: ~10% for Sgr A*, up to 40% for M87

### Multi-Frequency Synchrotron Emission

**Spectral shape:**
```
F_ν ∝ ν^(-α)  (optically thin)
τ_ν ∝ ν^(-2.1) (self-absorption)
```

**Observing frequency dependence:**
1. Select 230 GHz: Standard emission
2. Select 345 GHz: Higher frequency
   - Slightly lower flux (steeper spectrum)
   - Better resolution
   - Probes different optical depth

---

## Keyboard Shortcuts

*(If implemented)*

- `Space`: Pause/resume time evolution
- `R`: Reset camera
- `1-9`: Preset views
- `S`: Screenshot
- `F11`: Fullscreen toggle
- `ESC`: Exit

---

## Updates and Version History

**Version 2026.1 (2026-01-31):**
- EHT-constrained Sgr A* parameters (a* = 0.94)
- MAD accretion state implementation
- 345 GHz multi-frequency support
- Relativistic jet physics
- LIGO O4 validated mass/spin ranges
- Retrograde spin support (-0.998 to +0.998)
- M87 jet base (0.09 ly from EHT Jan 2026)

**Previous versions:**
- See STATUS.md for development history

---

## Getting Help

**Documentation:**
- README.md: Overview and build instructions
- PHYSICS_ARCHITECTURE.md: Physics foundations
- PHYSICS_UPDATE_2026.md: Latest observational data
- STATUS.md: Development status

**Issues and Bugs:**
- Report at: https://github.com/Oichkatzelesfrettschen/Blackhole/issues

**Questions:**
- Check existing documentation first
- Search closed issues for similar questions
- Open new issue with "Question:" prefix

---

## Appendix: Physics Formulas

### ISCO Radius (Bardeen-Press-Teukolsky 1972)

**Prograde:**
```
r_ISCO/M = 3 + Z2 - √((3 - Z1)(3 + Z1 + 2Z2))
```

**Retrograde:**
```
r_ISCO/M = 3 + Z2 + √((3 - Z1)(3 + Z1 + 2Z2))
```

**Where:**
```
Z1 = 1 + (1 - a*²)^(1/3) [(1 + a*)^(1/3) + (1 - a*)^(1/3)]
Z2 = √(3a*² + Z1²)
```

### Schwarzschild Radius
```
r_s = 2GM/c² = 2.95 km × (M/M☉)
```

### Hawking Temperature
```
T_H = ℏc³/(8πGMk_B) = 6.17×10⁻⁸ K × (M☉/M)
```

### Blandford-Znajek Power
```
P_BZ = κ (B_H² r_+² c / 4π) Ω_H² a*²
```

Where κ is a dimensionless efficiency factor.

---

**End of User Guide**

For the latest updates and detailed physics documentation, see the docs/ directory.
