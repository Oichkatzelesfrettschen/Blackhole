# Phase 10.1: Hawking Radiation Testing Guide

**Created**: 2026-01-02
**Status**: Implementation complete, ready for visual validation

## Quick Start

```bash
cd /home/eirikr/Github/Blackhole/build
./Blackhole
```

In the UI:
1. Navigate to **Physics > Hawking Radiation Glow** section
2. Check **"Enable Hawking Glow"**
3. Test the three presets

---

## Test Plan Overview

### ✓ Completed (Automated)
- [x] Unit tests (13 tests, all passing)
- [x] Build verification (no warnings, no errors)
- [x] LUT generation (512 temperature samples, 256 spectrum samples)
- [x] Physics validation (T_H formula, Wien's law, Stefan-Boltzmann)

### ⏳ Pending (Manual)
- [ ] Visual rendering with 3 presets
- [ ] GPU performance benchmarking

---

## Test 1: Physical Preset (Invisible, Baseline)

**Purpose**: Verify that solar-mass black holes have no visible glow (correct physics)

**Steps**:
1. Launch `./Blackhole`
2. Set black hole mass to **1 M_☉** (solar mass, default)
3. Enable Hawking Glow
4. Select preset: **Physical**
5. Observe rendering

**Expected Result**:
- **No visible glow** around the black hole
- Reason: T_H ≈ 6×10⁻⁸ K (microkelvin) → peak wavelength ~47,000 km (radio waves)
- This is physically correct - solar mass BHs are cold!

**Validation**:
- [ ] Black hole appears completely dark (no thermal emission)
- [ ] Accretion disk still visible (if enabled)
- [ ] No performance regression vs Phase 9

---

## Test 2: Primordial Preset (X-ray Glow)

**Purpose**: Visualize hot primordial black holes with pedagogical scaling

**Steps**:
1. Select preset: **Primordial**
2. Note parameters:
   - Temperature scale: **1×10⁶** (1 million multiplier)
   - Intensity: **2.0**
3. Observe rendering

**Expected Result**:
- **Visible glow** around event horizon
- Color: **Blue-white** (Wien peak in X-ray range, shifted to visible)
- Falloff: Exponential decay with distance from horizon
- Should be brighter than Physical preset

**Validation**:
- [ ] Glow is visible and blue-white colored
- [ ] Glow is concentrated near the event horizon
- [ ] Intensity smoothly decreases with radius
- [ ] No flickering or artifacts
- [ ] Frame rate remains acceptable (target: 60 FPS @ 1080p)

**Physics Note**:
- Real primordial BH at 5×10¹⁴ g: T_H ≈ 2.45×10¹¹ K
- Peak wavelength: ~1.2×10⁻¹² cm (hard X-rays)
- Visualization uses temperature multiplier to make this visible

---

## Test 3: Extreme Preset (Pedagogical Exaggeration)

**Purpose**: Maximum visibility for educational demonstrations

**Steps**:
1. Select preset: **Extreme**
2. Note parameters:
   - Temperature scale: **1×10⁹** (1 billion multiplier)
   - Intensity: **5.0**
3. Observe rendering

**Expected Result**:
- **Bright, vivid glow** completely surrounding the black hole
- Color: **Intense blue-white** (extremely hot)
- Glow extends significantly beyond event horizon
- Dominates the visual

**Validation**:
- [ ] Glow is brightest of all three presets
- [ ] Color is saturated blue-white
- [ ] Glow extends visibly beyond r = 1.5 r_s
- [ ] No performance degradation
- [ ] Additive blending works correctly (glow overlays accretion disk)

**Warning**: This is **not** physically accurate - it's pedagogical exaggeration!

---

## Test 4: Custom Parameter Tuning

**Purpose**: Verify UI controls work smoothly

**Steps**:
1. Start with any preset
2. Adjust **Temperature Scale** slider (logarithmic, 1.0–1×10⁹)
3. Adjust **Glow Intensity** slider (linear, 0.0–5.0)
4. Toggle **Use LUTs** checkbox (precomputed vs direct calculation)

**Expected Behavior**:
- Temperature scale: Glow brightness changes smoothly (log scale)
- Intensity: Glow opacity changes linearly
- Use LUTs: No visible difference (LUT vs direct should match)

**Validation**:
- [ ] Sliders respond smoothly (no lag)
- [ ] Temperature scale changes are smooth across orders of magnitude
- [ ] Intensity slider has noticeable effect
- [ ] LUT toggle shows no visual difference (validates LUT accuracy)
- [ ] Changes apply in real-time (no need to restart)

---

## Test 5: Different Black Hole Masses

**Purpose**: Verify inverse mass relationship (T_H ∝ 1/M)

**Steps**:
1. Set preset: **Primordial**
2. Test masses:
   - 10³⁰ g (very small BH): Should have **bright glow**
   - 10³³ g (solar mass): Should have **faint glow** (with scaling)
   - 10⁴⁰ g (supermassive): Should have **extremely faint glow**

**Expected Result**:
- Smaller masses → hotter → brighter glow
- Larger masses → cooler → dimmer glow
- Temperature ratio: M₂/M₁ = T₁/T₂

**Validation**:
- [ ] 10³⁰ g BH has visible glow (even at low temp scale)
- [ ] 10⁴⁰ g BH is nearly invisible (even at high temp scale)
- [ ] Recommended temp scale changes appropriately with mass

---

## Test 6: Performance Benchmarking

**Purpose**: Verify GPU overhead is <0.5ms @ 1080p

**Method 1: Built-in Frame Time Display**
1. Enable frame time overlay (if available in UI)
2. Record frame times:
   - Baseline (Hawking glow disabled)
   - With glow enabled (Physical preset)
   - With glow enabled (Extreme preset)

**Method 2: Manual Timing**
```bash
# Run headless benchmark (if supported)
./Blackhole --benchmark --enable-hawking-glow --preset=extreme --resolution=1920x1080
```

**Target Performance**:
- Overhead: <0.5ms per frame @ 1080p
- Frame rate: 60 FPS maintained (16.67ms budget)
- Glow overhead: <3% of frame time

**Validation**:
- [ ] Physical preset: negligible overhead (<0.1ms)
- [ ] Primordial preset: <0.3ms overhead
- [ ] Extreme preset: <0.5ms overhead
- [ ] No frame drops during camera movement
- [ ] Consistent performance across different viewing angles

---

## Test 7: Edge Cases

**Purpose**: Verify shader robustness

**Steps**:
1. Test with mass = 0 (should handle gracefully)
2. Test with negative mass (should handle gracefully)
3. Test with extreme camera positions:
   - Very close to horizon (r → r_s)
   - Very far from horizon (r >> r_s)
4. Test preset switching during rendering
5. Test rapid slider adjustments

**Expected Behavior**:
- No crashes or NaN artifacts
- Graceful fallback for invalid parameters
- Smooth transitions when changing parameters

**Validation**:
- [ ] Zero mass: no glow (or error message)
- [ ] Negative mass: no glow (or error message)
- [ ] Near horizon: glow remains stable (no overflow)
- [ ] Far from horizon: glow fades to zero smoothly
- [ ] Preset switching: instant, no flicker
- [ ] Rapid slider movement: smooth, no tearing

---

## Test 8: Integration with Phase 9 Features

**Purpose**: Verify Hawking glow doesn't break existing features

**Steps**:
1. Enable accretion disk
2. Enable Hawking glow
3. Rotate camera through full orbit
4. Toggle features on/off

**Expected Result**:
- Glow and accretion disk render correctly together
- Glow appears **behind** accretion disk (correct depth)
- Additive blending works (glow brightens disk where they overlap)

**Validation**:
- [ ] Accretion disk renders correctly with glow enabled
- [ ] Depth ordering is correct (disk occludes glow)
- [ ] No visual artifacts at boundaries
- [ ] Both features can be toggled independently

---

## Test 9: LUT Sampling Accuracy

**Purpose**: Verify LUT interpolation matches direct calculation

**Method**: Use "Use LUTs" toggle to compare

**Steps**:
1. Set specific parameters (e.g., M = 10³³ g, scale = 1e6)
2. Enable "Use LUTs"
3. Take screenshot
4. Disable "Use LUTs" (uses direct calculation)
5. Take screenshot
6. Compare visually

**Expected Result**:
- **Visually identical** (LUT interpolation accurate)
- Minor differences acceptable (<1% intensity variation)

**Validation**:
- [ ] No visible color shift between LUT and direct
- [ ] No visible brightness shift
- [ ] Both modes render at same performance (LUT may be faster)

---

## Test 10: Shader Compilation

**Purpose**: Verify shaders compile on target GPU

**Automatic Check**: Build system validates shaders
**Manual Check**: Look for OpenGL errors in console

**Expected Output**:
```
Loading Hawking LUTs from: assets/luts
Loading temperature LUT: assets/luts/hawking_temp_lut.csv
Temperature LUT loaded: 512 samples
Loading spectrum LUT: assets/luts/hawking_spectrum_lut.csv
Spectrum LUT loaded: 256 samples
All Hawking LUTs loaded successfully
Created 1D texture: width=512, channels=1, texture=10
Created 1D texture: width=256, channels=3, texture=11
Shader compilation: SUCCESS
```

**Validation**:
- [ ] No shader compilation errors
- [ ] No texture creation errors
- [ ] LUTs load successfully on startup
- [ ] Texture IDs assigned correctly (temp=10, spectrum=11)

---

## Known Issues & Limitations

### Expected Behavior (Not Bugs)
1. **Solar mass BHs invisible at Physical preset**: This is correct! Real BHs are cold.
2. **Glow dominates at Extreme preset**: Intentional pedagogical exaggeration.
3. **Temperature scale slider feels "jumpy"**: Logarithmic scale covers 9 orders of magnitude.

### Potential Issues to Watch For
1. **LUT not found error**: Ensure `assets/luts/` directory exists with CSV files
2. **Texture upload failure**: May indicate GPU memory pressure
3. **NaN artifacts near horizon**: Check for division by zero in shader
4. **Performance cliff at high intensity**: May need to optimize falloff calculation

---

## Success Criteria Summary

**Visual Correctness**:
- ✓ Physical preset shows no glow (correct for solar mass)
- ✓ Primordial preset shows blue-white glow
- ✓ Extreme preset shows bright, vivid glow
- ✓ Glow follows inverse-square + exponential falloff
- ✓ Color matches blackbody spectrum

**Technical Correctness**:
- ✓ Unit tests pass (13/13)
- ✓ Shader compiles without errors
- ✓ LUTs load successfully
- ✓ No OpenGL errors in console

**Performance**:
- ✓ 60 FPS maintained @ 1080p
- ✓ Hawking glow overhead <0.5ms
- ✓ No frame drops during camera movement

**Integration**:
- ✓ Works with Phase 9 features (accretion disk, etc.)
- ✓ No regressions in existing functionality

---

## Next Steps After Testing

1. **If tests pass**: Proceed to Phase 10.2 (Morris-Thorne Wormhole)
2. **If performance issues**: Profile with NVIDIA Nsight or AMD RGP
3. **If visual artifacts**: Check shader logic in `hawking_glow.glsl`
4. **If LUT errors**: Regenerate with `python3 scripts/generate_hawking_lut.py`

---

## Debugging Tips

**No glow visible?**
- Check "Enable Hawking Glow" is checked
- Increase Temperature Scale slider
- Try Extreme preset
- Verify LUTs loaded (check console output)

**Performance issues?**
- Try Physical preset (minimal overhead)
- Reduce intensity slider
- Check GPU utilization with monitoring tool

**Visual artifacts?**
- Update GPU drivers
- Check for NaN in console (enable GL debug context)
- Verify LUT files are not corrupted (re-run generation script)

**Build errors?**
- Run `cmake ..` to reconfigure
- Ensure hawking_renderer.cpp is in PHYSICS_SRC_FILES
- Check for missing includes in hawking_renderer.h

---

## Contact & Reporting

**Implementation Complete**: 2026-01-02
**Phase 10.1 Status**: Ready for visual validation
**Next Phase**: 10.2 Morris-Thorne Wormhole Rendering (Weeks 3-5)
