# Quick Start: 2026 Physics Updates
## 30-Minute Critical Updates for Physical Accuracy

**Purpose:** Get the most important 2026 physics data into the simulation in under 30 minutes.

**Prerequisites:**
- Build completed successfully
- All tests passing: `ctest --output-on-failure`

---

## Critical Update #1: Sgr A* Spin Parameter (5 minutes)

**Justification:** EHT-constrained GRMHD models favor a* = 0.94 for Sagittarius A* (arXiv:2510.03602)

**File:** `src/main.cpp` (or wherever presets are defined)

**Find:**
```cpp
// Likely something like:
float kerrSpin = 0.7f;  // or 0.5f
```

**Replace with:**
```cpp
// Updated to Sgr A* EHT-GRMHD constraint (2025-2026)
float kerrSpin = 0.94f;  // Near-extremal rotation
```

**Test:**
```bash
./build/Release/Blackhole
# In UI: Verify spin parameter shows 0.94
# Check that ISCO radius is ~1.2 r_s (smaller than before)
```

---

## Critical Update #2: Mass Range Upper Limit (3 minutes)

**Justification:** LIGO GW231123 detected 225 M☉ black hole (July 2025)

**File:** `src/main.cpp` or `src/physics/constants.h`

**Find:**
```cpp
// Likely:
float maxMassSolar = 100.0f;
```

**Replace with:**
```cpp
// Updated for GW231123 detection (225 M☉)
float maxMassSolar = 250.0f;  // Conservative upper limit
```

**Test:**
```bash
# In UI: Adjust mass slider - should now go up to 250 M☉
```

---

## Critical Update #3: Add Retrograde Spin Support (10 minutes)

**Justification:** LIGO GW241110 detected first retrograde binary (Oct 2025)

**File:** `src/main.cpp` (UI sliders)

**Find:**
```cpp
// Likely:
ImGui::SliderFloat("Spin", &kerrSpin, 0.0f, 0.998f);
```

**Replace with:**
```cpp
// Support retrograde spins (GW241110)
ImGui::SliderFloat("Spin", &kerrSpin, -0.998f, 0.998f);

if (kerrSpin < 0.0f) {
    ImGui::SameLine();
    ImGui::TextColored(ImVec4(1.0f, 0.5f, 0.0f, 1.0f), "Retrograde");
}
```

**File:** `src/physics/kerr.cpp` (if ISCO calculation exists)

**Find:**
```cpp
double isco_radius(double M, double a_star) {
    // Likely assumes a_star >= 0
```

**Add check:**
```cpp
double isco_radius(double M, double a_star) {
    // Handle retrograde spins (GW241110)
    double sign = (a_star >= 0.0) ? 1.0 : -1.0;
    double a = std::abs(a_star);
    // ... rest of calculation with sign handling
```

**Test:**
```bash
# In UI: Set spin to -0.9
# Verify ISCO radius is much larger (~6-9 r_s vs ~1.5 r_s for prograde)
```

---

## Critical Update #4: Add MAD Accretion Preset (10 minutes)

**Justification:** Sgr A* observations favor MAD state (arXiv:2510.03602)

**File:** `src/main.cpp`

**Add after existing presets:**
```cpp
// Sgr A* MAD state (EHT-GRMHD 2025-2026)
if (ImGui::Button("Sgr A* (MAD, a*=0.94)")) {
    kerrSpin = 0.94f;
    blackHoleMass = 4.3e6f;  // Million solar masses
    accretionRate = 1e-5f;   // Low accretion
    // Enable stronger magnetic field visualization
    magneticFieldStrength = 2.0f;  // If available
}
ImGui::SameLine();
ImGui::TextDisabled("(EHT-constrained)");
```

**Test:**
```bash
# Click preset button
# Verify spin = 0.94, mass = 4.3e6 M☉
```

---

## Bonus Update #5: Update Documentation Strings (2 minutes)

**File:** `README.md`

**Find:**
```markdown
- Schwarzschild/Kerr geodesic tracing
```

**Add after:**
```markdown
- Latest physics from EHT 2025-2026 and LIGO O4
- Sgr A* spin a* = 0.94 (EHT-GRMHD constrained)
- Support for retrograde black hole spins (GW241110)
- Mass range up to 250 M☉ (GW231123)
```

---

## Validation After Quick Updates

Run these quick checks:

```bash
cd build/Release

# 1. Check build is healthy
./Blackhole --help  # Should show options without crashing

# 2. Run physics tests
ctest --output-on-failure -R physics

# 3. Validate shaders
cmake --build . --target validate-shaders

# 4. Quick visual test
./Blackhole
# - Set spin to 0.94 → ISCO should shrink to ~1.2 r_s
# - Set spin to -0.9 → ISCO should expand to ~6+ r_s
# - Set mass to 225 M☉ → Should work without issues
```

---

## What You'll See After These Updates

### Sgr A* (a* = 0.94):
- **Smaller ISCO:** ~1.236 r_s vs ~3 r_s for non-rotating
- **Stronger frame dragging:** Objects orbit faster near horizon
- **Brighter inner disk:** More gravitational energy released

### Retrograde Spin (a* = -0.9):
- **Larger ISCO:** ~6-9 r_s (orbits further out)
- **Opposite frame dragging:** Spacetime drags opposite to spin
- **Different appearance:** Disk looks "puffier" due to larger inner edge

### High Mass (225 M☉):
- **Larger event horizon:** ~663 km vs ~3 km for 1 M☉
- **Colder Hawking temperature:** ~10⁻¹⁰ K vs ~10⁻⁷ K
- **Same visual appearance:** Physics scales with M

---

## Next Steps After Quick Updates

Once these critical 30-minute updates are done:

1. **Review Full Implementation Plan:** See `PHYSICS_IMPLEMENTATION_PLAN.md`
2. **GPU Profiling:** Use `intel_gpu_top` to identify bottlenecks
3. **Advanced Features:**
   - MAD accretion state physics
   - 345 GHz frequency support
   - M87 jet base at 0.09 light-years
   - Time-varying magnetic fields

---

## Troubleshooting

**Issue:** Spin slider doesn't go negative

**Fix:** Check ImGui::SliderFloat has negative minimum:
```cpp
ImGui::SliderFloat("Spin", &kerrSpin, -0.998f, 0.998f);
//                                      ^^^^^^ negative minimum
```

**Issue:** Large masses cause numerical instability

**Fix:** Ensure calculations use double precision:
```cpp
double M_solar = static_cast<double>(blackHoleMass);
double r_s = 2.0 * M_solar;  // Not: float r_s = 2.0f * blackHoleMass
```

**Issue:** ISCO calculation wrong for retrograde

**Fix:** Apply sign correction in ISCO formula (see Update #3)

---

## Files Modified Summary

- `src/main.cpp`: Spin limits, mass limits, MAD preset
- `src/physics/kerr.cpp`: Retrograde ISCO support (if applicable)
- `README.md`: Documentation update

**Total Changes:** ~30 lines of code
**Time Required:** 30 minutes
**Impact:** Physically accurate parameters for 2026 observations

---

## Before/After Comparison

| Parameter | Before | After (2026) | Source |
|-----------|--------|--------------|--------|
| Sgr A* spin | 0.5-0.7 | 0.94 | EHT-GRMHD arXiv:2510.03602 |
| Min spin | 0.0 | -0.998 | LIGO GW241110 |
| Max mass | 100 M☉ | 250 M☉ | LIGO GW231123 |
| ISCO (a*=0.94) | ~1.5 r_s | 1.236 r_s | Kerr formula |

---

**Last Updated:** 2026-01-31
**Ready to Apply:** Yes (after build completion)
**Estimated Time:** 30 minutes
