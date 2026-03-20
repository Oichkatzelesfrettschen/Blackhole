# Physics Implementation Plan - 2026 Updates
## Step-by-Step Code Changes for Latest Observational Data

**Created:** 2026-01-31
**Status:** Ready for Implementation
**Prerequisites:** Build completion, baseline tests passing

---

## Overview

This document provides actionable implementation steps for integrating January 2026 black hole physics data into the Blackhole simulation, organized by priority and validated against EHT, LIGO-Virgo-KAGRA, and GRMHD simulation constraints.

---

## Phase 1: Kerr Parameter Updates (HIGH PRIORITY)

### 1.1 Update Spin Parameter Defaults

**File:** `src/physics/kerr.h` and `src/physics/kerr.cpp`

**Current State:**
```cpp
// Likely has default spin around a* = 0.5 or 0.7
constexpr double DEFAULT_KERR_SPIN = 0.7;
```

**Required Changes:**
```cpp
// Updated based on EHT-constrained GRMHD for Sgr A* (2025-2026)
namespace physics {
    // Sgr A* spin from EHT-GRMHD models (arXiv:2510.03602)
    constexpr double SGR_A_STAR_SPIN = 0.94;

    // M87* spin (observational estimate, intermediate)
    constexpr double M87_STAR_SPIN = 0.5;  // Conservative estimate

    // Default spin for generic black holes
    constexpr double DEFAULT_KERR_SPIN = 0.94;  // Updated from 0.7

    // Spin limits (extended for GW241110 retrograde detection)
    constexpr double MIN_KERR_SPIN = -0.998;  // Retrograde limit
    constexpr double MAX_KERR_SPIN = +0.998;  // Prograde limit
}
```

**Validation:**
- Test ISCO calculations for a* = 0.94: r_ISCO ≈ 1.236 r_s (prograde)
- Test ergosphere for a* = 0.94: r_erg(θ=π/2) ≈ 1.27 r_s
- Verify frame dragging calculations

**Files to Update:**
- `src/physics/kerr.h` - Add new constants
- `src/physics/kerr.cpp` - Update default initialization
- `src/main.cpp` - Update ImGui preset values for Sgr A*
- `tests/physics_test.cpp` - Add validation for a* = 0.94

**Estimated Time:** 30 minutes

---

### 1.2 Add Retrograde Spin Support

**File:** `src/physics/kerr.cpp`

**Current Limitation:**
Most implementations only support prograde spins (a* ≥ 0).

**Required Changes:**

```cpp
// ISCO radius for Kerr black hole (handles retrograde)
double isco_radius_kerr(double M, double a_star) {
    double sign = (a_star >= 0.0) ? 1.0 : -1.0;
    double a = std::abs(a_star);

    double Z1 = 1.0 + std::cbrt(1.0 - a*a) *
                (std::cbrt(1.0 + a) + std::cbrt(1.0 - a));
    double Z2 = std::sqrt(3.0*a*a + Z1*Z1);

    // Prograde: Z1 - sign*Z2, Retrograde: Z1 + |Z2|
    double r_isco = M * (3.0 + Z2 - sign * std::sqrt((3.0 - Z1)*(3.0 + Z1 + 2.0*Z2)));

    return r_isco;
}

// Frame dragging angular velocity (works for retrograde)
double frame_drag_omega(double r, double M, double a_star) {
    double a = a_star * M;
    double r_s = 2.0 * M;

    // Handles both signs of a
    double numerator = r_s * a;
    double denominator = r*r*r + a*a*r + r_s*a*a;

    return numerator / denominator;
}
```

**New Test Cases:**
```cpp
// tests/kerr_retrograde_test.cpp
TEST(KerrRetrogradeTest, ISCORadiusRetrogradeExtreme) {
    double M = 1.0;
    double a_star = -0.998;  // Retrograde
    double r_isco = isco_radius_kerr(M, a_star);

    // Retrograde ISCO is much larger
    EXPECT_NEAR(r_isco, 9.0, 0.1);  // ~9 r_s for extreme retrograde
}

TEST(KerrRetrogradeTest, FrameDragOppositeDirection) {
    double r = 3.0;
    double M = 1.0;
    double a_prograde = 0.9;
    double a_retrograde = -0.9;

    double omega_pro = frame_drag_omega(r, M, a_prograde);
    double omega_retro = frame_drag_omega(r, M, a_retrograde);

    // Opposite signs for frame dragging
    EXPECT_GT(omega_pro, 0.0);
    EXPECT_LT(omega_retro, 0.0);
}
```

**Estimated Time:** 1 hour

---

### 1.3 Update Mass Range Limits

**File:** `src/physics/schwarzschild.h`

**Current State:**
```cpp
// May have upper limit around 100 M☉
constexpr double MAX_BLACK_HOLE_MASS_SOLAR = 100.0;
```

**Required Changes:**
```cpp
// Updated based on LIGO GW231123 detection (225 M☉)
namespace physics {
    constexpr double MIN_BLACK_HOLE_MASS_SOLAR = 1.0;
    constexpr double MAX_BLACK_HOLE_MASS_SOLAR = 250.0;  // Conservative upper limit

    // Known observed systems
    constexpr double GW231123_FINAL_MASS = 225.0;  // Most massive merger observed
    constexpr double SGR_A_STAR_MASS = 4.3e6;      // Million solar masses
    constexpr double M87_STAR_MASS = 6.5e9;         // Billion solar masses
}
```

**Validation:**
- Test Schwarzschild radius for 225 M☉: r_s ≈ 663 km
- Test Hawking temperature for 225 M☉: T_H ≈ 2.74×10⁻¹⁰ K
- Verify gravitational wave energy calculations

**Estimated Time:** 15 minutes

---

## Phase 2: Accretion Disk Physics (HIGH PRIORITY)

### 2.1 Implement MAD Accretion State

**File:** `src/physics/accretion_disk.h` (new file)

**Current State:**
The project likely has a simple Novikov-Thorne thin disk model with procedural noise.

**Required Changes:**

```cpp
// src/physics/accretion_disk.h
#pragma once

namespace physics {

enum class AccretionState {
    SANE,           // Standard and Normal Evolution (weak B-field)
    MAD,            // Magnetically Arrested Disk (strong B-field)
    INTERMEDIATE    // Transitional state
};

struct AccretionDiskConfig {
    double mass;                    // Black hole mass (M☉)
    double spin;                    // Kerr parameter a*
    double accretion_rate;          // Eddington ratio (Ṁ/Ṁ_Edd)
    AccretionState state;           // SANE/MAD/Intermediate
    double magnetic_flux;           // Dimensionless magnetic flux

    // MAD-specific parameters
    double flux_eruption_period;    // Hours (for Sgr A*)
    double magnetic_pressure_ratio; // P_mag / P_gas
};

class AccretionDisk {
public:
    AccretionDisk(const AccretionDiskConfig& config);

    // Novikov-Thorne thin disk model
    double emissivity(double r) const;
    double temperature(double r) const;
    double surface_density(double r) const;

    // MAD-specific physics
    double magnetic_field_strength(double r) const;
    double jet_power() const;
    bool is_flux_eruption_active(double time) const;

    // State transitions
    void update_state(double dt);

private:
    AccretionDiskConfig config_;
    double inner_radius_;   // ISCO
    double outer_radius_;
    double time_;
};

} // namespace physics
```

**Implementation Example:**

```cpp
// src/physics/accretion_disk.cpp
#include "accretion_disk.h"
#include "constants.h"
#include <cmath>

namespace physics {

double AccretionDisk::magnetic_field_strength(double r) const {
    if (config_.state != AccretionState::MAD) {
        return 0.0;  // Negligible for SANE
    }

    // MAD: Strong magnetic field near ISCO
    // B ∝ sqrt(ρ) in equipartition
    double r_isco = inner_radius_;
    double rho = surface_density(r);

    // Magnetic pressure ratio β = P_gas / P_mag
    // For MAD: β ~ 1 (equipartition)
    double beta = 1.0 / config_.magnetic_pressure_ratio;

    // B = sqrt(8π P_mag) = sqrt(8π P_gas / β)
    double P_gas = constants::BOLTZMANN * rho * temperature(r);
    double B = std::sqrt(8.0 * constants::PI * P_gas / beta);

    // Geometry factor: stronger near ISCO
    double geometry_factor = std::pow(r_isco / r, 1.5);

    return B * geometry_factor;
}

bool AccretionDisk::is_flux_eruption_active(double time) const {
    if (config_.state != AccretionState::MAD) {
        return false;
    }

    // MAD exhibits episodic flux eruptions
    // Modeled as periodic with quasi-random duty cycle
    double period = config_.flux_eruption_period * 3600.0;  // Convert hours to seconds
    double phase = std::fmod(time, period) / period;

    // Eruption active for ~20% of cycle
    return (phase > 0.4 && phase < 0.6);
}

double AccretionDisk::jet_power() const {
    if (config_.state == AccretionState::SANE) {
        return 0.01 * config_.accretion_rate;  // Weak jet: ~1% of accretion power
    }

    // MAD: Blandford-Znajek mechanism
    // P_jet ∝ a*² Φ_BH² (spin and magnetic flux)
    double a2 = config_.spin * config_.spin;
    double flux2 = config_.magnetic_flux * config_.magnetic_flux;

    // Normalized jet power (fraction of rest-mass energy)
    double eta_jet = 0.1 * a2 * flux2;  // Can reach 10-40% for MAD

    return eta_jet * config_.accretion_rate;
}

} // namespace physics
```

**ImGui Integration:**

```cpp
// src/main.cpp - Add to Black Hole Parameters panel
static const char* accretion_states[] = { "SANE", "MAD", "Intermediate" };
static int current_accretion_state = 1;  // Default: MAD (for Sgr A*)

ImGui::Combo("Accretion State", &current_accretion_state, accretion_states, 3);

if (current_accretion_state == 1) {  // MAD
    ImGui::SliderFloat("Flux Eruption Period (hours)", &flux_eruption_period, 0.5f, 24.0f);
    ImGui::SliderFloat("Magnetic Pressure Ratio", &mag_pressure_ratio, 0.5f, 2.0f);

    if (ImGui::Button("Trigger Flux Eruption")) {
        // Manually trigger eruption for visualization
    }
}
```

**Estimated Time:** 3-4 hours

---

### 2.2 Update Emissivity LUT Generation

**File:** `scripts/generate_luts.py`

**Current State:**
LUT generation likely uses basic Novikov-Thorne with single accretion state.

**Required Changes:**

```python
# scripts/generate_luts.py
import numpy as np
import h5py
import json

def generate_emissivity_lut_mad(M, a_star, mdot_edd, n_radii=512):
    """
    Generate emissivity LUT for MAD accretion state.

    Parameters:
    - M: black hole mass (solar masses)
    - a_star: dimensionless spin parameter
    - mdot_edd: Eddington ratio (Mdot / Mdot_Edd)
    - n_radii: number of radial grid points
    """
    # ISCO for given spin
    r_isco = compute_isco_radius(M, a_star)

    # Radial grid from ISCO to 100 r_s
    r_grid = np.logspace(np.log10(r_isco), np.log10(100.0), n_radii)

    # Novikov-Thorne base emissivity
    emissivity_base = novikov_thorne_emissivity(r_grid, M, a_star, mdot_edd)

    # MAD enhancement factors
    # 1. Magnetic dissipation near ISCO
    mag_enhancement = np.exp(-(r_grid - r_isco)**2 / (0.5 * r_isco)**2)

    # 2. Episodic flux eruptions (time-averaged)
    flux_modulation = 1.0 + 0.3 * np.sin(2.0 * np.pi * r_grid / (10.0 * r_isco))

    emissivity_mad = emissivity_base * (1.0 + 0.5 * mag_enhancement) * flux_modulation

    return r_grid, emissivity_mad

def save_lut_with_metadata(filename, r_grid, emissivity, metadata):
    """Save LUT with comprehensive metadata."""
    with h5py.File(filename, 'w') as f:
        f.create_dataset('radii', data=r_grid)
        f.create_dataset('emissivity', data=emissivity)

        # Metadata group
        meta = f.create_group('metadata')
        for key, value in metadata.items():
            if isinstance(value, str):
                meta.attrs[key] = value
            else:
                meta.attrs[key] = value

if __name__ == "__main__":
    # Generate LUTs for different states
    metadata_mad = {
        'accretion_state': 'MAD',
        'spin': 0.94,
        'mass_solar': 4.3e6,
        'source': 'Sgr A* EHT-GRMHD (arXiv:2510.03602)',
        'date_generated': '2026-01-31',
        'magnetic_field': 'Strong (equipartition)',
        'units': 'CGS'
    }

    r_grid, emissivity = generate_emissivity_lut_mad(4.3e6, 0.94, 1e-5, 512)
    save_lut_with_metadata('assets/luts/emissivity_mad_sgr_a_star.h5',
                          r_grid, emissivity, metadata_mad)

    print("MAD emissivity LUT generated successfully")
```

**Estimated Time:** 2 hours

---

## Phase 3: Multi-Frequency Support (MEDIUM PRIORITY)

### 3.1 Add 345 GHz Frequency Channel

**File:** `src/physics/radiative_transfer.h` (new or existing)

**Required Changes:**

```cpp
namespace physics {

enum class ObservingFrequency {
    FREQ_230_GHZ,  // EHT baseline
    FREQ_345_GHZ,  // Next-gen EHT (50% better resolution)
    FREQ_XRAY,     // Chandra/NuSTAR band
    FREQ_OPTICAL,
    FREQ_IR
};

struct FrequencyChannel {
    double frequency_hz;
    double wavelength_cm;
    double resolution_factor;  // Relative to 230 GHz

    static FrequencyChannel from_enum(ObservingFrequency freq) {
        switch(freq) {
            case ObservingFrequency::FREQ_230_GHZ:
                return {230e9, 0.13, 1.0};
            case ObservingFrequency::FREQ_345_GHZ:
                return {345e9, 0.087, 1.5};  // 50% better resolution
            case ObservingFrequency::FREQ_XRAY:
                return {2.4e18, 1.24e-8, 1e6};  // 1 keV X-rays
            default:
                return {230e9, 0.13, 1.0};
        }
    }
};

// Frequency-dependent emissivity
double disk_emissivity_at_frequency(double r, double T,
                                     const FrequencyChannel& channel) {
    // Planck function
    double h = constants::PLANCK;
    double c = constants::SPEED_OF_LIGHT;
    double k = constants::BOLTZMANN;
    double nu = channel.frequency_hz;

    double x = h * nu / (k * T);

    // Avoid overflow for x >> 1
    if (x > 100.0) return 0.0;

    double B_nu = (2.0 * h * nu*nu*nu) / (c*c * (std::exp(x) - 1.0));

    return B_nu;
}

} // namespace physics
```

**ImGui UI Addition:**

```cpp
// Add frequency selector to rendering panel
static const char* frequencies[] = {
    "230 GHz (EHT baseline)",
    "345 GHz (Next-gen EHT)",
    "X-ray (Chandra band)",
    "Optical",
    "Infrared"
};
static int current_frequency = 0;

ImGui::Combo("Observing Frequency", &current_frequency, frequencies, 5);

if (current_frequency == 1) {  // 345 GHz
    ImGui::TextColored(ImVec4(0.0f, 1.0f, 0.0f, 1.0f),
                      "Next-gen EHT: 50%% higher resolution");
}
```

**Estimated Time:** 2 hours

---

## Phase 4: Jet Physics (MEDIUM PRIORITY)

### 4.1 M87 Jet Base Positioning

**File:** `src/physics/jet.h` (new file)

**Required Changes:**

```cpp
// src/physics/jet.h
#pragma once
#include <array>

namespace physics {

struct JetConfig {
    double base_distance_light_years;  // Distance from horizon to jet base
    double opening_angle_deg;          // Jet opening angle
    double lorentz_factor;             // Bulk Lorentz factor γ
    double power_erg_per_sec;          // Jet luminosity
    double magnetic_flux;              // Poloidal field strength
};

// M87 jet configuration from EHT Jan 2026 observations
constexpr JetConfig M87_JET = {
    .base_distance_light_years = 0.09,  // From EHT detection
    .opening_angle_deg = 10.0,          // Narrow collimation
    .lorentz_factor = 10.0,             // Mildly relativistic
    .power_erg_per_sec = 1e43,          // High jet power
    .magnetic_flux = 50.0               // Strong poloidal field (MAD)
};

class Jet {
public:
    Jet(const JetConfig& config) : config_(config) {}

    // Check if position is inside jet cone
    bool is_inside_jet(const std::array<double, 3>& pos) const;

    // Synchrotron emissivity inside jet
    double synchrotron_emissivity(const std::array<double, 3>& pos,
                                   double frequency_hz) const;

    // Doppler boosting factor for relativistic jet
    double doppler_factor(const std::array<double, 3>& pos,
                         const std::array<double, 3>& observer_dir) const;

private:
    JetConfig config_;
};

} // namespace physics
```

**Shader Integration:**

```glsl
// shader/include/jet.glsl
#ifndef JET_GLSL
#define JET_GLSL

struct Jet {
    vec3 axis;                    // Jet direction (typically +z)
    float base_distance;          // Distance from horizon in r_s units
    float opening_angle_rad;      // Half-opening angle
    float lorentz_factor;         // Bulk Lorentz factor
    float emissivity_scale;       // Brightness scaling
};

bool is_inside_jet(vec3 pos, Jet jet) {
    float r = length(pos);

    // Only active beyond jet base
    if (r < jet.base_distance) {
        return false;
    }

    // Angle from jet axis
    float cos_theta = dot(normalize(pos), jet.axis);
    float theta = acos(cos_theta);

    return theta < jet.opening_angle_rad;
}

float jet_emissivity(vec3 pos, Jet jet, float frequency) {
    if (!is_inside_jet(pos, jet)) {
        return 0.0;
    }

    // Synchrotron emissivity ∝ B^2 n_e ν^(-0.7)
    // Simplified model: decreases with distance from base
    float r = length(pos);
    float distance_factor = jet.base_distance / r;

    // Frequency dependence (synchrotron spectrum)
    float freq_factor = pow(frequency / 230e9, -0.7);

    return jet.emissivity_scale * distance_factor * distance_factor * freq_factor;
}

#endif // JET_GLSL
```

**Estimated Time:** 3 hours

---

## Phase 5: Validation and Testing (HIGH PRIORITY)

### 5.1 Create 2026 Physics Validation Suite

**File:** `tests/physics_validation_2026_test.cpp` (new file)

```cpp
#include <gtest/gtest.h>
#include "physics/kerr.h"
#include "physics/schwarzschild.h"
#include "physics/accretion_disk.h"

// Test 1: Sgr A* spin parameter from EHT-GRMHD
TEST(Physics2026, SgrAStarSpin) {
    using namespace physics;

    double spin = SGR_A_STAR_SPIN;
    EXPECT_NEAR(spin, 0.94, 0.01) << "Sgr A* spin from EHT-GRMHD (arXiv:2510.03602)";

    // ISCO radius for a* = 0.94
    double M = 1.0;
    double r_isco = isco_radius_kerr(M, spin);
    double expected_isco = 1.236;  // In units of r_s

    EXPECT_NEAR(r_isco, expected_isco, 0.01)
        << "ISCO for a*=0.94 (prograde near-extremal)";
}

// Test 2: Retrograde spin (GW241110)
TEST(Physics2026, RetrogradeSpinSupport) {
    using namespace physics;

    double a_retrograde = -0.9;
    double M = 1.0;

    double r_isco = isco_radius_kerr(M, a_retrograde);

    // Retrograde ISCO is much larger
    EXPECT_GT(r_isco, 6.0) << "Retrograde ISCO should be >> prograde";

    // Frame dragging should be opposite sign
    double omega = frame_drag_omega(3.0, M, a_retrograde);
    EXPECT_LT(omega, 0.0) << "Retrograde frame dragging is negative";
}

// Test 3: GW231123 mass limit
TEST(Physics2026, MassiveBlackHoleMerger) {
    using namespace physics;

    double M_GW231123 = 225.0;  // Solar masses

    EXPECT_LE(M_GW231123, MAX_BLACK_HOLE_MASS_SOLAR)
        << "GW231123 final mass within supported range";

    // Schwarzschild radius
    double r_s_km = schwarzschild_radius_km(M_GW231123);
    double expected = 663.0;  // km

    EXPECT_NEAR(r_s_km, expected, 1.0);
}

// Test 4: MAD accretion state
TEST(Physics2026, MADAccretionPhysics) {
    using namespace physics;

    AccretionDiskConfig config{};
    config.mass = 4.3e6;          // Sgr A*
    config.spin = 0.94;
    config.accretion_rate = 1e-5; // Low accretion
    config.state = AccretionState::MAD;
    config.magnetic_flux = 50.0;

    AccretionDisk disk(config);

    // MAD has strong magnetic field
    double B_field = disk.magnetic_field_strength(2.0);  // At 2 r_s
    EXPECT_GT(B_field, 0.0) << "MAD should have non-zero B-field";

    // MAD has powerful jets
    double jet_power = disk.jet_power();
    EXPECT_GT(jet_power, 0.01) << "MAD jet power > 1% of accretion";
}

// Test 5: 345 GHz frequency support
TEST(Physics2026, NextGenEHTFrequency) {
    using namespace physics;

    auto freq_345 = FrequencyChannel::from_enum(ObservingFrequency::FREQ_345_GHZ);
    auto freq_230 = FrequencyChannel::from_enum(ObservingFrequency::FREQ_230_GHZ);

    // 345 GHz has 50% better resolution
    double resolution_improvement = freq_345.resolution_factor / freq_230.resolution_factor;
    EXPECT_NEAR(resolution_improvement, 1.5, 0.01);

    // Wavelength relationship
    double wavelength_ratio = freq_345.wavelength_cm / freq_230.wavelength_cm;
    double freq_ratio = freq_230.frequency_hz / freq_345.frequency_hz;
    EXPECT_NEAR(wavelength_ratio, freq_ratio, 0.01) << "λ ∝ 1/ν";
}

// Test 6: M87 jet base position
TEST(Physics2026, M87JetBaseDetection) {
    using namespace physics;

    double jet_base_ly = 0.09;  // EHT detection Jan 2026

    // Convert to Schwarzschild radii for M87
    double M_M87 = 6.5e9;  // Solar masses
    double r_s_cm = schwarzschild_radius_cm(M_M87);
    double ly_to_cm = 9.461e17;

    double jet_base_rs = (jet_base_ly * ly_to_cm) / r_s_cm;

    // Jet base should be ~thousands of r_s
    EXPECT_GT(jet_base_rs, 1000.0);
    EXPECT_LT(jet_base_rs, 1e6);
}
```

**Running Tests:**
```bash
cd build/Release
ctest --output-on-failure -R physics_validation_2026
```

**Estimated Time:** 2 hours

---

## Phase 6: Documentation and Presets (LOW PRIORITY)

### 6.1 Create Observational Presets

**File:** `src/presets.h` (new file)

```cpp
#pragma once
#include "physics/kerr.h"
#include "physics/accretion_disk.h"

namespace presets {

struct BlackHolePreset {
    const char* name;
    const char* description;
    double mass_solar;
    double spin;
    AccretionDiskConfig disk;
    bool has_jet;
    const char* reference;
};

// Sgr A* - EHT-constrained (2025-2026)
constexpr BlackHolePreset SGR_A_STAR_2026 = {
    .name = "Sgr A* (EHT 2025-2026)",
    .description = "Milky Way SMBH with MAD accretion and a* = 0.94",
    .mass_solar = 4.3e6,
    .spin = 0.94,
    .disk = {
        .mass = 4.3e6,
        .spin = 0.94,
        .accretion_rate = 1e-5,
        .state = AccretionState::MAD,
        .magnetic_flux = 50.0,
        .flux_eruption_period = 2.0,
        .magnetic_pressure_ratio = 1.0
    },
    .has_jet = false,  // Weak jet for Sgr A*
    .reference = "EHT-GRMHD arXiv:2510.03602"
};

// M87* - With jet base (EHT Jan 2026)
constexpr BlackHolePreset M87_STAR_2026 = {
    .name = "M87* (EHT Jan 2026)",
    .description = "M87 SMBH with detected jet base at 0.09 ly",
    .mass_solar = 6.5e9,
    .spin = 0.5,  // Conservative estimate
    .disk = {
        .mass = 6.5e9,
        .spin = 0.5,
        .accretion_rate = 1e-4,
        .state = AccretionState::MAD,
        .magnetic_flux = 50.0,
        .flux_eruption_period = 24.0,  // Daily for M87 scale
        .magnetic_pressure_ratio = 1.0
    },
    .has_jet = true,
    .reference = "EHT Jan 2026 jet base detection"
};

// GW231123 - Most massive merger
constexpr BlackHolePreset GW231123_REMNANT = {
    .name = "GW231123 Remnant",
    .description = "Most massive black hole merger (225 M☉)",
    .mass_solar = 225.0,
    .spin = 0.7,  // Post-merger spin (estimate)
    .disk = {
        .mass = 225.0,
        .spin = 0.7,
        .accretion_rate = 0.0,  // No disk initially
        .state = AccretionState::SANE,
        .magnetic_flux = 0.0,
        .flux_eruption_period = 0.0,
        .magnetic_pressure_ratio = 10.0
    },
    .has_jet = false,
    .reference = "LIGO GW231123 (July 2025)"
};

} // namespace presets
```

**ImGui Preset Selector:**

```cpp
// src/main.cpp
static const char* preset_names[] = {
    "Custom",
    "Sgr A* (EHT 2025-2026)",
    "M87* (EHT Jan 2026)",
    "GW231123 Remnant",
    "Stellar Mass (10 M☉)",
    "Intermediate Mass (1000 M☉)"
};

static int current_preset = 0;

if (ImGui::Combo("Preset", &current_preset, preset_names, 6)) {
    switch(current_preset) {
        case 1: load_preset(presets::SGR_A_STAR_2026); break;
        case 2: load_preset(presets::M87_STAR_2026); break;
        case 3: load_preset(presets::GW231123_REMNANT); break;
    }
}
```

**Estimated Time:** 1 hour

---

## Implementation Timeline

### Week 1: Core Physics Updates
- **Day 1-2:** Phase 1 (Kerr parameters) - 2 hours
- **Day 3-4:** Phase 2.1 (MAD accretion) - 4 hours
- **Day 5:** Phase 5.1 (Validation tests) - 2 hours

### Week 2: Advanced Features
- **Day 1-2:** Phase 2.2 (LUT generation) - 2 hours
- **Day 3-4:** Phase 3 (Multi-frequency) - 2 hours
- **Day 5:** Phase 4 (Jet physics) - 3 hours

### Week 3: Polish and Validation
- **Day 1-2:** Phase 6 (Presets and docs) - 2 hours
- **Day 3-5:** Comprehensive testing and validation

**Total Estimated Time:** 20-25 hours of development

---

## Validation Checklist

Before considering implementation complete:

- [ ] All physics_validation_2026 tests pass
- [ ] Sgr A* preset renders with a* = 0.94
- [ ] Retrograde spins work correctly (negative frame dragging)
- [ ] GW231123 mass (225 M☉) within supported range
- [ ] MAD accretion state shows flux eruptions
- [ ] 345 GHz frequency available in UI
- [ ] M87 preset shows jet base at 0.09 ly
- [ ] LUT metadata includes 2026 references
- [ ] Shader validation passes (21/21 shaders)
- [ ] Existing regression tests still pass
- [ ] Performance impact < 10% vs baseline
- [ ] Documentation updated in PHYSICS_ARCHITECTURE.md

---

## References

All changes are based on:

1. **EHT Sgr A* GRMHD:** arXiv:2510.03602 (a* = 0.94)
2. **EHT M87 Jet Base:** EHT Jan 2026 announcement (0.09 ly)
3. **LIGO GW231123:** Most massive merger (225 M☉)
4. **LIGO GW241110:** First retrograde binary detection
5. **GRMHD Dynamo:** arXiv:2512.02129 (MAD jet physics)

---

## Next Steps After Implementation

1. **GPU Optimization:** Profile with intel_gpu_top, optimize shader hot paths
2. **Synthetic Observations:** Generate EHT-comparable images at 230/345 GHz
3. **Time Evolution:** Implement MAD flux eruption animations
4. **Polarization:** Add magnetic field visualization
5. **GW Waveforms:** Generate gravitational wave signatures for mergers

---

**Document Version:** 1.0
**Last Updated:** 2026-01-31
**Ready for Implementation:** Yes (pending build completion)
