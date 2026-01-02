#!/usr/bin/env python3
"""
Generate Hawking Radiation Lookup Tables (LUTs)

This script generates precomputed LUTs for Hawking radiation visualization:
1. hawking_temp_lut.csv: Temperature T_H(M) for 512 log-spaced masses
2. hawking_spectrum_lut.csv: Blackbody RGB colors for temperatures
3. hawking_meta.json: Metadata for LUT usage

Physical formulas from hawking.h:
  T_H = ℏc³/(8πGMk_B)
  Planck distribution: B_ν(T) = (2hν³/c²) / (exp(hν/kT) - 1)
  Wien's law: λ_peak = b/T where b = 2.898×10⁻³ m·K

Phase 10.1: Quick path implementation for Hawking thermal glow
"""

import numpy as np
import csv
import json
from pathlib import Path

# ============================================================================
# Physical Constants (CGS units to match C++ implementation)
# ============================================================================

# Fundamental constants
C = 2.99792458e10        # Speed of light [cm/s]
G = 6.67430e-8           # Gravitational constant [cm³/g/s²]
HBAR = 1.054571817e-27   # Reduced Planck constant [erg·s]
K_B = 1.380649e-16       # Boltzmann constant [erg/K]
PI = np.pi

# Derived constants
M_SUN = 1.98847e33       # Solar mass [g]
WIEN_CONSTANT = 0.2898   # Wien displacement constant [cm·K]

# ============================================================================
# Hawking Temperature Functions
# ============================================================================

def hawking_temperature(mass):
    """
    Compute Hawking temperature for Schwarzschild black hole.

    T_H = ℏc³ / (8πGMk_B)

    Args:
        mass: Black hole mass [g]

    Returns:
        Hawking temperature [K]
    """
    if mass <= 0:
        return np.inf
    return HBAR * C**3 / (8.0 * PI * G * mass * K_B)

def schwarzschild_radius(mass):
    """
    Compute Schwarzschild radius.

    r_s = 2GM/c²

    Args:
        mass: Black hole mass [g]

    Returns:
        Schwarzschild radius [cm]
    """
    return 2.0 * G * mass / (C * C)

# ============================================================================
# Blackbody Spectrum Functions
# ============================================================================

def planck_blackbody(wavelength, temperature):
    """
    Compute Planck blackbody spectral radiance.

    B_λ(T) = (2hc²/λ⁵) / (exp(hc/λkT) - 1)

    Args:
        wavelength: Wavelength [cm]
        temperature: Temperature [K]

    Returns:
        Spectral radiance [erg/s/cm²/cm/sr]
    """
    if temperature <= 0 or wavelength <= 0:
        return 0.0

    # Planck constant (not reduced)
    h = 2.0 * PI * HBAR

    # Exponent argument
    x = h * C / (wavelength * K_B * temperature)

    # Avoid overflow
    if x > 700:
        return 0.0

    # Planck function
    numerator = 2.0 * h * C * C / (wavelength**5)
    denominator = np.exp(x) - 1.0

    return numerator / denominator

def wavelength_to_rgb(temperature):
    """
    Convert blackbody temperature to RGB color.

    Uses Planck distribution at RGB wavelengths:
    - Red: 700 nm
    - Green: 546 nm
    - Blue: 435 nm

    Args:
        temperature: Temperature [K]

    Returns:
        RGB color as (r, g, b) tuple, normalized to [0,1]
    """
    # RGB wavelengths in cm
    lambda_r = 700e-7  # 700 nm
    lambda_g = 546e-7  # 546 nm
    lambda_b = 435e-7  # 435 nm

    # Compute Planck distribution at each wavelength
    r = planck_blackbody(lambda_r, temperature)
    g = planck_blackbody(lambda_g, temperature)
    b = planck_blackbody(lambda_b, temperature)

    # Normalize to peak
    rgb = np.array([r, g, b])
    peak = np.max(rgb)
    if peak > 0:
        rgb /= peak

    return tuple(rgb)

# ============================================================================
# LUT Generation
# ============================================================================

def generate_temperature_lut(output_path, n_samples=512):
    """
    Generate temperature LUT: T_H(M) for log-spaced masses.

    Mass range: 10¹⁴ g (primordial) to 10⁴² g (supermassive)
    This spans T_H from ~10¹² K (extreme) to ~10⁻¹⁴ K (cold)

    Args:
        output_path: Output CSV file path
        n_samples: Number of samples (default: 512)
    """
    print(f"Generating temperature LUT with {n_samples} samples...")

    # Log-spaced masses from 10^14 g to 10^42 g
    log_mass_min = 14.0  # Primordial BH (evaporating now)
    log_mass_max = 42.0  # Supermassive BH (M87*)

    log_masses = np.linspace(log_mass_min, log_mass_max, n_samples)
    masses = 10.0**log_masses

    # Compute temperatures
    temperatures = np.array([hawking_temperature(m) for m in masses])
    radii = np.array([schwarzschild_radius(m) for m in masses])

    # Write CSV
    with open(output_path, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['# Hawking Temperature LUT'])
        writer.writerow(['# Columns: Mass [g], Temperature [K], Schwarzschild Radius [cm]'])
        writer.writerow(['Mass_g', 'Temperature_K', 'Radius_cm'])

        for m, t, r in zip(masses, temperatures, radii):
            writer.writerow([f'{m:.6e}', f'{t:.6e}', f'{r:.6e}'])

    print(f"  Wrote {n_samples} temperature samples to {output_path}")
    print(f"  Mass range: {masses[0]:.2e} g to {masses[-1]:.2e} g")
    print(f"  Temp range: {temperatures[-1]:.2e} K to {temperatures[0]:.2e} K")

    return masses, temperatures

def generate_spectrum_lut(output_path, n_samples=256):
    """
    Generate spectrum LUT: Temperature → RGB mapping.

    Temperature range: 10³ K to 10¹² K
    Covers visible to X-ray peak wavelengths.

    Args:
        output_path: Output CSV file path
        n_samples: Number of samples (default: 256)
    """
    print(f"Generating spectrum LUT with {n_samples} samples...")

    # Log-spaced temperatures from 10^3 K to 10^12 K
    log_temp_min = 3.0   # Infrared peak
    log_temp_max = 12.0  # X-ray peak (primordial BH)

    log_temps = np.linspace(log_temp_min, log_temp_max, n_samples)
    temperatures = 10.0**log_temps

    # Compute RGB colors
    rgb_colors = np.array([wavelength_to_rgb(t) for t in temperatures])

    # Write CSV
    with open(output_path, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['# Hawking Spectrum LUT'])
        writer.writerow(['# Columns: Temperature [K], Red, Green, Blue (normalized)'])
        writer.writerow(['Temperature_K', 'Red', 'Green', 'Blue'])

        for t, (r, g, b) in zip(temperatures, rgb_colors):
            writer.writerow([f'{t:.6e}', f'{r:.6f}', f'{g:.6f}', f'{b:.6f}'])

    print(f"  Wrote {n_samples} spectrum samples to {output_path}")
    print(f"  Temp range: {temperatures[0]:.2e} K to {temperatures[-1]:.2e} K")

    return temperatures, rgb_colors

def generate_metadata(output_path, mass_range, temp_range, n_temp_samples, n_spec_samples):
    """
    Generate JSON metadata for LUTs.

    Args:
        output_path: Output JSON file path
        mass_range: (min_mass, max_mass) tuple [g]
        temp_range: (min_temp, max_temp) tuple [K]
        n_temp_samples: Number of temperature LUT samples
        n_spec_samples: Number of spectrum LUT samples
    """
    print("Generating metadata...")

    metadata = {
        "description": "Hawking Radiation LUT Metadata",
        "generation_date": "2026-01-02",
        "phase": "10.1",
        "temperature_lut": {
            "filename": "hawking_temp_lut.csv",
            "samples": n_temp_samples,
            "mass_min_g": f"{mass_range[0]:.6e}",
            "mass_max_g": f"{mass_range[1]:.6e}",
            "temperature_min_K": f"{temp_range[1]:.6e}",
            "temperature_max_K": f"{temp_range[0]:.6e}",
            "mass_units": "grams",
            "temperature_units": "Kelvin",
            "notes": "Log-spaced masses from primordial to supermassive BH"
        },
        "spectrum_lut": {
            "filename": "hawking_spectrum_lut.csv",
            "samples": n_spec_samples,
            "temperature_min_K": "1.0e3",
            "temperature_max_K": "1.0e12",
            "rgb_range": "[0,1] normalized",
            "wavelengths_nm": {
                "red": 700,
                "green": 546,
                "blue": 435
            },
            "notes": "Blackbody RGB colors from Planck distribution"
        },
        "physical_constants": {
            "c_cm_s": f"{C:.6e}",
            "G_cgs": f"{G:.6e}",
            "hbar_erg_s": f"{HBAR:.6e}",
            "k_B_erg_K": f"{K_B:.6e}",
            "M_sun_g": f"{M_SUN:.6e}"
        },
        "example_values": {
            "solar_mass_BH": {
                "mass_g": f"{M_SUN:.6e}",
                "temperature_K": f"{hawking_temperature(M_SUN):.6e}",
                "note": "Extremely cold - invisible"
            },
            "primordial_BH": {
                "mass_g": "5.0e14",
                "temperature_K": f"{hawking_temperature(5e14):.6e}",
                "note": "Evaporating now - X-ray peak"
            }
        }
    }

    with open(output_path, 'w') as jsonfile:
        json.dump(metadata, jsonfile, indent=2)

    print(f"  Wrote metadata to {output_path}")

# ============================================================================
# Main
# ============================================================================

def main():
    """Generate all Hawking radiation LUTs."""
    # Output directory
    output_dir = Path(__file__).parent.parent / "assets" / "luts"
    output_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 70)
    print("HAWKING RADIATION LUT GENERATION")
    print("Phase 10.1: Quick Path Implementation")
    print("=" * 70)

    # Generate temperature LUT
    temp_lut_path = output_dir / "hawking_temp_lut.csv"
    masses, temperatures = generate_temperature_lut(temp_lut_path, n_samples=512)

    # Generate spectrum LUT
    spec_lut_path = output_dir / "hawking_spectrum_lut.csv"
    spec_temps, rgb_colors = generate_spectrum_lut(spec_lut_path, n_samples=256)

    # Generate metadata
    meta_path = output_dir / "hawking_meta.json"
    mass_range = (masses[0], masses[-1])
    temp_range = (temperatures[0], temperatures[-1])
    generate_metadata(meta_path, mass_range, temp_range,
                     n_temp_samples=512, n_spec_samples=256)

    print("=" * 70)
    print("GENERATION COMPLETE")
    print(f"Output directory: {output_dir}")
    print("=" * 70)

if __name__ == "__main__":
    main()
