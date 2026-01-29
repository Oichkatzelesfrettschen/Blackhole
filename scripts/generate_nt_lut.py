#!/usr/bin/env python3
"""
Generate Novikov-Thorne disk temperature/flux lookup table (LUT)

WHY: GPU-efficient disk profile sampling for real-time rendering
WHAT: 2D texture (radius × spin) with temperature and flux values
HOW: Sample Novikov-Thorne formulas, pack into binary texture

Usage:
    python3 generate_nt_lut.py --output data/novikov_thorne_lut.bin
    python3 generate_nt_lut.py --resolution 512 --output data/nt_hires.bin
    python3 generate_nt_lut.py --visualize --output nt_lut.png

Output format:
    - Binary file: float32 array [resolution_r, resolution_a, 2]
    - Channel 0: Normalized temperature (0-1)
    - Channel 1: Normalized flux (0-1)
    - Little-endian, no header
    - Companion JSON metadata file with scales/ranges
"""

import argparse
import json
import struct
import sys
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt


def isco_radius(a_star):
    """Compute ISCO radius (BPT 1972 formula)"""
    a = np.clip(a_star, -0.9999, 0.9999)

    z1 = 1.0 + (1.0 - a*a)**(1/3) * ((1 + a)**(1/3) + (1 - a)**(1/3))
    z2 = np.sqrt(3 * a*a + z1*z1)

    # Prograde orbit ISCO
    r_isco = 3 + z2 - np.sign(a) * np.sqrt((3 - z1) * (3 + z1 + 2*z2))

    return r_isco


def radiative_efficiency(a_star):
    """Compute radiative efficiency (BPT 1972)"""
    r_isco = isco_radius(a_star)
    E_isco = np.sqrt(1.0 - 2.0 / (3.0 * r_isco))
    return 1.0 - E_isco


def normalized_temperature(r, a_star):
    """
    Compute normalized disk temperature

    Page & Thorne (1974) approximation:
    T(r) ~ f(r) / r^(3/4)

    where f(r) = 1 - sqrt(r_isco/r) (zero-torque inner boundary)
    """
    r_isco = isco_radius(a_star)

    # Inside ISCO: no stable disk
    mask = r < r_isco

    # Radial emissivity function
    f_r = np.maximum(0.0, 1.0 - np.sqrt(r_isco / r))

    # Temperature profile (simplified, normalized)
    T = f_r / (r**0.75)
    T[mask] = 0.0

    return T


def normalized_flux(r, a_star):
    """
    Compute normalized disk flux (energy per unit area)

    F(r) ~ f(r) / r³ (Stefan-Boltzmann: F = σT⁴)
    """
    r_isco = isco_radius(a_star)

    mask = r < r_isco

    # Emissivity function
    f_r = np.maximum(0.0, 1.0 - np.sqrt(r_isco / r))

    # Flux profile
    F = f_r / (r**3)
    F[mask] = 0.0

    return F


def generate_lut(resolution_r=256, resolution_a=64, r_min=1.0, r_max=50.0):
    """
    Generate Novikov-Thorne LUT

    Args:
        resolution_r: Radial resolution (pixels)
        resolution_a: Spin resolution (pixels)
        r_min: Minimum radius (in M)
        r_max: Maximum radius (in M)

    Returns:
        lut: Array of shape [resolution_r, resolution_a, 2]
        metadata: Dict with grid parameters and statistics
    """
    print(f"Generating Novikov-Thorne LUT...")
    print(f"  Resolution: {resolution_r} × {resolution_a}")
    print(f"  Radius range: [{r_min}, {r_max}] M")

    # Create coordinate grids
    # Use logarithmic spacing for radius (better sampling near ISCO)
    r_grid = np.logspace(np.log10(r_min), np.log10(r_max), resolution_r)
    a_grid = np.linspace(-0.998, 0.998, resolution_a)

    R, A = np.meshgrid(r_grid, a_grid, indexing='ij')

    # Compute temperature and flux
    print("  Computing temperature field...")
    T = normalized_temperature(R, A)

    print("  Computing flux field...")
    F = normalized_flux(R, A)

    # Normalize to [0, 1] range
    T_max = np.max(T[T > 0])  # Ignore zero values (inside ISCO)
    F_max = np.max(F[F > 0])

    T_norm = T / T_max
    F_norm = F / F_max

    # Pack into LUT array
    lut = np.stack([T_norm, F_norm], axis=-1).astype(np.float32)

    # Compute statistics
    metadata = {
        "resolution_r": resolution_r,
        "resolution_a": resolution_a,
        "r_min": float(r_min),
        "r_max": float(r_max),
        "r_spacing": "logarithmic",
        "a_min": float(a_grid[0]),
        "a_max": float(a_grid[-1]),
        "channels": {
            "0": {
                "name": "temperature",
                "normalized": True,
                "max_value": float(T_max),
                "units": "arbitrary (normalized)"
            },
            "1": {
                "name": "flux",
                "normalized": True,
                "max_value": float(F_max),
                "units": "arbitrary (normalized)"
            }
        },
        "isco_range": {
            "schwarzschild_a0": float(isco_radius(0.0)),
            "kerr_a0p998": float(isco_radius(0.998))
        },
        "efficiency_range": {
            "schwarzschild_a0": float(radiative_efficiency(0.0)),
            "kerr_a0p998": float(radiative_efficiency(0.998))
        }
    }

    # Statistics
    print(f"\n  Temperature statistics:")
    print(f"    Max (normalized): {T_max:.6f}")
    print(f"    Non-zero pixels: {np.sum(T > 0)} / {T.size}")

    print(f"\n  Flux statistics:")
    print(f"    Max (normalized): {F_max:.6f}")
    print(f"    Non-zero pixels: {np.sum(F > 0)} / {F.size}")

    print(f"\n  ISCO validation:")
    print(f"    Schwarzschild (a=0): r_ISCO = {isco_radius(0.0):.6f} M (expect 6.0)")
    print(f"    Kerr (a=0.998): r_ISCO = {isco_radius(0.998):.6f} M (expect ~1.24)")

    print(f"\n  Radiative efficiency:")
    print(f"    Schwarzschild (a=0): η = {radiative_efficiency(0.0):.6f} (expect 0.0572)")
    print(f"    Kerr (a=0.998): η = {radiative_efficiency(0.998):.6f} (expect ~0.42)")

    return lut, metadata


def write_binary(lut, output_path):
    """Write LUT as raw binary (float32, little-endian)"""
    print(f"\nWriting binary LUT to {output_path}...")

    # Flatten and pack
    data = lut.tobytes(order='C')

    with open(output_path, 'wb') as f:
        f.write(data)

    size_mb = len(data) / (1024 * 1024)
    print(f"  Size: {size_mb:.2f} MB")
    print(f"  Shape: {lut.shape}")
    print(f"  Dtype: float32")


def write_metadata(metadata, output_path):
    """Write companion JSON metadata file"""
    json_path = output_path.with_suffix('.json')
    print(f"\nWriting metadata to {json_path}...")

    with open(json_path, 'w') as f:
        json.dump(metadata, f, indent=2)


def visualize(lut, metadata, output_path):
    """Generate visualization plots"""
    print(f"\nGenerating visualization...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Temperature field
    ax = axes[0, 0]
    im = ax.imshow(lut[:, :, 0].T, aspect='auto', origin='lower',
                   extent=[metadata['r_min'], metadata['r_max'],
                           metadata['a_min'], metadata['a_max']],
                   cmap='hot', interpolation='bilinear')
    ax.set_xlabel('Radius (M)')
    ax.set_ylabel('Spin parameter a*')
    ax.set_title('Normalized Temperature')
    ax.set_xscale('log')
    plt.colorbar(im, ax=ax, label='T (normalized)')

    # Draw ISCO lines
    r_vals = np.logspace(np.log10(metadata['r_min']),
                         np.log10(metadata['r_max']), 100)
    a_vals = np.linspace(metadata['a_min'], metadata['a_max'], 100)
    r_isco_vals = [isco_radius(a) for a in a_vals]
    ax.plot(r_isco_vals, a_vals, 'c--', linewidth=2, label='ISCO')
    ax.legend()

    # Flux field
    ax = axes[0, 1]
    im = ax.imshow(lut[:, :, 1].T, aspect='auto', origin='lower',
                   extent=[metadata['r_min'], metadata['r_max'],
                           metadata['a_min'], metadata['a_max']],
                   cmap='plasma', interpolation='bilinear')
    ax.set_xlabel('Radius (M)')
    ax.set_ylabel('Spin parameter a*')
    ax.set_title('Normalized Flux')
    ax.set_xscale('log')
    plt.colorbar(im, ax=ax, label='F (normalized)')
    ax.plot(r_isco_vals, a_vals, 'c--', linewidth=2, label='ISCO')
    ax.legend()

    # Radial profiles (a=0, a=0.5, a=0.998)
    ax = axes[1, 0]

    r_vals = np.logspace(np.log10(metadata['r_min']),
                         np.log10(metadata['r_max']),
                         metadata['resolution_r'])

    for a_star, label, color in [(0.0, 'a=0 (Schwarzschild)', 'blue'),
                                   (0.5, 'a=0.5', 'green'),
                                   (0.998, 'a=0.998 (near-extremal)', 'red')]:
        a_idx = np.argmin(np.abs(np.linspace(metadata['a_min'],
                                              metadata['a_max'],
                                              metadata['resolution_a']) - a_star))

        T_profile = lut[:, a_idx, 0]
        ax.plot(r_vals, T_profile, label=label, color=color, linewidth=2)

        # Mark ISCO
        r_isco_val = isco_radius(a_star)
        ax.axvline(r_isco_val, color=color, linestyle='--', alpha=0.5)

    ax.set_xlabel('Radius (M)')
    ax.set_ylabel('Temperature (normalized)')
    ax.set_title('Temperature Radial Profiles')
    ax.set_xscale('log')
    ax.set_xlim(metadata['r_min'], metadata['r_max'])
    ax.grid(True, alpha=0.3)
    ax.legend()

    # Efficiency vs spin
    ax = axes[1, 1]
    a_vals = np.linspace(-0.998, 0.998, 200)
    eta_vals = [radiative_efficiency(a) for a in a_vals]

    ax.plot(a_vals, eta_vals, 'purple', linewidth=2)
    ax.axhline(0.0572, color='blue', linestyle='--', label='η(a=0) = 0.0572')
    ax.axhline(0.42, color='red', linestyle='--', label='η(a→1) ≈ 0.42')
    ax.set_xlabel('Spin parameter a*')
    ax.set_ylabel('Radiative efficiency η')
    ax.set_title('Radiative Efficiency (BPT 1972)')
    ax.set_xlim(-1, 1)
    ax.set_ylim(0, 0.45)
    ax.grid(True, alpha=0.3)
    ax.legend()

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"  Saved visualization to {output_path}")
    plt.close()


def main():
    parser = argparse.ArgumentParser(
        description='Generate Novikov-Thorne disk LUT for GPU sampling',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )

    parser.add_argument('--output', '-o', type=Path, required=True,
                        help='Output binary file path (e.g., data/novikov_thorne_lut.bin)')
    parser.add_argument('--resolution', '-r', type=int, default=256,
                        help='Radial resolution (default: 256)')
    parser.add_argument('--resolution-spin', '-s', type=int, default=64,
                        help='Spin resolution (default: 64)')
    parser.add_argument('--r-min', type=float, default=1.0,
                        help='Minimum radius in M (default: 1.0)')
    parser.add_argument('--r-max', type=float, default=50.0,
                        help='Maximum radius in M (default: 50.0)')
    parser.add_argument('--visualize', '-v', action='store_true',
                        help='Generate visualization plots (saves as PNG)')
    parser.add_argument('--no-metadata', action='store_true',
                        help='Skip JSON metadata generation')

    args = parser.parse_args()

    # Validate parameters
    if args.resolution < 8 or args.resolution > 4096:
        print(f"ERROR: Resolution must be in range [8, 4096]", file=sys.stderr)
        return 1

    if args.resolution_spin < 8 or args.resolution_spin > 512:
        print(f"ERROR: Spin resolution must be in range [8, 512]", file=sys.stderr)
        return 1

    if args.r_min <= 0 or args.r_max <= args.r_min:
        print(f"ERROR: Invalid radius range: [{args.r_min}, {args.r_max}]", file=sys.stderr)
        return 1

    # Create output directory if needed
    args.output.parent.mkdir(parents=True, exist_ok=True)

    # Generate LUT
    lut, metadata = generate_lut(
        resolution_r=args.resolution,
        resolution_a=args.resolution_spin,
        r_min=args.r_min,
        r_max=args.r_max
    )

    # Write binary
    write_binary(lut, args.output)

    # Write metadata
    if not args.no_metadata:
        write_metadata(metadata, args.output)

    # Visualization
    if args.visualize:
        vis_path = args.output.with_suffix('.png')
        visualize(lut, metadata, vis_path)

    print("\n✓ LUT generation complete!")
    print(f"\nUsage in C++:")
    print(f"  // Load binary LUT")
    print(f'  std::ifstream f("{args.output}", std::ios::binary);')
    print(f"  std::vector<float> lut_data({args.resolution * args.resolution_spin * 2});")
    print(f"  f.read(reinterpret_cast<char*>(lut_data.data()), lut_data.size() * sizeof(float));")
    print(f"\nUsage in GLSL:")
    print(f"  // Upload to GL_TEXTURE_2D_ARRAY or GL_TEXTURE_3D")
    print(f"  // Sample: vec2 temp_flux = texture(nt_lut, vec2(r_normalized, a_normalized)).rg;")

    return 0


if __name__ == '__main__':
    sys.exit(main())
