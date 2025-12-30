#!/usr/bin/env python3
"""
Stub LUT generator for radiative transfer (TARDIS cleanroom reference).
Produces a mock spectrum LUT when TARDIS is unavailable.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def generate_mock_spectrum(wavelength_min: float, wavelength_max: float, bins: int) -> tuple[list[float], list[float]]:
    wavelengths = [
        wavelength_min + (wavelength_max - wavelength_min) * i / (bins - 1)
        for i in range(bins)
    ]
    mu = 0.5 * (wavelength_min + wavelength_max)
    sigma = 0.15 * (wavelength_max - wavelength_min)
    intensities = [math.exp(-0.5 * ((wl - mu) / sigma) ** 2) for wl in wavelengths]
    peak = max(intensities) if intensities else 1.0
    intensities = [val / peak for val in intensities]
    return wavelengths, intensities


def write_csv(path: Path, wavelengths: list[float], intensities: list[float]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        handle.write("wavelength_angstrom,intensity\n")
        for wl, val in zip(wavelengths, intensities):
            handle.write(f"{wl:.6f},{val:.8f}\n")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate a stub radiative transfer LUT.")
    parser.add_argument("--output-dir", default="assets/luts", help="Output directory")
    parser.add_argument("--bins", type=int, default=256, help="Number of wavelength bins")
    parser.add_argument("--wavelength-min", type=float, default=3000.0, help="Min wavelength (Angstrom)")
    parser.add_argument("--wavelength-max", type=float, default=9000.0, help="Max wavelength (Angstrom)")
    parser.add_argument("--mode", choices=["mock", "tardis"], default="mock",
                        help="Use mock spectrum or attempt TARDIS (falls back to mock)")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    source = "mock"
    if args.mode == "tardis":
        try:
            import tardis  # noqa: F401
            source = "tardis"
        except Exception:
            source = "mock"

    wavelengths, intensities = generate_mock_spectrum(
        args.wavelength_min, args.wavelength_max, args.bins
    )

    csv_path = output_dir / "rt_spectrum_lut.csv"
    meta_path = output_dir / "rt_spectrum_meta.json"

    write_csv(csv_path, wavelengths, intensities)

    meta = {
        "source": source,
        "bins": args.bins,
        "wavelength_min_angstrom": args.wavelength_min,
        "wavelength_max_angstrom": args.wavelength_max,
        "units": {"wavelength": "Angstrom", "intensity": "normalized"},
        "notes": "Stub generator; replace with TARDIS-driven output when available.",
    }
    meta_path.write_text(json.dumps(meta, indent=2) + "\n", encoding="utf-8")

    print(f"Wrote {csv_path} and {meta_path} ({source})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
