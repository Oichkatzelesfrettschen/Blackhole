#!/usr/bin/env python3
"""Blackbody color and luminance against temperature for the observer sky.

Writes assets/luts/blackbody_cie_lut.csv and blackbody_cie_meta.json. Row k
holds log10 T = LOG10_T_MIN + k * LOG10_T_STEP and

  r, g, b   linear sRGB (D65) of a Planck spectrum at T, normalized to unit
            Rec. 709 luminance (0.2126 r + 0.7152 g + 0.0722 b = 1), with
            out-of-gamut negatives clipped to zero before normalizing;
  log10_Y   log10 of the photopic luminance 683 lm/W * integral of
            B_lambda(T) ybar(lambda) dlambda, in cd/m^2.

A spectrum blueshifted by g is a Planck spectrum at g T (I_nu / nu^3 is
invariant), so the renderer looks up g T. The table spans T = 1 K (log10_Y
about -7500: the visible band sits 2.6e4 e-folds down the Wien tail) to
1e11 K (Rayleigh-Jeans, where Y grows as T and the color no longer changes),
so a float stores log10_Y without underflow.

Color matching functions: the multi-lobe Gaussian fit of Wyman, Sloan &
Shirley, "Simple Analytic Approximations to the CIE XYZ Color Matching
Functions", JCGT 2(2), 2013, Sec. 2.1 (1931 2-degree observer), integrated
over 360-830 nm at 0.5 nm. Planck terms are summed in log space so that the
cold end does not underflow. Below T = 794 K (log10 T = 2.9) the visible
light of a blackbody comes from beyond 750 nm, where the Gaussian lobes' tails
depart from the tabulated CIE functions (the fit's ybar exceeds its xbar
there), so those rows keep the 794 K color; log10_Y still follows Planck.

Usage: $PYTHON scripts/generate_blackbody_cie_lut.py [--out-dir assets/luts]
"""

import argparse
import csv
import json
from pathlib import Path

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]

H = 6.62607015e-34  # Planck constant [J s] (SI 2019, exact)
C = 2.99792458e8  # speed of light [m/s] (exact)
K_B = 1.380649e-23  # Boltzmann constant [J/K] (exact)
LUMINOUS_EFFICACY = 683.0  # lm/W at 540 THz (SI definition of the candela)

LOG10_T_MIN = 0.0
LOG10_T_MAX = 11.0
LOG10_T_STEP = 0.01
LOG10_T_CHROMA_FLOOR = 2.9

WAVELENGTH_NM = np.arange(360.0, 830.0 + 0.25, 0.5)

# XYZ (D65 white) to linear sRGB, IEC 61966-2-1.
XYZ_TO_SRGB = np.array(
    [
        [3.2406, -1.5372, -0.4986],
        [-0.9689, 1.8758, 0.0415],
        [0.0557, -0.2040, 1.0570],
    ]
)
REC709_LUMA = np.array([0.2126, 0.7152, 0.0722])


def lobe(wavelength: Array, mean: float, sigma_below: float, sigma_above: float) -> Array:
    sigma = np.where(wavelength < mean, sigma_below, sigma_above)
    return np.exp(-0.5 * ((wavelength - mean) / sigma) ** 2)


def cie_1931(wavelength: Array) -> Array:
    """Wyman-Sloan-Shirley multi-lobe fit, wavelength in nm."""
    xbar = (
        1.056 * lobe(wavelength, 599.8, 37.9, 31.0)
        + 0.362 * lobe(wavelength, 442.0, 16.0, 26.7)
        - 0.065 * lobe(wavelength, 501.1, 20.4, 26.2)
    )
    ybar = 0.821 * lobe(wavelength, 568.8, 46.9, 40.5) + 0.286 * lobe(wavelength, 530.9, 16.3, 31.1)
    zbar = 1.217 * lobe(wavelength, 437.0, 11.8, 36.0) + 0.681 * lobe(wavelength, 459.0, 26.0, 13.8)
    return np.stack([xbar, ybar, zbar])


def log_planck(wavelength_m: Array, temperature: float) -> Array:
    """ln B_lambda(T) in W m^-3 sr^-1, stable for any hc / (lambda k T)."""
    a = H * C / (wavelength_m * K_B * temperature)
    # ln(expm1(a)) = a + ln(1 - e^-a) for large a; log(expm1) for small.
    large = a + np.log1p(-np.exp(-np.minimum(a, 700.0)))
    small = np.log(np.expm1(np.minimum(a, 30.0)))
    log_expm1 = np.where(a > 30.0, large, small)
    return np.log(2.0 * H * C * C) - 5.0 * np.log(wavelength_m) - log_expm1


def row(log10_t: float, cmf: Array, wavelength_m: Array, step_m: float) -> tuple[Array, float]:
    temperature = 10.0**log10_t
    log_b = log_planck(wavelength_m, temperature)
    peak = log_b.max()
    weights = np.exp(log_b - peak)
    xyz = (cmf * weights).sum(axis=1) * step_m  # times e^peak
    rgb = np.clip(XYZ_TO_SRGB @ xyz, 0.0, None)
    rgb /= REC709_LUMA @ rgb
    log10_y = float((np.log(LUMINOUS_EFFICACY * xyz[1]) + peak) / np.log(10.0))
    return rgb, log10_y


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out-dir", default="assets/luts", type=Path)
    args = parser.parse_args()

    cmf = cie_1931(WAVELENGTH_NM)
    wavelength_m = WAVELENGTH_NM * 1e-9
    step_m = 0.5e-9
    count = round((LOG10_T_MAX - LOG10_T_MIN) / LOG10_T_STEP) + 1
    floor_rgb, _ = row(LOG10_T_CHROMA_FLOOR, cmf, wavelength_m, step_m)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    table = args.out_dir / "blackbody_cie_lut.csv"
    with table.open("w", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["log10_T", "r", "g", "b", "log10_Y"])
        for k in range(count):
            log10_t = LOG10_T_MIN + k * LOG10_T_STEP
            rgb, log10_y = row(log10_t, cmf, wavelength_m, step_m)
            if log10_t < LOG10_T_CHROMA_FLOOR:
                rgb = floor_rgb
            cells = [f"{log10_t:.2f}", *(f"{channel:.6f}" for channel in rgb), f"{log10_y:.6f}"]
            writer.writerow(cells)

    meta = {
        "table": table.name,
        "rows": count,
        "log10_T_min": LOG10_T_MIN,
        "log10_T_step": LOG10_T_STEP,
        "columns": {
            "r,g,b": "linear sRGB (D65) of B_lambda(T), unit Rec. 709 luminance, "
            "negatives clipped, held at log10 T = 2.9 below it",
            "log10_Y": "log10 photopic luminance 683 * int B_lambda ybar dlambda [cd/m^2]",
        },
        "cmf": "Wyman, Sloan & Shirley 2013 (JCGT 2(2)) multi-lobe fit to CIE 1931 2-degree",
        "wavelength_nm": [float(WAVELENGTH_NM[0]), float(WAVELENGTH_NM[-1]), 0.5],
        "generator": "scripts/generate_blackbody_cie_lut.py",
    }
    (args.out_dir / "blackbody_cie_meta.json").write_text(json.dumps(meta, indent=2) + "\n")


if __name__ == "__main__":
    main()
