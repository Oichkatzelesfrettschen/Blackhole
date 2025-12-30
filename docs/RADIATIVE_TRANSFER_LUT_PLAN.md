# Radiative Transfer LUT Plan (tardis)

This plan defines offline LUT generation for spectral response curves
using TARDIS as the cleanroom reference source.

## Inputs
- Ejecta model parameters (density, temperature, composition).
- Wavelength/frequency bins for spectral curves.

## Key reference details (TARDIS)
- TARDISSpectrum stores frequency bin edges in Hz and luminosity per bin (erg/s).
- Derived curves: luminosity density in erg/s/Hz and erg/s/Angstrom.
- Flux conversion: `F = L / (4 * pi * d^2)` with distance in cm.
- ASCII export uses wavelength (Angstrom) vs L_lambda by default.

## Steps
1. Use TARDIS to generate spectral response curves.
2. Sample intensity vs wavelength and compress to LUTs.
3. Normalize intensity per chosen bandpass.
4. Emit LUTs + metadata (bin edges, units, source model).
5. Validate against CPU reference curves (CSV diffs).

## Stub generator (offline)
- `python3 scripts/generate_tardis_lut_stub.py --output-dir assets/luts`
- Produces `assets/luts/rt_spectrum_lut.csv` + `assets/luts/rt_spectrum_meta.json`.
- Replace mock spectra with real TARDIS output when available.

## Runtime Integration
- Load LUT textures in C++ and bind to shader.
- Use spectral weighting in disk emission or post-process.
- Provide a debug overlay to visualize LUT samples.
- `shader/blackhole_main.frag` samples `spectralLUT` with radius mapping as a placeholder hook.
