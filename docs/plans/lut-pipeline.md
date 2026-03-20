# LUT Pipeline Plan (compact-common)

This plan formalizes the offline LUT workflow using compact-common as a
reference source (no code reuse).

## Inputs
- Mass (M_sun), spin (a*), mdot (Eddington fraction).
- Optional view angle grid for Doppler/redshift factors.

## Outputs (v1)
- `assets/luts/emissivity_lut.csv`
- `assets/luts/redshift_lut.csv`
- `assets/luts/lut_meta.json`

## Outputs (v2)
- `assets/luts/doppler_lut.csv` (angle/radius grid)
- `assets/luts/spin_radii_lut.csv` (spin vs ISCO/photon sphere)

## Outputs (v3 - GRB / spectra)
- `assets/luts/grb_spectral_table.h5` (ported grid from JetFit Table.h5 schema)
- `assets/luts/grb_afterglow_lut.csv` (time/frequency flux surface)
- `assets/luts/grb_modulation_lut.csv` (pulse envelopes from PyGRB-style models)

## Steps
1. Use compact-common formulas for ISCO/photon references.
2. Generate emissivity via Novikov-Thorne flux (normalize to max).
3. Generate redshift curve for equatorial plane.
4. Emit metadata with units + r_in/r_out over r_s.
5. Validate via `physics_test` and CSV curve diffs.
6. Import JetFit/boxfit tables offline and emit GRB spectral LUTs.
7. Normalize GRB LUTs to CGS units using grb-common conventions.
8. Add metadata for source model and reference citation.

## Scripts
- `scripts/generate_luts.py`: emissivity/redshift/spin curves (compact-common reference).
- `scripts/generate_grb_luts.py`: JetFit `Table.h5` -> `grb_spectral_table.h5`.

## compact-common touchpoints
- `compact_common.spacetime`: `isco_radius`, `photon_sphere_radius`, `kerr_isco`.
- `compact_common.constants`: `M_SUN`, `G`, `C`.
- Fallback: if compact-common is missing, use C++ formulas and set `compact_common_version=null`.

## GRB touchpoints (offline only)
- `grb-common` I/O schema (LightCurve, Spectrum) defines unit conventions.
- `JetFit` `Table.h5` grid used as a spectral LUT reference.
- `boxfit` HDF5 RHD box datasets define interpolation ranges (afterglowlibrary).
- `PyGRB` pulse envelopes define modulation curves (time-domain).

## File formats (current)
- CSV header: `u,value` where `u` is normalized [0..1] over r_in..r_out.
- lut_meta.json keys: `version`, `size`, `spin`, `mass_solar`, `mdot`, `prograde`,
  `r_in_over_rs`, `r_out_over_rs`, `r_in_cm`, `r_out_cm`, `isco_source`,
  `emissivity_model`, `redshift_model`, `compact_common_version`, `timestamp_utc`.
- spin_radii_lut header: `spin,r_isco_over_rs,r_ph_over_rs`.
  - Optional meta: `spin_curve_points`, `spin_curve_min`, `spin_curve_max`, `spin_curve_source`.

## Cleanroom Policy
- Use formulas and unit conventions only; no code reuse.
- LUTs are treated as data assets and validated against CPU helpers.
