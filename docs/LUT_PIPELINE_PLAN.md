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

## Steps
1. Use compact-common formulas for ISCO/photon references.
2. Generate emissivity via Novikov-Thorne flux (normalize to max).
3. Generate redshift curve for equatorial plane.
4. Emit metadata with units + r_in/r_out over r_s.
5. Validate via `physics_test` and CSV curve diffs.

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
