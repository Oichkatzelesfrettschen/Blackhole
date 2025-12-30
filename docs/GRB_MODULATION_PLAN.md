# GRB Modulation Plan

This plan scopes time-domain modulation LUTs for GRB/afterglow features.
All processing is offline; runtime uses sampled LUTs only.

## Reference Sources (cleanroom)
- grb-common: constants, cosmology, unit schemas.
- ASGARD_GRBAfterglow: afterglow spectra checklist.
- boxfit: HDF5 box data interpolation ranges.
- JetFit: `Table.h5` spectral functions (`f_peak`, `f_nu_c`, `f_nu_m` over tau/Eta0/GammaB/theta_obs).
- PyGRB: pulse models for prompt emission envelopes.

## Key reference details
- grb-common/io/schemas: LightCurve + Spectrum units (time s, flux erg/cm^2/s or erg/cm^2/s/Hz,
  frequency Hz, wavelength Angstroms, energy keV); supports observer vs source frame.
- JetFit FluxGeneratorClass: scale relations for F_peak, nu_c, nu_m using {z, dL, E, n, p, epse,
  epsb, xiN, Eta0, GammaB, theta_obs}; spectral branches follow Sari+1998 slow/fast cooling.
- PyGRB backend rate functions: Gaussian, FRED, and FREDx pulse shapes with parameters
  (start, scale, tau, xi, gamma, nu); use as envelope options for LUT generation.

## Steps
1. Define a `flux(t, nu)` LUT grid (time x frequency).
2. Use cosmology distance conversions (Planck18) for normalization.
3. Generate time-domain envelopes from PyGRB pulse models (Gaussian/FRED/FREDx).
4. Overlay afterglow spectral shapes from ASGARD/JetFit references (slow/fast cooling cases).
5. Emit LUTs + metadata (units, time frame, redshift).

## Runtime Integration
- Add modulation multiplier in shader (optional toggle).
- Provide C++ loader for LUT textures.
- Expose parameters in Controls/Performance UI.
