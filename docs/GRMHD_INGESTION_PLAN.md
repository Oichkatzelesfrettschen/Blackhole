# GRMHD Ingestion Plan (nubhlight)

This plan scopes offline ingestion of nubhlight HDF5 outputs into
compact textures for use in Blackhole. Runtime coupling is optional.

## Tooling
- `nubhlight_inspect` (`tools/nubhlight_inspect.cpp`) emits dataset/dimension metadata:
  `./build/build/Release/nubhlight_inspect -i dump_00000000.h5 -o logs/perf/nubhlight_meta.json`

## Reference Schema (nubhlight)
- HDF5 opacity/emissivity tables in `core/opac_emis_hdf.c`:
  - Datasets: `lrho`, `lT`, `Ye`, `lnu`, `emis`, `opac`.
  - Attributes: `numRho`, `numT`, `numYe`, `numNu`.
- Runtime outputs (see `core/xdmf_output.c`):
  - Grid file `grid.h5` with `XFcart`, `Lambda_h2cart_con`, `Lambda_h2cart_cov`,
    `gcon`, `gcov`, `gdet`, `alpha`, plus `Xharm` coordinate arrays.
  - Dump file `dump_########.h5` with primitives dataset `P` (shape `[N1,N2,N3,NVAR]`).
    - Primitive ordering from `core/decs.h`: `RHO, UU, U1, U2, U3, B1, B2, B3`,
      plus optional `KEL, KTOT` (if electrons enabled) and passive vars.
    - Header metadata (see `script/analysis/hdf5_to_dict.py`): `N1tot/N2tot/N3tot`,
      `metric`, `nvar`, `startx[i]`, `dx[i]`, unit fields, and `P.attrs['vnams']`
      (variable name list used to map channels).
  - Derived datasets (full dump): `divb`, `jcon`, `PRESS`, `ENT`, `TEMP`, `CS2`,
    `Qvisc`, `Qcoul`, `nph`, `Jrad`, `Rmunu`.
  - XDMF metadata emitted as `dump_########.xmf`.
- Output layout: `dumps/` + `restarts/` folders under the run output directory
  (set with `-o /path/to/output/`).

## Offline Conversion Pipeline
1. Detect dataset version + dimensions.
2. Convert to CGS and normalize to geometric units if needed.
3. Pack fields into 3D textures (density/temperature/velocity/B).
4. Emit metadata JSON (units, bounds, axes order, checksums).
5. Validate against a small reference dump (min/max + checksum).

## Runtime Loader (C++)
- Parse metadata JSON and enforce schema version.
- Load textures (3D) and set shader uniforms.
- Provide a debug overlay to visualize density/temperature slices.

## Metadata JSON (nubhlight_inspect)
```json
{
  "input": "dump_00000000.h5",
  "datasets": [
    { "path": "/dump/P", "dims": [256, 128, 128, 8], "vnams": ["RHO", "UU", "U1"] }
  ]
}
```

## Packed Texture Schema (proposal)
```json
{
  "schema_version": 1,
  "source": "nubhlight",
  "grid": { "dims": [256, 128, 128], "spacing": [1.0, 1.0, 1.0] },
  "textures": [
    {
      "path": "density_temp_vel_RGBA16F.bin",
      "format": "RGBA16F",
      "channels": ["rho", "temp", "u1", "u2"],
      "units": ["g/cm^3", "K", "c", "c"],
      "scale": [1.0, 1.0, 1.0, 1.0],
      "offset": [0.0, 0.0, 0.0, 0.0],
      "min": [0.0, 0.0, -1.0, -1.0],
      "max": [1.0, 1.0, 1.0, 1.0]
    }
  ]
}
```

## Validation
- Min/max sanity checks against source HDF5.
- Compare integrated profiles vs CPU reference curves.
- Optional histogram export for tuning LUT ranges.
