# GRMHD Ingestion Plan (nubhlight)

This plan scopes offline ingestion of nubhlight HDF5 outputs into
compact textures for use in Blackhole. Runtime coupling is optional.

## Tooling
- `nubhlight_inspect` (`tools/nubhlight_inspect.cpp`) emits dataset/dimension metadata:
  `./build/build/Release/nubhlight_inspect -i dump_00000000.h5 -o logs/perf/nubhlight_meta.json`
- `nubhlight_pack` (`tools/nubhlight_pack.cpp`) packs selected channels into RGBA blobs:
  `./build/build/Release/nubhlight_pack -i dump_00000000.h5 -d /dump/P --fields RHO,UU,U1,U2 -o logs/perf/nubhlight_pack.json`

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
- `src/grmhd_packed_loader.*` loads RGBA32F blobs + metadata into 3D textures.
- `shader/blackhole_main.frag` samples `grmhdTexture` when `useGrmhd` is enabled.
- `shader/grmhd_slice.frag` renders slice previews for ImGui inspection.

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

## Packed Texture Metadata (nubhlight_pack)
```json
{
  "schema_version": 1,
  "source": "nubhlight",
  "input": "dump_00000000.h5",
  "dataset": "/dump/P",
  "layout": "channels-last",
  "format": "RGBA32F",
  "bin": "logs/perf/nubhlight_pack.bin",
  "checksum_fnv1a64": "c83f57a8d1e22ef0",
  "dataset_dims": [256, 128, 128, 8],
  "grid_dims": [256, 128, 128],
  "channel_dim_index": 3,
  "channels": ["RHO", "UU", "U1", "U2"],
  "source_indices": [0, 1, 2, 3],
  "fill": [0.0, 0.0, 0.0, 1.0],
  "min": [0.0, 0.0, -1.0, -1.0],
  "max": [1.0, 1.0, 1.0, 1.0],
  "vnams": ["RHO", "UU", "U1", "U2", "U3", "B1", "B2", "B3"]
}
```

## Validation
- Min/max sanity checks against source HDF5.
- Compare integrated profiles vs CPU reference curves.
- Optional histogram export for tuning LUT ranges.
- Packed blob checksum (FNV-1a 64-bit) validation in loader.
- CTest fixture: `grmhd_pack_fixture` generates a tiny HDF5 dump and validates pack/loader.
