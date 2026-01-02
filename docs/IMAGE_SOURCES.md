# Image Sources and Licensing Notes

## Scope
- Track where background assets come from, the license/credit requirements,
  and any restrictions that affect distribution in this repo.
- Always preserve the credit line shown on the source page for each image.

## NASA (general)
- Source: https://www.nasa.gov/nasa-brand-center/images-and-media/
- NASA content is generally not subject to copyright in the United States
  for educational/informational use; credit NASA as the source.
- Watch for third-party copyrighted material explicitly marked on NASA pages.
- NASA insignia/logotypes are not public domain and are protected.

## JWST (NASA/ESA/CSA/STScI)
- Primary gallery: https://webbtelescope.org/resource-gallery/images
- Many JWST assets are credited "NASA, ESA, CSA, STScI" or similar.
- Follow NASA image guidance above and preserve the full credit line; if a
  third-party credit appears (artist, photographer), include it verbatim.

## ESA/Hubble
- Source: https://esahubble.org/copyright/
- ESA/Hubble images/videos are released under CC BY 4.0.
- Must show the full credit line clearly (example: "ESA/Hubble").
- No implication of ESA/Hubble endorsement; logos require permission.

## JAXA
- Site policy: https://global.jaxa.jp/policy.html
- Materials are copyrighted; non-commercial use for education/research is
  allowed under the stated conditions with required attribution.
- Commercial/business use requires prior permission from JAXA.
- No use of JAXA logos without explicit permission; third-party content is
  excluded from the default permissions.

## DESI
- Gallery: https://www.desi.lbl.gov/gallery/
- The site displays copyright notices; no explicit reuse license found in the
  gallery page. Treat as permission-required until verified.
- If we use DESI imagery, capture the credit line and confirm usage rights
  from the source page or DESI communications.

## Asset ingestion checklist
- Record: source URL, credit line, license/terms link, resolution, format.
- Verify: third-party credits, logo restrictions, and commercial-use limits.
- Store: metadata alongside the asset (for in-app credits and documentation).

---

# Asset Inventory

**Last Updated:** 2026-01-01

The canonical machine-readable source is `assets/backgrounds/manifest.json`.

## License Summary

| License | Count | Usage |
|---------|-------|-------|
| NASA Media Guidelines | 5 | Public domain equivalent for educational/scientific use |
| CC BY 4.0 | 4 | ESA/Hubble images, attribution required |
| JAXA Website Terms | 1 | Non-commercial use, credit required |
| Generated | 3+ | LUT data from physics formulas |

---

## Background Images

### NASA/JPL-Caltech

| Asset ID | Title | Resolution | Source URL |
|----------|-------|------------|------------|
| `nasa_pia22085` | Black Hole With Jet | 5120x2880 | [PIA22085](http://images-assets.nasa.gov/image/PIA22085/PIA22085~orig.jpg) |
| `nasa_pia15415` | Cygnus Loop Nebula | 6000x6000 | [PIA15415](http://images-assets.nasa.gov/image/PIA15415/PIA15415~orig.jpg) |
| `nasa_pia15416` | NASA/JPL PIA15416 | 9400x7000 | [PIA15416](http://images-assets.nasa.gov/image/PIA15416/PIA15416~orig.jpg) |
| `nasa_pia08506` | NASA/JPL Panorama | 14772x4953 | [PIA08506](http://images-assets.nasa.gov/image/PIA08506/PIA08506~orig.jpg) |

**Credit:** NASA/JPL-Caltech

### ESA/Hubble (CC BY 4.0)

| Asset ID | Title | Resolution | Source URL |
|----------|-------|------------|------------|
| `esa_heic1509a_4k` | Westerlund 2 | 4000x2997 | [heic1509a](https://cdn.esahubble.org/archives/images/publicationjpg/heic1509a.jpg) |
| `esa_heic1509a_large` | Westerlund 2 (large) | 8919x6683 | [large](https://cdn.esahubble.org/archives/images/large/heic1509a.jpg) |
| `esa_heic1402a_4k` | Horsehead Nebula | 4000x3596 | [heic1402a](https://cdn.esahubble.org/archives/images/publicationjpg/heic1402a.jpg) |
| `esa_heic1402a_large` | Horsehead Nebula (large) | 16617x14939 | [large](https://cdn.esahubble.org/archives/images/large/heic1402a.jpg) |

**Credits:**
- Westerlund 2: NASA, ESA, Hubble Heritage Team (STScI/AURA), A. Nota (ESA/STScI)
- Horsehead: NASA, ESA, E. Sabbi (STScI)

### JAXA

| Asset ID | Title | Resolution | Source URL |
|----------|-------|------------|------------|
| `jaxa_hayabusa2_main_001` | Hayabusa2 Mission | 480x320 | [JAXA](https://global.jaxa.jp/projects/sas/hayabusa2/) |

---

## Skybox Assets

### skybox_nebula_dark

Custom-processed skybox derived from ESA/Hubble imagery (2048x2048 per face).

| Face | File | Size |
|------|------|------|
| back | `back.png` | 2.7 MB |
| bottom | `bottom.png` | 4.0 MB |
| front | `front.png` | 3.4 MB |
| left | `left.png` | 3.3 MB |
| right | `right.png` | 3.7 MB |
| top | `top.png` | 1.4 MB |

**License:** Derived from CC BY 4.0 source

### skybox_test

Test UV checker skybox (debug). Project-generated.

---

## Generated LUT Data

| File | Purpose | Generator |
|------|---------|-----------|
| `luts/emissivity_lut.csv` | Novikov-Thorne disk | `generate_luts.py` |
| `luts/redshift_lut.csv` | Gravitational redshift | `generate_luts.py` |
| `luts/spin_radii_lut.csv` | ISCO/photon orbit vs spin | `generate_luts.py` |
| `luts/grb_modulation_lut.csv` | GRB modulation | `generate_grb_modulation_lut.py` |

**Source:** BPT 1972, Novikov-Thorne 1973 formulas

---

## Test Assets

| File | Purpose |
|------|---------|
| `color_map.png` | Color gradient test |
| `uv_checker.png` | UV coordinate checker |

---

## Adding New Assets

1. Download from authorized source
2. Add entry to `assets/backgrounds/manifest.json`
3. Update this document
4. Add hash to `assets/backgrounds/source/manifest.sha256`
5. Verify in application
