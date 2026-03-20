# Phase 3.1: Background Asset Download Guide

**Status:** In Progress (2026-01-15)
**Goal:** Acquire 4K/8K astronomical background imagery for black hole visualization
**Target:** 10-20 high-resolution backgrounds with proper licensing

---

## Overview

This guide documents procedures for downloading high-resolution astronomical imagery from authorized sources (NASA, ESA, ESO) for use as black hole visualization backgrounds in the Blackhole renderer.

**Key Requirements:**
- **Resolution**: 4K (3840×2160) minimum, 8K (7680×4320) preferred
- **Format**: FITS (raw scientific data) or TIFF/PNG (processed imagery)
- **License**: Public domain (NASA) or CC BY 4.0 (ESA/Hubble) or compatible
- **Content**: Deep sky objects (nebulae, galaxies, star fields, cosmic phenomena)

---

## Primary Data Sources

### 1. Hubble Legacy Archive (HLA) - STScI

**Access**: [https://hla.stsci.edu/](https://hla.stsci.edu/)

**Description**: The Hubble Legacy Archive provides enhanced Hubble products with advanced browsing capabilities. Contains observations through 2017-10-01.

**Resolution**: Native resolution varies; many exceed 8K (e.g., 34,372×19,345 pixels for deep space scans)

**Format Options**:
- **FITS**: Scientific data format (recommended for raw data)
- **TIFF**: High-quality processed images
- **JPEG**: Compressed preview

**Download Procedure**:
1. Navigate to [HLA main page](https://hla.stsci.edu/)
2. Use HLAView browser to search by:
   - Object name (e.g., "Carina Nebula", "M87")
   - Coordinates (RA/Dec)
   - Proposal ID
3. Click on thumbnails to view full-resolution options
4. Select "Download" → Choose format (TIFF or FITS)
5. Record metadata: URL, credit line, resolution

**License**: NASA content generally public domain for educational/scientific use
**Credit Required**: "NASA, ESA, STScI" or specific credit line from image page

**Recommended Targets**:
- Deep field surveys (HUDF, XDF, GOODS)
- Nebulae (Carina, Orion, Horsehead, Eagle)
- Galaxies (M87, Whirlpool, Sombrero, Andromeda)
- Globular clusters (Omega Centauri, 47 Tucanae)

---

### 2. MAST Archive (Mikulski Archive for Space Telescopes)

**Access**: [https://archive.stsci.edu/missions-and-data/hst](https://archive.stsci.edu/missions-and-data/hst)

**Description**: For HST data after 2017-10-01. Provides Hubble Advanced Products (HAP) with HLA-style processing.

**Portal**: [MAST Portal](https://mast.stsci.edu/portal/Mashup/Clients/Mast/Portal.html)

**Format Options**:
- **FITS**: Multi-extension FITS with calibrated data
- **DRIZZLED**: Enhanced resolution via drizzle algorithm
- **HAP Products**: Mosaicked, background-subtracted

**Download Procedure**:
1. Go to MAST Portal
2. Select "HST" mission
3. Search by target name or coordinates
4. Filter by:
   - Instrument (ACS, WFC3, WFPC2)
   - Filter (visible, UV, IR)
   - Exposure time (longer = deeper)
5. Add to cart → Download

**License**: NASA Media Guidelines (public domain equivalent)
**Credit Required**: "NASA, ESA, STScI" + specific team/PI credits

---

### 3. ESA/Hubble Image Gallery

**Access**: [https://esahubble.org/images/](https://esahubble.org/images/)

**Description**: ESA's curated collection of Hubble imagery, optimized for public outreach.

**Resolution**: Up to 16,617×14,939 pixels (Horsehead Nebula example)

**Format Options**:
- **Original TIFF**: Highest quality (uncompressed or LZW)
- **Publication JPEG**: 4K resolution for web use
- **Large JPEG**: 8K+ for print/display

**Download Procedure**:
1. Navigate to [ESA/Hubble Images](https://esahubble.org/images/)
2. Browse by:
   - Top 100 images
   - Category (Nebulae, Galaxies, Stars)
   - Search term
3. Click on image thumbnail
4. Scroll to "Download" section
5. Select format:
   - "Original" → TIFF (largest file size, no compression)
   - "Large" → High-res JPEG (8K+)
   - "Publication" → 4K JPEG
6. Right-click → "Save As"

**License**: **CC BY 4.0** (Creative Commons Attribution 4.0)
**Credit Required**: Full credit line (e.g., "NASA, ESA, Hubble Heritage Team (STScI/AURA)")

**Top Targets** (confirmed 8K+ available):
- `heic1402a` - Horsehead Nebula: 16,617×14,939 pixels
- `heic1509a` - Westerlund 2: 8,919×6,683 pixels
- `heic1608a` - Hubble Deep Field: 12,000×12,000 pixels
- `heic1107a` - Carina Nebula: 18,000×18,000 pixels (mosaic)

---

### 4. ESO Science Archive Facility

**Access**: [http://archive.eso.org/](http://archive.eso.org/)

**Description**: European Southern Observatory archive with ground-based telescope data (VLT, VISTA, VST).

**Data Volume**: 65+ TB (1.5 million images/spectra)

**Resolution**: Varies; VISTA survey mosaics can exceed 8K

**Format**: **FITS** (standard astronomical data format)

**Download Procedure**:
1. Go to [ESO Archive Portal](http://archive.eso.org/)
2. Select interface:
   - **Query Form**: Search by coordinates, date, instrument
   - **Archive Science Portal**: Browse by science category
3. Filter by:
   - Instrument (MUSE, FORS2, VIMOS, HAWK-I)
   - Program ID (public surveys)
   - Target name
4. Select datasets → Add to cart
5. Download (requires free ESO account for bulk downloads)

**License**: ESO data policy - public after 1-year proprietary period
**Credit Required**: "ESO" + program ID + PI name

**Recommended Surveys**:
- **VISTA VVV**: Milky Way bulge/disk survey
- **VISTA VMC**: Magellanic Clouds survey (released 2025-12)
- **VST ATLAS**: Southern sky survey
- **MUSE Deep Fields**: 3D spectroscopic cubes

**Processing Note**: FITS files from ESO require calibration/reduction. Use:
- **Astropy** (Python) for FITS I/O
- **ESO Reflex** for automated reduction pipelines
- **GIMP** with Astro plugin for image conversion

---

### 5. James Webb Space Telescope (JWST)

**Access**: [https://webbtelescope.org/resource-gallery/images](https://webbtelescope.org/resource-gallery/images)

**Description**: Latest infrared imagery from JWST (launched 2021).

**Resolution**: Up to 14,575×8,441 pixels (JWST First Deep Field)

**Format Options**:
- **TIFF**: Uncompressed or LZW
- **PNG**: Alpha channel support
- **JPEG**: Compressed preview

**Download Procedure**:
1. Visit [JWST Image Gallery](https://webbtelescope.org/resource-gallery/images)
2. Browse by:
   - Latest releases
   - Science categories (galaxies, nebulae, etc.)
   - Instrument (NIRCam, MIRI, NIRSpec)
3. Click image → "Download" button
4. Select resolution (multiple sizes available)

**License**: NASA Media Guidelines (public domain equivalent)
**Credit Required**: "NASA, ESA, CSA, STScI" + science team credits

**Top Targets**:
- **SMACS 0723**: First Deep Field (14K resolution)
- **Carina Nebula**: Cosmic Cliffs (14K)
- **Southern Ring Nebula**: 12K resolution
- **Stephan's Quintet**: 12K mosaic

---

### 6. NASA Scientific Visualization Studio (SVS)

**Access**: [https://svs.gsfc.nasa.gov/](https://svs.gsfc.nasa.gov/)

**Description**: High-resolution visualizations prepared for NASA hyperwall displays.

**Resolution**: 4K (3840×2160) standard, some 8K (7680×4320)

**Format**: TIFF, PNG, JPEG

**Download Procedure**:
1. Search by keyword or browse categories
2. Click visualization → "Download" section
3. Select resolution (4K Hyperwall, 8K Hyperwall)
4. Multiple frame sequences available for animations

**License**: NASA Media Guidelines
**Credit**: "NASA's Scientific Visualization Studio"

---

## Asset Selection Criteria

### Priority 1: Star Fields & Nebulae
- **Use Case**: Black hole distant background
- **Targets**: Carina Nebula, Orion Nebula, Tarantula Nebula, Lagoon Nebula
- **Resolution Needed**: 8K+ for parallax layers
- **Color**: Rich RGB data (visible spectrum)

### Priority 2: Galaxies
- **Use Case**: Black hole environment context
- **Targets**: M87 (host of supermassive BH), Andromeda, Whirlpool, Sombrero
- **Resolution Needed**: 4K minimum (used at distance)
- **Features**: Well-defined spiral arms, jets, active galactic nuclei

### Priority 3: Deep Fields
- **Use Case**: Ultimate depth/distance backgrounds
- **Targets**: Hubble Ultra Deep Field, eXtreme Deep Field, JWST First Deep Field
- **Resolution Needed**: 8K+ (contains thousands of galaxies)
- **Special**: Shows cosmic evolution, distant universe

### Priority 4: Globular Clusters
- **Use Case**: Dense star fields
- **Targets**: Omega Centauri, 47 Tucanae, M13
- **Resolution Needed**: 4K+
- **Features**: Thousands of stars resolved

---

## Format Conversion Pipeline

### FITS → TIFF/PNG Conversion

**Tools**:
- **Astropy** (Python): `astropy.io.fits`
- **GIMP**: Astro-compatible fork or native FITS support
- **ImageMagick**: `convert` with FITS delegate
- **DS9/SAOImage**: Interactive viewer with export

**Procedure** (Astropy example):
```python
from astropy.io import fits
from astropy.visualization import astropy_mpl_style, ZScaleInterval, ImageNormalize
import matplotlib.pyplot as plt
import numpy as np

# Read FITS
hdul = fits.open('image.fits')
data = hdul[0].data

# Normalize (99.5th percentile clipping)
norm = ImageNormalize(data, interval=ZScaleInterval())

# Save as PNG (16-bit)
plt.imsave('output.png', data, cmap='gray', norm=norm, format='png', dpi=300)
```

**Color Composites** (R/G/B from multiple filters):
```python
# Load separate filter FITS files
r_data = fits.getdata('filter_r.fits')
g_data = fits.getdata('filter_g.fits')
b_data = fits.getdata('filter_b.fits')

# Normalize each channel
r_norm = ImageNormalize(r_data, interval=ZScaleInterval())
g_norm = ImageNormalize(g_data, interval=ZScaleInterval())
b_norm = ImageNormalize(b_data, interval=ZScaleInterval())

# Stack to RGB
rgb = np.dstack([r_norm(r_data), g_norm(g_data), b_norm(b_data)])

# Save as TIFF (16-bit per channel)
from PIL import Image
img = Image.fromarray((rgb * 65535).astype(np.uint16), mode='RGB')
img.save('output.tiff', compression='lzw')
```

---

## KTX2 Conversion (Phase 3.1.3)

**Goal**: Convert TIFF/PNG to KTX2 for GPU-optimized texture streaming.

**KTX2 Advantages**:
- Basis Universal supercompression (ETC1S or UASTC)
- Mipmap generation built-in
- Direct GPU upload (no CPU-side decompression)
- 50-80% smaller than PNG

**Tools**:
- **toktx**: Official Khronos KTX tool ([GitHub](https://github.com/KhronosGroup/KTX-Software))
- **Compressonator**: AMD texture compression GUI
- **basisu**: Basis Universal encoder

**Command** (toktx):
```bash
# Linear color space (most astronomy data)
toktx --bcmp --genmipmap --clevel 4 output.ktx2 input.tiff

# sRGB color space (processed imagery)
toktx --bcmp --genmipmap --clevel 4 --srgb output.ktx2 input.png

# UASTC (higher quality, larger)
toktx --uastc 2 --genmipmap output.ktx2 input.tiff
```

**Integration**:
- Load with `ktxTexture2` API (libktx)
- Upload to GL_TEXTURE_2D with `ktxTexture_GLUpload()`
- Enable anisotropic filtering for distant views

---

## Parallax Layer System Design (Phase 3.1.4)

**Concept**: Multiple background layers at different "depths" with parallax scrolling.

### Layer Stack (Far to Near):

| Layer | Content | Resolution | Parallax Factor | Distance Hint |
|-------|---------|------------|-----------------|---------------|
| **Layer 0** | Deep field (HUDF/XDF) | 8K | 0.01 | Billions of light-years |
| **Layer 1** | Distant galaxies | 4K | 0.05 | Hundreds of millions of ly |
| **Layer 2** | Local galaxy (M87, Andromeda) | 4K | 0.1 | Millions of ly |
| **Layer 3** | Nebula (Carina, Orion) | 8K | 0.3 | Thousands of ly |
| **Layer 4** | Star field (dense) | 4K | 0.5 | Hundreds of ly |
| **Layer 5** | Foreground stars (bright) | 2K | 1.0 | Tens of ly |

**Parallax Calculation**:
```glsl
vec2 parallaxOffset = cameraDirection.xy * parallaxFactor * depth;
vec2 uv = baseUV + parallaxOffset;
vec4 layerColor = texture(backgroundLayer, uv);
```

**Blending**:
- Additive blending for stars (HDR accumulation)
- Alpha blending for nebulae (soft edges)
- Depth-based fog for atmospheric perspective

**LOD Strategy**:
- Use mipmaps for distant layers (automatic with KTX2)
- Switch to lower-res textures when layer contribution < 5%

---

## HDR Pipeline Evaluation (Phase 3.1.5)

**Current**: 8-bit sRGB PNGs/JPEGs
**Target**: 16-bit linear TIFF or EXR for HDR workflow

### HDR Formats

| Format | Bit Depth | Color Space | Use Case |
|--------|-----------|-------------|----------|
| **TIFF** | 16-bit int | Linear | Astronomy data, easy to work with |
| **EXR** | 16-bit float | Linear | HDR compositing, wide dynamic range |
| **FITS** | 32-bit float | Linear | Raw scientific data |

**Libraries**:
- **OpenImageIO**: Universal image I/O (all formats)
- **tinyexr**: Lightweight EXR reader/writer
- **stb_image**: 8-bit/16-bit PNG/TIFF (already in use)

**HDR Workflow**:
1. Source: FITS (32-bit float) or TIFF (16-bit)
2. Tonemap for preview: Reinhard or ACES
3. Store in linear color space (no gamma correction)
4. Apply bloom/glow in HDR buffer (RGBA16F)
5. Tonemap to display in final pass

**Recommendation**: Use **tinyexr** for maximum dynamic range preservation.

---

## Download Checklist (Per Asset)

- [ ] **Source Identified**: URL recorded in IMAGE_SOURCES.md
- [ ] **License Verified**: Public domain, CC BY 4.0, or compatible
- [ ] **Credit Line Captured**: Full attribution string
- [ ] **Resolution Confirmed**: 4K minimum, 8K preferred
- [ ] **Format Selected**: TIFF (preferred) or FITS (if raw data)
- [ ] **Downloaded**: File saved to `assets/backgrounds/source/`
- [ ] **Converted** (if needed): FITS→TIFF, PNG→TIFF
- [ ] **Metadata Added**: Entry in `manifest.json`
- [ ] **Hash Computed**: SHA-256 added to `manifest.sha256`
- [ ] **Tested**: Loaded in application, visually verified
- [ ] **KTX2 Converted** (future): Compressed texture ready for GPU

---

## Asset Storage Structure

```
assets/
├── backgrounds/
│   ├── source/              # Original high-res downloads
│   │   ├── fits/            # Raw FITS files
│   │   ├── tiff/            # Converted TIFF (16-bit)
│   │   └── png/             # Processed PNG (8-bit preview)
│   ├── ktx2/                # KTX2 compressed textures (Phase 3.1.3)
│   ├── manifest.json        # Asset metadata (machine-readable)
│   └── manifest.sha256      # Integrity hashes
└── luts/                    # Generated lookup tables (existing)
```

**manifest.json Schema**:
```json
{
  "assets": [
    {
      "id": "esa_heic1402a_large",
      "title": "Horsehead Nebula",
      "source_url": "https://cdn.esahubble.org/archives/images/large/heic1402a.jpg",
      "license": "CC BY 4.0",
      "credit": "NASA, ESA, E. Sabbi (STScI)",
      "resolution": {"width": 16617, "height": 14939},
      "format": "TIFF",
      "file_path": "source/tiff/heic1402a_large.tiff",
      "sha256": "abc123...",
      "category": "nebula",
      "parallax_layer": 3,
      "parallax_factor": 0.3
    }
  ]
}
```

---

## Implementation Plan

### Week 1: Initial Downloads (Phase 3.1.2)
- [ ] Download 5 ESA/Hubble images (8K nebulae/galaxies)
- [ ] Download 3 JWST images (infrared deep fields)
- [ ] Download 2 HLA mosaics (star fields)
- [ ] Update IMAGE_SOURCES.md with full metadata

### Week 2: Format Conversion
- [ ] Convert all FITS to 16-bit TIFF (Astropy pipeline)
- [ ] Generate color composites for multi-filter data
- [ ] Create 4K preview PNGs for UI selection

### Week 3: KTX2 Pipeline (Phase 3.1.3)
- [ ] Install toktx/basisu tools
- [ ] Benchmark ETC1S vs UASTC compression
- [ ] Batch convert all assets to KTX2
- [ ] Integrate libktx into CMake build

### Week 4: Parallax System (Phase 3.1.4)
- [ ] Design shader architecture (multi-layer sampling)
- [ ] Implement parallax offset calculation
- [ ] Add UI controls (layer visibility, depth tuning)
- [ ] Performance test (6 layers @ 8K)

---

## Performance Targets

| Metric | Target | Notes |
|--------|--------|-------|
| **Texture Memory** | < 2 GB | 6 layers × KTX2 compression |
| **Load Time** | < 5 seconds | Async loading with mipmaps |
| **Frame Time** | < 2 ms | Parallax + sampling overhead |
| **VRAM Bandwidth** | < 10 GB/s | Mipmaps + anisotropic filtering |

---

## References

### Official Documentation
- **HLA User Guide**: [https://hla.stsci.edu/hla_help.html](https://hla.stsci.edu/hla_help.html)
- **MAST Portal Docs**: [https://mast.stsci.edu/portal/Mashup/Clients/Mast/PortalDocumentation.html](https://mast.stsci.edu/portal/Mashup/Clients/Mast/PortalDocumentation.html)
- **ESA/Hubble Copyright**: [https://esahubble.org/copyright/](https://esahubble.org/copyright/)
- **ESO Archive Manual**: [http://archive.eso.org/cms/tools-documentation/archive-science-portal-help.html](http://archive.eso.org/cms/tools-documentation/archive-science-portal-help.html)
- **NASA Media Guidelines**: [https://www.nasa.gov/nasa-brand-center/images-and-media/](https://www.nasa.gov/nasa-brand-center/images-and-media/)

### Tools & Libraries
- **Astropy**: [https://www.astropy.org/](https://www.astropy.org/)
- **KTX-Software**: [https://github.com/KhronosGroup/KTX-Software](https://github.com/KhronosGroup/KTX-Software)
- **Basis Universal**: [https://github.com/BinomialLLC/basis_universal](https://github.com/BinomialLLC/basis_universal)
- **tinyexr**: [https://github.com/syoyo/tinyexr](https://github.com/syoyo/tinyexr)
- **OpenImageIO**: [https://github.com/OpenImageIO/oiio](https://github.com/OpenImageIO/oiio)

### Scientific Background
- **Hubble Deep Fields**: [https://archive.stsci.edu/prepds/hlf/](https://archive.stsci.edu/prepds/hlf/)
- **JWST ERS Programs**: [https://www.stsci.edu/jwst/science-execution/approved-programs/dd-ers](https://www.stsci.edu/jwst/science-execution/approved-programs/dd-ers)
- **ESO Public Surveys**: [http://eso.org/sci/observing/PublicSurveys.html](http://eso.org/sci/observing/PublicSurveys.html)

---

**Last Updated**: 2026-01-15
**Status**: Guide complete, ready for implementation
**Next**: Begin Week 1 downloads (Phase 3.1.2)

Sources:
- [Hubble Legacy Archive](https://hla.stsci.edu/)
- [MAST Archive - HST](https://archive.stsci.edu/missions-and-data/hst)
- [ESA/Hubble Images](https://esahubble.org/images/)
- [ESO Science Archive](http://archive.eso.org/)
- [JWST Image Gallery](https://webbtelescope.org/resource-gallery/images)
- [NASA SVS](https://svs.gsfc.nasa.gov/)
