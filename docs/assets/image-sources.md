# Background Image Sources and Licensing

This document tracks all background astronomical images used in the Blackhole visualization engine, their original sources, licensing terms, and proper attribution requirements.

## Source Archives

### NASA Image and Video Library
- **URL**: https://images.nasa.gov/
- **License**: NASA Images and Media Usage Guidelines
- **Terms**: https://www.nasa.gov/nasa-brand-center/images-and-media/
- **Usage**: Free to use for any purpose (educational, commercial, or personal)
- **Attribution**: Credit line required as specified per image
- **Format**: High-resolution JPEG, TIFF, or PNG originals

### ESA/Hubble Space Telescope
- **URL**: https://esahubble.org/images/
- **License**: Creative Commons Attribution 4.0 International (CC BY 4.0)
- **Terms**: https://esahubble.org/copyright/
- **Usage**: Free to share and adapt with proper attribution
- **Attribution**: Credit line must include all listed contributors
- **Format**: Original TIFF files available, JPEG publication quality

### STScI (Space Telescope Science Institute)
- **URL**: https://www.stsci.edu/gallery
- **License**: Varies per image, typically STScI Public Domain or CC BY
- **Attribution**: Required as specified per image
- **Format**: High-resolution FITS, TIFF, JPEG

### ESO (European Southern Observatory)
- **URL**: https://www.eso.org/public/images/
- **License**: Creative Commons Attribution 4.0 International (CC BY 4.0)
- **Terms**: https://www.eso.org/public/outreach/copyright/
- **Attribution**: "ESO" or more detailed credit as specified
- **Format**: Original TIFF, high-res JPEG

## Current Asset Inventory

### nasa_pia22085 - Black Hole With Jet (Artist's Concept)
- **Source**: NASA/JPL-Caltech
- **Original URL**: http://images-assets.nasa.gov/image/PIA22085/PIA22085~orig.jpg
- **Resolution**: 5120 × 2880 pixels
- **File Size**: ~1.3 MB (JPEG)
- **Credit Line**: NASA/JPL-Caltech

### nasa_pia15415 - Cygnus Loop Nebula
- **Source**: NASA/JPL-Caltech
- **Original URL**: http://images-assets.nasa.gov/image/PIA15415/PIA15415~orig.jpg
- **Resolution**: 6000 × 6000 pixels
- **File Size**: ~5.3 MB (JPEG)

### esa_heic1509a - Westerlund 2 Cluster
- **Source**: ESA/Hubble
- **Original URL**: https://cdn.esahubble.org/archives/images/publicationjpg/heic1509a.jpg
- **Resolution**: 4K: 4000 × 2997 (~3.4 MB), Large: 8919 × 6683 (~19 MB)
- **Credit**: NASA, ESA, the Hubble Heritage Team (STScI/AURA), A. Nota (ESA/STScI)

### esa_heic1402a - Horsehead Nebula
- **Source**: ESA/Hubble
- **Original URL**: https://cdn.esahubble.org/archives/images/publicationjpg/heic1402a.jpg
- **Resolution**: 4K: 4000 × 3596 (~15 MB), Large: 16617 × 14939 (~218 MB)
- **Credit**: NASA, ESA, E. Sabbi (STScI)

## Technical Specifications

### Current Format Pipeline
1. Source: Original JPEG files from NASA/ESA archives
2. Storage: assets/backgrounds/source/*.jpg
3. Loading: Direct stb_image JPEG decode to GPU as GL_SRGB/GL_SRGB_ALPHA
4. Mipmaps: Generated via glGenerateMipmap after upload

### Planned KTX2 Pipeline (Phase 3.1.3)
1. Source: Original high-resolution JPEGs
2. Compression: Basis Universal (basisu) encoder with ETC1S or UASTC codecs
3. Storage: assets/backgrounds/*.ktx2 (compressed, 4-8x smaller)
4. Loading: KTX2 loader with GPU-native transcoding (BC7/ASTC)
5. Benefits: Faster loading, reduced memory, embedded mipmaps

### Resolution Targets
- Minimum: 4K (3840 × 2160) for full-screen backgrounds
- Optimal: 8K (7680 × 4320) for parallax layers with zoom
- Ultra: 16K+ for archive-quality sources

## Attribution Requirements

All ESA/Hubble images require CC BY 4.0 attribution in application UI.
NASA images require credit line display (policy, not legal requirement).

