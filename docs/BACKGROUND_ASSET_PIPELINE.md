# Background Asset Pipeline

## Formats and targets
- Source-of-truth: keep the original JPEG/TIFF from the source site.
- Runtime targets:
  - 2K JPEG (fast load, low VRAM).
  - 4K JPEG (default).
  - 8K JPEG (screenshot/hi-res mode).
- Optional GPU-ready path: KTX2 (BasisU) once the KTX pipeline is wired.

## Compression guidance
- JPEG quality: 90+ for 4K/8K to preserve nebula gradients.
- Avoid heavy compression artifacts; prefer larger files to prevent banding.
- If a source provides TIFF, store it but do not ship it by default.

## Integration notes
- Initial implementation uses stb_image for JPEG/PNG loading (already in Conan).
- KTX2 becomes the preferred runtime asset once the toolchain is in place.
- OpenImageIO is optional if we need EXR/TIFF ingestion beyond JPEG/PNG.
- Always record source URL + credit line in `assets/backgrounds/manifest.json`.
- Per-layer LOD bias is adjustable in the Background panel; use it to keep distant layers on
  lower mip levels for large source images.

## Conan package inventory (optional)
- ktx/4.3.2: KTX/KTX2 container + BasisU transcoding.
- openimageio/3.1.8.0: EXR/TIFF/JPG/PNG ingest for offline conversion.
- tinyexr/1.0.7: lightweight EXR loader.
- libpng/1.6.53: PNG ingest.
- libjpeg-turbo/3.1.3: JPEG ingest.
- meshoptimizer/0.25: optional LOD/mesh compression tools.
- assimp/6.0.2: optional mesh import pipeline.
