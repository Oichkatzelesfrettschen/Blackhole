/**
 * @file fits_writer.h
 * @brief FITS image output for scientifically actionable data products.
 *
 * Writes 2D float images with proper WCS (World Coordinate System) headers
 * so that downstream tools (ds9, eht-imaging, CASA) can interpret the output
 * as sky-plane images with correct angular coordinates.
 *
 * WHY: Without FITS output, no downstream astronomer or EHT comparison pipeline
 * can consume the rendered images. This is the single highest-ROI infrastructure
 * item for scientific relevance.
 *
 * WHAT: Thin wrapper around cfitsio that writes:
 *   - 2D FITS images (float32 or float64)
 *   - WCS keywords (CRPIX, CRVAL, CDELT, CTYPE, CUNIT)
 *   - Source metadata (M, a*, D, inclination)
 *   - Reproducibility keywords (git hash, build info)
 *   - Optional Stokes extensions (for future polarized RT)
 *
 * HOW: Link against system cfitsio (pkg-config). Call writeFitsImage() with
 * pixel data, image dimensions, and a FitsHeader struct describing the source.
 *
 * References:
 *   - FITS Standard v4.0 (IAU)
 *   - EHT Collaboration Data Products (ehtim format)
 *   - cfitsio User's Reference Guide (Pence 2010)
 */

#ifndef PHYSICS_FITS_WRITER_H
#define PHYSICS_FITS_WRITER_H

#include "constants.h"
#include <cstring>
// NOLINTBEGIN(misc-include-cleaner)
// WHY: cfitsio declares its C API symbols (fits_*) across internal sub-headers
// (fitsio2.h, longnam.h) that are transitively included by <fitsio.h>.
// clang-tidy cannot resolve the canonical include for each symbol and falsely
// reports missing direct includes. <fitsio.h> is the correct public header
// per the cfitsio API contract.
#include <fitsio.h>
// NOLINTEND(misc-include-cleaner)
#include <stdexcept>
#include <string>
#include <vector>

namespace physics {

// ============================================================================
// FITS Header Metadata
// ============================================================================

/**
 * @brief World Coordinate System parameters for sky-plane images.
 *
 * Standard WCS for EHT-style images: gnomonic (TAN) projection centered
 * on the source, with angular offsets in microarcseconds.
 */
struct WCSParams {
  double crpix1 = 0.0;  // Reference pixel X (1-indexed; 0 = auto-center)
  double crpix2 = 0.0;  // Reference pixel Y (1-indexed; 0 = auto-center)
  double crval1 = 0.0;  // Reference RA [deg]
  double crval2 = 0.0;  // Reference Dec [deg]
  double cdelt1 = 0.0;  // Pixel scale X [deg/pixel] (negative = East-left)
  double cdelt2 = 0.0;  // Pixel scale Y [deg/pixel]
};

/**
 * @brief Source and observation metadata for FITS header.
 */
struct FitsSourceInfo {
  std::string object;            // Source name (e.g., "M87*", "Sgr A*")
  double massMsun = 0.0;        // Black hole mass [solar masses]
  double spin = 0.0;            // Dimensionless spin a* [0, 1)
  double distanceCm = 0.0;      // Distance to source [cm]
  double inclinationDeg = 0.0;  // Observer inclination [degrees]
  double freqHz = 0.0;          // Observing frequency [Hz]
  double fovUas = 0.0;          // Field of view [microarcseconds]
};

/**
 * @brief Reproducibility metadata.
 */
struct FitsProvenance {
  std::string codeName = "Blackhole";
  std::string codeVersion;
  std::string gitHash;
  std::string compiler;
  std::string buildType;
};

/**
 * @brief Complete FITS header configuration.
 */
struct FitsHeader {
  WCSParams wcs;
  FitsSourceInfo source;
  FitsProvenance provenance;
};

// ============================================================================
// FITS Error Handling
// ============================================================================

/**
 * @brief Exception for FITS I/O errors.
 */
class FitsError : public std::runtime_error {
public:
  explicit FitsError(const std::string& msg, int cfitsioStatus = 0)
      : std::runtime_error(formatMessage(msg, cfitsioStatus)),
        status_(cfitsioStatus) {}

  [[nodiscard]] int cfitsioStatus() const noexcept { return status_; }

private:
  int status_;

  static std::string formatMessage(const std::string& msg, int status) {
    if (status == 0) { return msg; }
    char errmsg[FLEN_ERRMSG];
    fits_get_errstatus(status, errmsg);  // NOLINT(misc-include-cleaner)
    return msg + ": " + std::string(errmsg) + " (status=" + std::to_string(status) + ")";
  }
};

// ============================================================================
// Internal Helpers
// ============================================================================

namespace detail {

/// RAII wrapper for fitsfile* that closes on destruction.
class FitsFileGuard {
public:
  explicit FitsFileGuard(fitsfile* fp) : fp_(fp) {}
  ~FitsFileGuard() {
    if (fp_ != nullptr) {
      int status = 0;
      fits_close_file(fp_, &status);  // NOLINT(misc-include-cleaner)
    }
  }
  FitsFileGuard(const FitsFileGuard&) = delete;
  FitsFileGuard& operator=(const FitsFileGuard&) = delete;
  FitsFileGuard(FitsFileGuard&& o) noexcept : fp_(o.fp_) { o.fp_ = nullptr; }
  FitsFileGuard& operator=(FitsFileGuard&&) = delete;

  fitsfile* get() noexcept { return fp_; }

private:
  fitsfile* fp_;
};

/// Write a string keyword, truncating to FITS 68-char limit.
inline void writeKeyStr(fitsfile* fp, const char* key, const std::string& val,
                        const char* comment = nullptr) {
  int status = 0;
  fits_update_key_str(fp, key, val.c_str(), comment, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write a double keyword.
inline void writeKeyDbl(fitsfile* fp, const char* key, double val,
                        int decimals = 15, const char* comment = nullptr) {
  int status = 0;
  fits_update_key_dbl(fp, key, val, decimals, comment, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write a long keyword.
inline void writeKeyLng(fitsfile* fp, const char* key, long val,
                        const char* comment = nullptr) {
  int status = 0;
  fits_update_key_lng(fp, key, val, comment, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write WCS keywords for a 2D sky-plane image.
inline void writeWcs(fitsfile* fp, const WCSParams& wcs, int nx, int ny) {
  const double crpix1 = (wcs.crpix1 > 0.0) ? wcs.crpix1 : (static_cast<double>(nx) + 1.0) / 2.0;
  const double crpix2 = (wcs.crpix2 > 0.0) ? wcs.crpix2 : (static_cast<double>(ny) + 1.0) / 2.0;

  writeKeyStr(fp, "CTYPE1", "RA---TAN", "Coordinate type axis 1");
  writeKeyStr(fp, "CTYPE2", "DEC--TAN", "Coordinate type axis 2");
  writeKeyDbl(fp, "CRPIX1", crpix1, 6, "Reference pixel axis 1");
  writeKeyDbl(fp, "CRPIX2", crpix2, 6, "Reference pixel axis 2");
  writeKeyDbl(fp, "CRVAL1", wcs.crval1, 12, "[deg] Reference RA");
  writeKeyDbl(fp, "CRVAL2", wcs.crval2, 12, "[deg] Reference Dec");

  if (wcs.cdelt1 != 0.0) {
    writeKeyDbl(fp, "CDELT1", wcs.cdelt1, 15, "[deg] Pixel scale axis 1");
    writeKeyDbl(fp, "CDELT2", wcs.cdelt2, 15, "[deg] Pixel scale axis 2");
  }

  writeKeyStr(fp, "CUNIT1", "deg", "Units of axis 1");
  writeKeyStr(fp, "CUNIT2", "deg", "Units of axis 2");
  writeKeyStr(fp, "RADESYS", "ICRS", "Reference frame");
}

/// Write source metadata keywords.
inline void writeSourceInfo(fitsfile* fp, const FitsSourceInfo& src) {
  if (!src.object.empty()) {
    writeKeyStr(fp, "OBJECT", src.object, "Source name");
  }
  if (src.massMsun > 0.0) {
    writeKeyDbl(fp, "BH_MASS", src.massMsun, 6, "[Msun] Black hole mass");
  }
  if (src.spin != 0.0 || src.massMsun > 0.0) {
    writeKeyDbl(fp, "BH_SPIN", src.spin, 6, "Dimensionless spin a*");
  }
  if (src.distanceCm > 0.0) {
    const double distMpc = src.distanceCm / MPC;
    writeKeyDbl(fp, "BH_DIST", distMpc, 6, "[Mpc] Distance");
  }
  if (src.inclinationDeg != 0.0) {
    writeKeyDbl(fp, "BH_INCL", src.inclinationDeg, 4, "[deg] Inclination");
  }
  if (src.freqHz > 0.0) {
    writeKeyDbl(fp, "FREQ", src.freqHz, 6, "[Hz] Observing frequency");
  }
  if (src.fovUas > 0.0) {
    writeKeyDbl(fp, "FOV_UAS", src.fovUas, 4, "[uas] Field of view");
  }
}

/// Write provenance keywords.
inline void writeProvenance(fitsfile* fp, const FitsProvenance& prov) {
  writeKeyStr(fp, "ORIGIN", prov.codeName, "Software that created this file");
  if (!prov.codeVersion.empty()) {
    writeKeyStr(fp, "VERSION", prov.codeVersion, "Code version");
  }
  if (!prov.gitHash.empty()) {
    writeKeyStr(fp, "GITHASH", prov.gitHash, "Git commit hash");
  }
  if (!prov.compiler.empty()) {
    writeKeyStr(fp, "COMPILER", prov.compiler, "Compiler used");
  }
  if (!prov.buildType.empty()) {
    writeKeyStr(fp, "BLDTYPE", prov.buildType, "Build type");
  }
}

} // namespace detail

// ============================================================================
// Public API
// ============================================================================

/**
 * @brief Compute WCS pixel scale from source parameters.
 *
 * Given a field of view in microarcseconds and image size in pixels,
 * compute the CDELT values (degrees per pixel) for the FITS header.
 *
 * @param fovUas Field of view [microarcseconds]
 * @param nx Number of pixels in X
 * @param ny Number of pixels in Y
 * @return WCSParams with computed pixel scale (East-left convention)
 */
[[nodiscard]] inline WCSParams wcsFromFov(double fovUas, int nx, int ny) {
  WCSParams wcs;
  // Convert uas to degrees: 1 uas = 1e-6 arcsec = 1e-6/3600 deg
  const double fovDeg = fovUas * 1.0e-6 / 3600.0;
  wcs.cdelt1 = -fovDeg / static_cast<double>(nx); // Negative = East-left (RA convention)
  wcs.cdelt2 = fovDeg / static_cast<double>(ny);
  return wcs;
}

/**
 * @brief Compute field of view in microarcseconds from source parameters.
 *
 * FOV = 2 * nRg * r_g / D [radians], converted to microarcseconds.
 *
 * @param massMsun Black hole mass [solar masses]
 * @param distanceCm Distance to source [cm]
 * @param nRg Number of gravitational radii across half the FOV
 * @return Field of view [microarcseconds]
 */
[[nodiscard]] inline double fovFromSource(double massMsun, double distanceCm,
                                          double nRg = 20.0) {
  const double rG = G * massMsun * M_SUN / (C * C); // Gravitational radius [cm]
  const double fovRad = 2.0 * nRg * rG / distanceCm;
  // Convert radians to microarcseconds: 1 rad = 206265 arcsec = 206265e6 uas
  return fovRad * 206265.0e6;
}

/**
 * @brief Write a 2D float image to a FITS file.
 *
 * Creates a new FITS file (overwrites if exists) with a single IMAGE HDU
 * containing the pixel data and WCS/source/provenance metadata.
 *
 * Pixel data is in row-major order: data[y * nx + x], with y=0 at the
 * bottom of the image (FITS convention).
 *
 * @param filename Output filename (with .fits extension)
 * @param data Pixel values (nx * ny floats, row-major)
 * @param nx Image width [pixels]
 * @param ny Image height [pixels]
 * @param header FITS header metadata
 * @throws FitsError on cfitsio failure
 */
inline void writeFitsImage(const std::string& filename,
                           const float* data, int nx, int ny,
                           const FitsHeader& header = FitsHeader{}) {
  int status = 0;
  fitsfile* fp = nullptr;

  // cfitsio requires '!' prefix to overwrite existing files
  const std::string path = "!" + filename;
  fits_create_file(&fp, path.c_str(), &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to create FITS file: " + filename, status);
  }

  const detail::FitsFileGuard guard(fp);

  // Create 2D image HDU (FLOAT_IMG = -32 in cfitsio)
  long naxes[2] = {static_cast<long>(nx), static_cast<long>(ny)};
  fits_create_img(fp, FLOAT_IMG, 2, naxes, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to create image HDU", status);
  }

  // Write pixel data (cfitsio expects non-const void* but does not modify data)
  const long npixels = static_cast<long>(nx) * static_cast<long>(ny);
  fits_write_img(fp, TFLOAT, 1, npixels,                   // NOLINT(misc-include-cleaner)
                 const_cast<float*>(data), &status);       // NOLINT(cppcoreguidelines-pro-type-const-cast)
  if (status != 0) {
    throw FitsError("Failed to write pixel data", status);
  }

  // Write header keywords
  detail::writeWcs(fp, header.wcs, nx, ny);
  detail::writeSourceInfo(fp, header.source);
  detail::writeProvenance(fp, header.provenance);

  // Write BUNIT (physical units of pixel values)
  detail::writeKeyStr(fp, "BUNIT", "JY/PIXEL", "Pixel value units");
}

/**
 * @brief Write a 2D double-precision image to a FITS file.
 *
 * Same as writeFitsImage(float*) but for double-precision data.
 * Uses DOUBLE_IMG (-64) FITS type.
 */
inline void writeFitsImage(const std::string& filename,
                           const double* data, int nx, int ny,
                           const FitsHeader& header = FitsHeader{}) {
  int status = 0;
  fitsfile* fp = nullptr;

  const std::string path = "!" + filename;
  fits_create_file(&fp, path.c_str(), &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to create FITS file: " + filename, status);
  }

  const detail::FitsFileGuard guard(fp);

  long naxes[2] = {static_cast<long>(nx), static_cast<long>(ny)};
  fits_create_img(fp, DOUBLE_IMG, 2, naxes, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to create image HDU", status);
  }

  const long npixels = static_cast<long>(nx) * static_cast<long>(ny);
  fits_write_img(fp, TDOUBLE, 1, npixels,                    // NOLINT(misc-include-cleaner)
                 const_cast<double*>(data), &status);        // NOLINT(cppcoreguidelines-pro-type-const-cast)
  if (status != 0) {
    throw FitsError("Failed to write pixel data", status);
  }

  detail::writeWcs(fp, header.wcs, nx, ny);
  detail::writeSourceInfo(fp, header.source);
  detail::writeProvenance(fp, header.provenance);

  detail::writeKeyStr(fp, "BUNIT", "JY/PIXEL", "Pixel value units");
}

/**
 * @brief Read back a FITS image for verification.
 *
 * Reads a 2D float FITS image and returns the pixel data along with
 * image dimensions.
 *
 * @param filename Input FITS filename
 * @param nx Output: image width
 * @param ny Output: image height
 * @return Pixel data (nx * ny floats, row-major)
 * @throws FitsError on cfitsio failure
 */
[[nodiscard]] inline std::vector<float> readFitsImage(const std::string& filename,
                                                       int& nx, int& ny) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  const detail::FitsFileGuard guard(fp);

  // Get image dimensions
  int naxis = 0;
  fits_get_img_dim(fp, &naxis, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0 || naxis != 2) {
    throw FitsError("Expected 2D image, got " + std::to_string(naxis) + "D", status);
  }

  long naxes[2] = {0, 0};
  fits_get_img_size(fp, 2, naxes, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to get image size", status);
  }

  nx = static_cast<int>(naxes[0]);
  ny = static_cast<int>(naxes[1]);

  const long npixels = naxes[0] * naxes[1];
  std::vector<float> data(static_cast<size_t>(npixels));

  int anynull = 0;
  float nullval = 0.0f;
  fits_read_img(fp, TFLOAT, 1, npixels, &nullval, data.data(), &anynull, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to read pixel data", status);
  }

  return data;
}

/**
 * @brief Read a string keyword from a FITS file.
 *
 * @param filename FITS file path
 * @param keyword Keyword name (max 8 chars)
 * @return Keyword value string
 * @throws FitsError if keyword not found or file cannot be opened
 */
[[nodiscard]] inline std::string readFitsKeyword(const std::string& filename,
                                                  const std::string& keyword) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  const detail::FitsFileGuard guard(fp);

  char value[FLEN_VALUE];
  fits_read_key_str(fp, keyword.c_str(), value, nullptr, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Keyword not found: " + keyword, status);
  }

  return {value};
}

/**
 * @brief Read a double keyword from a FITS file.
 */
[[nodiscard]] inline double readFitsKeywordDbl(const std::string& filename,
                                               const std::string& keyword) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  const detail::FitsFileGuard guard(fp);

  double value = 0.0;
  fits_read_key_dbl(fp, keyword.c_str(), &value, nullptr, &status);  // NOLINT(misc-include-cleaner)
  if (status != 0) {
    throw FitsError("Keyword not found: " + keyword, status);
  }

  return value;
}

} // namespace physics

#endif // PHYSICS_FITS_WRITER_H
