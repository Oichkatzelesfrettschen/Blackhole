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
 * HOW: Link against system cfitsio (pkg-config). Call write_fits_image() with
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
#include <cstdint>
#include <cstring>
#include <fitsio.h>
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
  std::string object;          // Source name (e.g., "M87*", "Sgr A*")
  double mass_msun = 0.0;     // Black hole mass [solar masses]
  double spin = 0.0;          // Dimensionless spin a* [0, 1)
  double distance_cm = 0.0;   // Distance to source [cm]
  double inclination_deg = 0.0; // Observer inclination [degrees]
  double freq_hz = 0.0;       // Observing frequency [Hz]
  double fov_uas = 0.0;       // Field of view [microarcseconds]
};

/**
 * @brief Reproducibility metadata.
 */
struct FitsProvenance {
  std::string code_name = "Blackhole";
  std::string code_version;
  std::string git_hash;
  std::string compiler;
  std::string build_type;
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
  explicit FitsError(const std::string& msg, int cfitsio_status = 0)
      : std::runtime_error(format_message(msg, cfitsio_status)),
        status_(cfitsio_status) {}

  [[nodiscard]] int cfitsio_status() const noexcept { return status_; }

private:
  int status_;

  static std::string format_message(const std::string& msg, int status) {
    if (status == 0) return msg;
    char errmsg[FLEN_ERRMSG];
    fits_get_errstatus(status, errmsg);
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
    if (fp_) {
      int status = 0;
      fits_close_file(fp_, &status);
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
inline void write_key_str(fitsfile* fp, const char* key, const std::string& val,
                          const char* comment = nullptr) {
  int status = 0;
  // fits_update_key_str handles const-correctness internally
  fits_update_key_str(fp, key, val.c_str(), comment, &status);
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write a double keyword.
inline void write_key_dbl(fitsfile* fp, const char* key, double val,
                          int decimals = 15, const char* comment = nullptr) {
  int status = 0;
  fits_update_key_dbl(fp, key, val, decimals, comment, &status);
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write a long keyword.
inline void write_key_lng(fitsfile* fp, const char* key, long val,
                          const char* comment = nullptr) {
  int status = 0;
  fits_update_key_lng(fp, key, val, comment, &status);
  if (status != 0) {
    throw FitsError(std::string("Failed to write keyword ") + key, status);
  }
}

/// Write WCS keywords for a 2D sky-plane image.
inline void write_wcs(fitsfile* fp, const WCSParams& wcs, int nx, int ny) {
  double crpix1 = (wcs.crpix1 > 0.0) ? wcs.crpix1 : (static_cast<double>(nx) + 1.0) / 2.0;
  double crpix2 = (wcs.crpix2 > 0.0) ? wcs.crpix2 : (static_cast<double>(ny) + 1.0) / 2.0;

  write_key_str(fp, "CTYPE1", "RA---TAN", "Coordinate type axis 1");
  write_key_str(fp, "CTYPE2", "DEC--TAN", "Coordinate type axis 2");
  write_key_dbl(fp, "CRPIX1", crpix1, 6, "Reference pixel axis 1");
  write_key_dbl(fp, "CRPIX2", crpix2, 6, "Reference pixel axis 2");
  write_key_dbl(fp, "CRVAL1", wcs.crval1, 12, "[deg] Reference RA");
  write_key_dbl(fp, "CRVAL2", wcs.crval2, 12, "[deg] Reference Dec");

  if (wcs.cdelt1 != 0.0) {
    write_key_dbl(fp, "CDELT1", wcs.cdelt1, 15, "[deg] Pixel scale axis 1");
    write_key_dbl(fp, "CDELT2", wcs.cdelt2, 15, "[deg] Pixel scale axis 2");
  }

  write_key_str(fp, "CUNIT1", "deg", "Units of axis 1");
  write_key_str(fp, "CUNIT2", "deg", "Units of axis 2");
  write_key_str(fp, "RADESYS", "ICRS", "Reference frame");
}

/// Write source metadata keywords.
inline void write_source_info(fitsfile* fp, const FitsSourceInfo& src) {
  if (!src.object.empty()) {
    write_key_str(fp, "OBJECT", src.object, "Source name");
  }
  if (src.mass_msun > 0.0) {
    write_key_dbl(fp, "BH_MASS", src.mass_msun, 6, "[Msun] Black hole mass");
  }
  if (src.spin != 0.0 || src.mass_msun > 0.0) {
    write_key_dbl(fp, "BH_SPIN", src.spin, 6, "Dimensionless spin a*");
  }
  if (src.distance_cm > 0.0) {
    double dist_mpc = src.distance_cm / MPC;
    write_key_dbl(fp, "BH_DIST", dist_mpc, 6, "[Mpc] Distance");
  }
  if (src.inclination_deg != 0.0) {
    write_key_dbl(fp, "BH_INCL", src.inclination_deg, 4, "[deg] Inclination");
  }
  if (src.freq_hz > 0.0) {
    write_key_dbl(fp, "FREQ", src.freq_hz, 6, "[Hz] Observing frequency");
  }
  if (src.fov_uas > 0.0) {
    write_key_dbl(fp, "FOV_UAS", src.fov_uas, 4, "[uas] Field of view");
  }
}

/// Write provenance keywords.
inline void write_provenance(fitsfile* fp, const FitsProvenance& prov) {
  write_key_str(fp, "ORIGIN", prov.code_name, "Software that created this file");
  if (!prov.code_version.empty()) {
    write_key_str(fp, "VERSION", prov.code_version, "Code version");
  }
  if (!prov.git_hash.empty()) {
    write_key_str(fp, "GITHASH", prov.git_hash, "Git commit hash");
  }
  if (!prov.compiler.empty()) {
    write_key_str(fp, "COMPILER", prov.compiler, "Compiler used");
  }
  if (!prov.build_type.empty()) {
    write_key_str(fp, "BLDTYPE", prov.build_type, "Build type");
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
 * @param fov_uas Field of view [microarcseconds]
 * @param nx Number of pixels in X
 * @param ny Number of pixels in Y
 * @return WCSParams with computed pixel scale (East-left convention)
 */
inline WCSParams wcs_from_fov(double fov_uas, int nx, int ny) {
  WCSParams wcs;
  // Convert uas to degrees: 1 uas = 1e-6 arcsec = 1e-6/3600 deg
  double fov_deg = fov_uas * 1.0e-6 / 3600.0;
  wcs.cdelt1 = -fov_deg / static_cast<double>(nx); // Negative = East-left (RA convention)
  wcs.cdelt2 = fov_deg / static_cast<double>(ny);
  return wcs;
}

/**
 * @brief Compute field of view in microarcseconds from source parameters.
 *
 * FOV = 2 * n_rg * r_g / D [radians], converted to microarcseconds.
 *
 * @param mass_msun Black hole mass [solar masses]
 * @param distance_cm Distance to source [cm]
 * @param n_rg Number of gravitational radii across half the FOV
 * @return Field of view [microarcseconds]
 */
inline double fov_from_source(double mass_msun, double distance_cm, double n_rg = 20.0) {
  double r_g = G * mass_msun * M_SUN / (C * C); // Gravitational radius [cm]
  double fov_rad = 2.0 * n_rg * r_g / distance_cm;
  // Convert radians to microarcseconds: 1 rad = 206265 arcsec = 206265e6 uas
  return fov_rad * 206265.0e6;
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
inline void write_fits_image(const std::string& filename,
                             const float* data, int nx, int ny,
                             const FitsHeader& header = FitsHeader{}) {
  int status = 0;
  fitsfile* fp = nullptr;

  // cfitsio requires '!' prefix to overwrite existing files
  std::string path = "!" + filename;
  fits_create_file(&fp, path.c_str(), &status);
  if (status != 0) {
    throw FitsError("Failed to create FITS file: " + filename, status);
  }

  detail::FitsFileGuard guard(fp);

  // Create 2D image HDU (FLOAT_IMG = -32 in cfitsio)
  long naxes[2] = {static_cast<long>(nx), static_cast<long>(ny)};
  fits_create_img(fp, FLOAT_IMG, 2, naxes, &status);
  if (status != 0) {
    throw FitsError("Failed to create image HDU", status);
  }

  // Write pixel data
  long npixels = static_cast<long>(nx) * static_cast<long>(ny);
  // cfitsio expects non-const pointer but does not modify the data for write
  fits_write_img(fp, TFLOAT, 1, npixels,
                 const_cast<float*>(data), &status);
  if (status != 0) {
    throw FitsError("Failed to write pixel data", status);
  }

  // Write header keywords
  detail::write_wcs(fp, header.wcs, nx, ny);
  detail::write_source_info(fp, header.source);
  detail::write_provenance(fp, header.provenance);

  // Write BUNIT (physical units of pixel values)
  detail::write_key_str(fp, "BUNIT", "JY/PIXEL", "Pixel value units");
}

/**
 * @brief Write a 2D double-precision image to a FITS file.
 *
 * Same as write_fits_image(float*) but for double-precision data.
 * Uses DOUBLE_IMG (-64) FITS type.
 */
inline void write_fits_image(const std::string& filename,
                             const double* data, int nx, int ny,
                             const FitsHeader& header = FitsHeader{}) {
  int status = 0;
  fitsfile* fp = nullptr;

  std::string path = "!" + filename;
  fits_create_file(&fp, path.c_str(), &status);
  if (status != 0) {
    throw FitsError("Failed to create FITS file: " + filename, status);
  }

  detail::FitsFileGuard guard(fp);

  long naxes[2] = {static_cast<long>(nx), static_cast<long>(ny)};
  fits_create_img(fp, DOUBLE_IMG, 2, naxes, &status);
  if (status != 0) {
    throw FitsError("Failed to create image HDU", status);
  }

  long npixels = static_cast<long>(nx) * static_cast<long>(ny);
  fits_write_img(fp, TDOUBLE, 1, npixels,
                 const_cast<double*>(data), &status);
  if (status != 0) {
    throw FitsError("Failed to write pixel data", status);
  }

  detail::write_wcs(fp, header.wcs, nx, ny);
  detail::write_source_info(fp, header.source);
  detail::write_provenance(fp, header.provenance);

  detail::write_key_str(fp, "BUNIT", "JY/PIXEL", "Pixel value units");
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
inline std::vector<float> read_fits_image(const std::string& filename,
                                          int& nx, int& ny) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  detail::FitsFileGuard guard(fp);

  // Get image dimensions
  int naxis = 0;
  fits_get_img_dim(fp, &naxis, &status);
  if (status != 0 || naxis != 2) {
    throw FitsError("Expected 2D image, got " + std::to_string(naxis) + "D", status);
  }

  long naxes[2] = {0, 0};
  fits_get_img_size(fp, 2, naxes, &status);
  if (status != 0) {
    throw FitsError("Failed to get image size", status);
  }

  nx = static_cast<int>(naxes[0]);
  ny = static_cast<int>(naxes[1]);

  long npixels = naxes[0] * naxes[1];
  std::vector<float> data(static_cast<size_t>(npixels));

  int anynull = 0;
  float nullval = 0.0f;
  fits_read_img(fp, TFLOAT, 1, npixels, &nullval, data.data(), &anynull, &status);
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
inline std::string read_fits_keyword(const std::string& filename,
                                     const std::string& keyword) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  detail::FitsFileGuard guard(fp);

  char value[FLEN_VALUE];
  fits_read_key_str(fp, keyword.c_str(), value, nullptr, &status);
  if (status != 0) {
    throw FitsError("Keyword not found: " + keyword, status);
  }

  return std::string(value);
}

/**
 * @brief Read a double keyword from a FITS file.
 */
inline double read_fits_keyword_dbl(const std::string& filename,
                                    const std::string& keyword) {
  int status = 0;
  fitsfile* fp = nullptr;

  fits_open_file(&fp, filename.c_str(), READONLY, &status);
  if (status != 0) {
    throw FitsError("Failed to open FITS file: " + filename, status);
  }

  detail::FitsFileGuard guard(fp);

  double value = 0.0;
  fits_read_key_dbl(fp, keyword.c_str(), &value, nullptr, &status);
  if (status != 0) {
    throw FitsError("Keyword not found: " + keyword, status);
  }

  return value;
}

} // namespace physics

#endif // PHYSICS_FITS_WRITER_H
