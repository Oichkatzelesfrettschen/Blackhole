/**
 * @file fits_writer_test.cpp
 * @brief Tests for FITS image output.
 *
 * Validates round-trip write/read of 2D images with WCS headers,
 * source metadata, and provenance keywords.
 */

#include <gtest/gtest.h>
#include "physics/constants.h"
#include "physics/fits_writer.h"
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <filesystem>
#include <string>
#include <vector>

namespace {

// Temporary file helper that cleans up on destruction
class TempFitsFile {
public:
  explicit TempFitsFile(const std::string& name)
      : path_(std::filesystem::temp_directory_path() / name) {}
  ~TempFitsFile() { std::filesystem::remove(path_); }
  TempFitsFile(const TempFitsFile&) = delete;
  TempFitsFile& operator=(const TempFitsFile&) = delete;
  TempFitsFile(TempFitsFile&&) = delete;
  TempFitsFile& operator=(TempFitsFile&&) = delete;
  [[nodiscard]] std::string str() const { return path_.string(); }

private:
  std::filesystem::path path_;
};

} // namespace

// --------------------------------------------------------------------------
// Basic round-trip: write float image, read it back, compare
// --------------------------------------------------------------------------
// NOLINTNEXTLINE(readability-function-cognitive-complexity) -- test body with nested loops
TEST(FitsWriter, RoundTripFloat32) {
  TempFitsFile const tmp("test_roundtrip_f32.fits");

  constexpr int nx = 64;
  constexpr int ny = 48;
  std::vector<float> image(static_cast<size_t>(nx) * static_cast<size_t>(ny));
  for (int j = 0; j < ny; ++j) {
    for (int i = 0; i < nx; ++i) {
      // Simple gradient pattern
      image.at((static_cast<size_t>(j) * static_cast<size_t>(nx)) + static_cast<size_t>(i)) =
          static_cast<float>(i + j) / static_cast<float>(nx + ny);
    }
  }

  // Write
  physics::FitsHeader hdr;
  hdr.source.object = "TestSource";
  hdr.source.massMsun = 6.5e9;
  hdr.source.spin = 0.94;
  hdr.provenance.codeVersion = "1.0.0-test";

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), nx, ny, hdr));

  // Read back
  int rx = 0;
  int ry = 0;
  std::vector<float> readback;
  ASSERT_NO_THROW(readback = physics::readFitsImage(tmp.str(), rx, ry));

  EXPECT_EQ(rx, nx);
  EXPECT_EQ(ry, ny);
  ASSERT_EQ(readback.size(), image.size());

  for (size_t k = 0; k < image.size(); ++k) {
    EXPECT_FLOAT_EQ(readback.at(k), image.at(k))
        << "Mismatch at pixel " << k;
  }
}

// --------------------------------------------------------------------------
// Round-trip: write double image, read back as float (cfitsio converts)
// --------------------------------------------------------------------------
TEST(FitsWriter, RoundTripFloat64) {
  TempFitsFile const tmp("test_roundtrip_f64.fits");

  constexpr int nx = 32;
  constexpr int ny = 32;
  std::vector<double> image(static_cast<size_t>(nx) * static_cast<size_t>(ny));
  for (size_t k = 0; k < image.size(); ++k) {
    image.at(k) = std::sin(static_cast<double>(k) * 0.1);
  }

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), nx, ny));

  // cfitsio can read DOUBLE_IMG as TFLOAT (converts on the fly)
  int rx = 0;
  int ry = 0;
  std::vector<float> readback;
  ASSERT_NO_THROW(readback = physics::readFitsImage(tmp.str(), rx, ry));

  EXPECT_EQ(rx, nx);
  EXPECT_EQ(ry, ny);

  for (size_t k = 0; k < image.size(); ++k) {
    EXPECT_NEAR(readback.at(k), static_cast<float>(image.at(k)), 1e-6f)
        << "Mismatch at pixel " << k;
  }
}

// --------------------------------------------------------------------------
// WCS keywords are written correctly
// --------------------------------------------------------------------------
TEST(FitsWriter, WCSKeywords) {
  TempFitsFile const tmp("test_wcs.fits");

  constexpr int nx = 128;
  constexpr int ny = 128;
  std::vector<float> image(static_cast<size_t>(nx) * static_cast<size_t>(ny), 1.0f);

  physics::FitsHeader hdr;
  // M87*: 42 uas shadow at 16.8 Mpc
  hdr.wcs = physics::wcsFromFov(200.0, nx, ny); // 200 uas FOV
  hdr.wcs.crval1 = 187.7059308; // M87 RA (J2000)
  hdr.wcs.crval2 = 12.3911231;  // M87 Dec (J2000)

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), nx, ny, hdr));

  // Verify WCS keywords
  std::string const ctype1 = physics::readFitsKeyword(tmp.str(), "CTYPE1");
  EXPECT_EQ(ctype1, "RA---TAN");

  std::string const ctype2 = physics::readFitsKeyword(tmp.str(), "CTYPE2");
  EXPECT_EQ(ctype2, "DEC--TAN");

  double const crval1 = physics::readFitsKeywordDbl(tmp.str(), "CRVAL1");
  EXPECT_NEAR(crval1, 187.7059308, 1e-6);

  double const crval2 = physics::readFitsKeywordDbl(tmp.str(), "CRVAL2");
  EXPECT_NEAR(crval2, 12.3911231, 1e-6);

  // Pixel scale: 200 uas / 128 pixels = 1.5625 uas/pixel
  // 1.5625 uas = 1.5625e-6 arcsec = 1.5625e-6/3600 deg
  double const expectedCdelt = 200.0e-6 / 3600.0 / 128.0;
  double const cdelt1 = physics::readFitsKeywordDbl(tmp.str(), "CDELT1");
  EXPECT_NEAR(std::abs(cdelt1), expectedCdelt, 1e-20);
  EXPECT_LT(cdelt1, 0.0); // East-left convention
}

// --------------------------------------------------------------------------
// Source metadata keywords
// --------------------------------------------------------------------------
TEST(FitsWriter, SourceMetadata) {
  TempFitsFile const tmp("test_source.fits");

  constexpr int n = 16;
  std::vector<float> image(static_cast<size_t>(n) * static_cast<size_t>(n), 0.0f);

  physics::FitsHeader hdr;
  hdr.source.object = "Sgr A*";
  hdr.source.massMsun = 4.0e6;
  hdr.source.spin = 0.5;
  hdr.source.distanceCm = 8.3e3 * physics::PARSEC; // 8.3 kpc
  hdr.source.inclinationDeg = 30.0;
  hdr.source.freqHz = 230.0e9; // 230 GHz

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), n, n, hdr));

  EXPECT_EQ(physics::readFitsKeyword(tmp.str(), "OBJECT"), "Sgr A*");

  double const mass = physics::readFitsKeywordDbl(tmp.str(), "BH_MASS");
  EXPECT_NEAR(mass, 4.0e6, 1.0);

  double const spin = physics::readFitsKeywordDbl(tmp.str(), "BH_SPIN");
  EXPECT_NEAR(spin, 0.5, 1e-10);

  double const freq = physics::readFitsKeywordDbl(tmp.str(), "FREQ");
  EXPECT_NEAR(freq, 230.0e9, 1.0);
}

// --------------------------------------------------------------------------
// Provenance keywords
// --------------------------------------------------------------------------
TEST(FitsWriter, ProvenanceKeywords) {
  TempFitsFile const tmp("test_provenance.fits");

  constexpr int n = 8;
  std::vector<float> image(static_cast<size_t>(n) * static_cast<size_t>(n), 0.0f);

  physics::FitsHeader hdr;
  hdr.provenance.codeName = "Blackhole";
  hdr.provenance.codeVersion = "1.0.0";
  hdr.provenance.gitHash = "abc123def456";
  hdr.provenance.compiler = "GCC 14.2.1";
  hdr.provenance.buildType = "Release";

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), n, n, hdr));

  EXPECT_EQ(physics::readFitsKeyword(tmp.str(), "ORIGIN"), "Blackhole");
  EXPECT_EQ(physics::readFitsKeyword(tmp.str(), "GITHASH"), "abc123def456");
  EXPECT_EQ(physics::readFitsKeyword(tmp.str(), "BLDTYPE"), "Release");
}

// --------------------------------------------------------------------------
// FOV calculation from source parameters
// --------------------------------------------------------------------------
TEST(FitsWriter, FovFromSource) {
  // M87*: M = 6.5e9 Msun, D = 16.8 Mpc
  double const m87Fov = physics::fovFromSource(6.5e9,                    // mass [Msun]
                                               16.8e6 * physics::PARSEC, // distance [cm]
                                               20.0                      // 20 r_g half-FOV
  );

  // r_g = GM/c^2 = 6.67e-8 * 6.5e9 * 1.99e33 / (3e10)^2 ~ 9.6e14 cm
  // FOV_rad = 2 * 20 * 9.6e14 / (16.8e6 * 3.09e18) ~ 7.38e-10 rad
  // FOV_uas ~ 7.38e-10 * 206265e6 ~ 152 uas
  EXPECT_GT(m87Fov, 100.0);
  EXPECT_LT(m87Fov, 300.0);

  // Sgr A*: M = 4e6 Msun, D = 8.3 kpc
  double const sgraFov = physics::fovFromSource(4.0e6, 8.3e3 * physics::PARSEC, 20.0);

  // Sgr A* angular size is ~50 uas shadow, FOV at 20 r_g should be ~200 uas
  EXPECT_GT(sgraFov, 50.0);
  EXPECT_LT(sgraFov, 500.0);
}

// --------------------------------------------------------------------------
// Overwrite existing file
// --------------------------------------------------------------------------
TEST(FitsWriter, OverwriteExistingFile) {
  TempFitsFile const tmp("test_overwrite.fits");

  constexpr int n = 8;
  std::vector<float> image1(static_cast<size_t>(n) * static_cast<size_t>(n), 1.0f);
  std::vector<float> image2(static_cast<size_t>(n) * static_cast<size_t>(n), 2.0f);

  // Write first file
  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image1.data(), n, n));

  // Overwrite with different data
  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image2.data(), n, n));

  // Verify second data was written
  int rx = 0;
  int ry = 0;
  auto readback = physics::readFitsImage(tmp.str(), rx, ry);
  EXPECT_FLOAT_EQ(readback.at(0), 2.0f);
}

// --------------------------------------------------------------------------
// WCS auto-centering
// --------------------------------------------------------------------------
TEST(FitsWriter, WCSAutoCenter) {
  TempFitsFile const tmp("test_autocenter.fits");

  constexpr int nx = 100;
  constexpr int ny = 80;
  std::vector<float> image(static_cast<size_t>(nx) * static_cast<size_t>(ny), 0.0f);

  physics::FitsHeader const hdr;
  // Leave crpix at 0 to trigger auto-centering

  ASSERT_NO_THROW(physics::writeFitsImage(tmp.str(), image.data(), nx, ny, hdr));

  double const crpix1 = physics::readFitsKeywordDbl(tmp.str(), "CRPIX1");
  double const crpix2 = physics::readFitsKeywordDbl(tmp.str(), "CRPIX2");

  EXPECT_NEAR(crpix1, 50.5, 1e-6); // (100+1)/2
  EXPECT_NEAR(crpix2, 40.5, 1e-6); // (80+1)/2
}
