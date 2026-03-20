/**
 * @file fits_writer_test.cpp
 * @brief Tests for FITS image output.
 *
 * Validates round-trip write/read of 2D images with WCS headers,
 * source metadata, and provenance keywords.
 */

#include <gtest/gtest.h>
#include "physics/fits_writer.h"
#include <cmath>
#include <cstdio>
#include <filesystem>
#include <vector>

namespace {

// Temporary file helper that cleans up on destruction
class TempFitsFile {
public:
  explicit TempFitsFile(const std::string& name)
      : path_(std::filesystem::temp_directory_path() / name) {}
  ~TempFitsFile() { std::filesystem::remove(path_); }
  [[nodiscard]] std::string str() const { return path_.string(); }

private:
  std::filesystem::path path_;
};

} // namespace

// --------------------------------------------------------------------------
// Basic round-trip: write float image, read it back, compare
// --------------------------------------------------------------------------
TEST(FitsWriter, RoundTripFloat32) {
  TempFitsFile tmp("test_roundtrip_f32.fits");

  constexpr int NX = 64;
  constexpr int NY = 48;
  std::vector<float> image(NX * NY);
  for (int j = 0; j < NY; ++j) {
    for (int i = 0; i < NX; ++i) {
      // Simple gradient pattern
      image[static_cast<size_t>(j * NX + i)] =
          static_cast<float>(i + j) / static_cast<float>(NX + NY);
    }
  }

  // Write
  physics::FitsHeader hdr;
  hdr.source.object = "TestSource";
  hdr.source.mass_msun = 6.5e9;
  hdr.source.spin = 0.94;
  hdr.provenance.code_version = "1.0.0-test";

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), NX, NY, hdr));

  // Read back
  int rx = 0, ry = 0;
  std::vector<float> readback;
  ASSERT_NO_THROW(readback = physics::read_fits_image(tmp.str(), rx, ry));

  EXPECT_EQ(rx, NX);
  EXPECT_EQ(ry, NY);
  ASSERT_EQ(readback.size(), image.size());

  for (size_t k = 0; k < image.size(); ++k) {
    EXPECT_FLOAT_EQ(readback[k], image[k])
        << "Mismatch at pixel " << k;
  }
}

// --------------------------------------------------------------------------
// Round-trip: write double image, read back as float (cfitsio converts)
// --------------------------------------------------------------------------
TEST(FitsWriter, RoundTripFloat64) {
  TempFitsFile tmp("test_roundtrip_f64.fits");

  constexpr int NX = 32;
  constexpr int NY = 32;
  std::vector<double> image(NX * NY);
  for (size_t k = 0; k < image.size(); ++k) {
    image[k] = std::sin(static_cast<double>(k) * 0.1);
  }

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), NX, NY));

  // cfitsio can read DOUBLE_IMG as TFLOAT (converts on the fly)
  int rx = 0, ry = 0;
  std::vector<float> readback;
  ASSERT_NO_THROW(readback = physics::read_fits_image(tmp.str(), rx, ry));

  EXPECT_EQ(rx, NX);
  EXPECT_EQ(ry, NY);

  for (size_t k = 0; k < image.size(); ++k) {
    EXPECT_NEAR(readback[k], static_cast<float>(image[k]), 1e-6f)
        << "Mismatch at pixel " << k;
  }
}

// --------------------------------------------------------------------------
// WCS keywords are written correctly
// --------------------------------------------------------------------------
TEST(FitsWriter, WCSKeywords) {
  TempFitsFile tmp("test_wcs.fits");

  constexpr int NX = 128;
  constexpr int NY = 128;
  std::vector<float> image(NX * NY, 1.0f);

  physics::FitsHeader hdr;
  // M87*: 42 uas shadow at 16.8 Mpc
  hdr.wcs = physics::wcs_from_fov(200.0, NX, NY); // 200 uas FOV
  hdr.wcs.crval1 = 187.7059308; // M87 RA (J2000)
  hdr.wcs.crval2 = 12.3911231;  // M87 Dec (J2000)

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), NX, NY, hdr));

  // Verify WCS keywords
  std::string ctype1 = physics::read_fits_keyword(tmp.str(), "CTYPE1");
  EXPECT_EQ(ctype1, "RA---TAN");

  std::string ctype2 = physics::read_fits_keyword(tmp.str(), "CTYPE2");
  EXPECT_EQ(ctype2, "DEC--TAN");

  double crval1 = physics::read_fits_keyword_dbl(tmp.str(), "CRVAL1");
  EXPECT_NEAR(crval1, 187.7059308, 1e-6);

  double crval2 = physics::read_fits_keyword_dbl(tmp.str(), "CRVAL2");
  EXPECT_NEAR(crval2, 12.3911231, 1e-6);

  // Pixel scale: 200 uas / 128 pixels = 1.5625 uas/pixel
  // 1.5625 uas = 1.5625e-6 arcsec = 1.5625e-6/3600 deg
  double expected_cdelt = 200.0e-6 / 3600.0 / 128.0;
  double cdelt1 = physics::read_fits_keyword_dbl(tmp.str(), "CDELT1");
  EXPECT_NEAR(std::abs(cdelt1), expected_cdelt, 1e-20);
  EXPECT_LT(cdelt1, 0.0); // East-left convention
}

// --------------------------------------------------------------------------
// Source metadata keywords
// --------------------------------------------------------------------------
TEST(FitsWriter, SourceMetadata) {
  TempFitsFile tmp("test_source.fits");

  constexpr int N = 16;
  std::vector<float> image(N * N, 0.0f);

  physics::FitsHeader hdr;
  hdr.source.object = "Sgr A*";
  hdr.source.mass_msun = 4.0e6;
  hdr.source.spin = 0.5;
  hdr.source.distance_cm = 8.3e3 * physics::PARSEC; // 8.3 kpc
  hdr.source.inclination_deg = 30.0;
  hdr.source.freq_hz = 230.0e9; // 230 GHz

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), N, N, hdr));

  EXPECT_EQ(physics::read_fits_keyword(tmp.str(), "OBJECT"), "Sgr A*");

  double mass = physics::read_fits_keyword_dbl(tmp.str(), "BH_MASS");
  EXPECT_NEAR(mass, 4.0e6, 1.0);

  double spin = physics::read_fits_keyword_dbl(tmp.str(), "BH_SPIN");
  EXPECT_NEAR(spin, 0.5, 1e-10);

  double freq = physics::read_fits_keyword_dbl(tmp.str(), "FREQ");
  EXPECT_NEAR(freq, 230.0e9, 1.0);
}

// --------------------------------------------------------------------------
// Provenance keywords
// --------------------------------------------------------------------------
TEST(FitsWriter, ProvenanceKeywords) {
  TempFitsFile tmp("test_provenance.fits");

  constexpr int N = 8;
  std::vector<float> image(N * N, 0.0f);

  physics::FitsHeader hdr;
  hdr.provenance.code_name = "Blackhole";
  hdr.provenance.code_version = "1.0.0";
  hdr.provenance.git_hash = "abc123def456";
  hdr.provenance.compiler = "GCC 14.2.1";
  hdr.provenance.build_type = "Release";

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), N, N, hdr));

  EXPECT_EQ(physics::read_fits_keyword(tmp.str(), "ORIGIN"), "Blackhole");
  EXPECT_EQ(physics::read_fits_keyword(tmp.str(), "GITHASH"), "abc123def456");
  EXPECT_EQ(physics::read_fits_keyword(tmp.str(), "BLDTYPE"), "Release");
}

// --------------------------------------------------------------------------
// FOV calculation from source parameters
// --------------------------------------------------------------------------
TEST(FitsWriter, FovFromSource) {
  // M87*: M = 6.5e9 Msun, D = 16.8 Mpc
  double m87_fov = physics::fov_from_source(
      6.5e9,                  // mass [Msun]
      16.8e6 * physics::PARSEC, // distance [cm]
      20.0                    // 20 r_g half-FOV
  );

  // r_g = GM/c^2 = 6.67e-8 * 6.5e9 * 1.99e33 / (3e10)^2 ~ 9.6e14 cm
  // FOV_rad = 2 * 20 * 9.6e14 / (16.8e6 * 3.09e18) ~ 7.38e-10 rad
  // FOV_uas ~ 7.38e-10 * 206265e6 ~ 152 uas
  EXPECT_GT(m87_fov, 100.0);
  EXPECT_LT(m87_fov, 300.0);

  // Sgr A*: M = 4e6 Msun, D = 8.3 kpc
  double sgra_fov = physics::fov_from_source(
      4.0e6,
      8.3e3 * physics::PARSEC,
      20.0
  );

  // Sgr A* angular size is ~50 uas shadow, FOV at 20 r_g should be ~200 uas
  EXPECT_GT(sgra_fov, 50.0);
  EXPECT_LT(sgra_fov, 500.0);
}

// --------------------------------------------------------------------------
// Overwrite existing file
// --------------------------------------------------------------------------
TEST(FitsWriter, OverwriteExistingFile) {
  TempFitsFile tmp("test_overwrite.fits");

  constexpr int N = 8;
  std::vector<float> image1(N * N, 1.0f);
  std::vector<float> image2(N * N, 2.0f);

  // Write first file
  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image1.data(), N, N));

  // Overwrite with different data
  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image2.data(), N, N));

  // Verify second data was written
  int rx = 0, ry = 0;
  auto readback = physics::read_fits_image(tmp.str(), rx, ry);
  EXPECT_FLOAT_EQ(readback[0], 2.0f);
}

// --------------------------------------------------------------------------
// WCS auto-centering
// --------------------------------------------------------------------------
TEST(FitsWriter, WCSAutoCenter) {
  TempFitsFile tmp("test_autocenter.fits");

  constexpr int NX = 100;
  constexpr int NY = 80;
  std::vector<float> image(NX * NY, 0.0f);

  physics::FitsHeader hdr;
  // Leave crpix at 0 to trigger auto-centering

  ASSERT_NO_THROW(physics::write_fits_image(tmp.str(), image.data(), NX, NY, hdr));

  double crpix1 = physics::read_fits_keyword_dbl(tmp.str(), "CRPIX1");
  double crpix2 = physics::read_fits_keyword_dbl(tmp.str(), "CRPIX2");

  EXPECT_NEAR(crpix1, 50.5, 1e-6); // (100+1)/2
  EXPECT_NEAR(crpix2, 40.5, 1e-6); // (80+1)/2
}
