/**
 * @file tests/disk_transfer_test.cpp
 * @brief Orbiting-emitter energy shift and blackbody chroma (disk_transfer.h).
 *
 * Face-on (lambda = 0) g at the ISCO is 1/u^t of the circular orbit:
 * sqrt(1 - 3/r) at a = 0, 0.370868 at a = 0.9, 0.092670 at a = 0.998
 * (scripts/gen_page_thorne_reference.py). Photons emitted along the orbital
 * motion (lambda > 0 for a disk orbiting in +phi) are blueshifted, g > 1, on
 * the approaching limb; photons against it are redshifted more than face-on.
 * The redshift LUT (lut.h) stores z = u^t - 1 of the same emitter.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>

#include <gtest/gtest.h>

#include "disk_transfer.h"
#include "lut.h"
#include "page_thorne.h"

TEST(DiskTransfer, FaceOnIscoShiftIsInverseUt) {
  EXPECT_NEAR(physics::diskTransferG(physics::pageThorneIscoRadius(0.9), 0.9, 0.0),
              0.370867944398646, 1e-9);
  EXPECT_NEAR(physics::diskTransferG(physics::pageThorneIscoRadius(0.998), 0.998, 0.0),
              0.0926703083653686, 1e-9);
  EXPECT_NEAR(physics::diskTransferG(physics::pageThorneIscoRadius(0.5), 0.5, 0.0),
              0.602664534741558, 1e-9);
  for (double const r : {6.0, 10.0, 40.0}) {
    EXPECT_NEAR(physics::diskTransferG(r, 0.0, 0.0), std::sqrt(1.0 - (3.0 / r)), 1e-14)
        << "r = " << r;
  }
}

TEST(DiskTransfer, ApproachingLimbIsBlueshifted) {
  for (double const a : {0.0, 0.6, 0.998}) {
    double const r = 3.0 * physics::pageThorneIscoRadius(a);
    // Edge-on, a photon leaving the approaching limb along the orbital
    // motion carries lambda = r in the flat-space limit.
    double const lambda = r;
    EXPECT_GT(physics::diskTransferG(r, a, lambda), 1.0) << "a = " << a;
    EXPECT_LT(physics::diskTransferG(r, a, -lambda), physics::diskTransferG(r, a, 0.0))
        << "a = " << a;
  }
  // Edge-on Schwarzschild at r = 6 with the flat-space limb lambda = r:
  // g = sqrt(1 - 3/r) / (1 - r^{-1/2}) at Omega r = r^{-1/2}.
  double const r = 6.0;
  EXPECT_NEAR(physics::diskTransferG(r, 0.0, r),
              std::sqrt(1.0 - (3.0 / r)) / (1.0 - (1.0 / std::sqrt(r))), 1e-14);
}

TEST(DiskTransfer, InvalidEmittersReturnZero) {
  // Inside the prograde photon orbit (r = 3 at a = 0) no circular orbit exists.
  EXPECT_EQ(physics::diskTransferG(2.9, 0.0, 0.0), 0.0);
  // A photon needing non-positive local energy (1 - Omega lambda <= 0).
  double const r = 10.0;
  EXPECT_EQ(physics::diskTransferG(r, 0.0, 1.0 / physics::keplerianOmega(r, 0.0)), 0.0);
}

TEST(DiskTransfer, BlackbodyChromaHasUnitLuminanceAndOrderedHue) {
  for (double const t : {2500.0, 4000.0, 5000.0, 6500.0, 10000.0, 20000.0}) {
    std::array<double, 3> const rgb = physics::blackbodyChromaLinearSrgb(t);
    double const luminance = (0.2126729 * rgb[0]) + (0.7151522 * rgb[1]) + (0.0721750 * rgb[2]);
    EXPECT_NEAR(luminance, 1.0, 2e-3) << "T = " << t;
  }
  // Blue-to-red ratio rises monotonically with temperature.
  double previous = 0.0;
  for (double const t : {2000.0, 3000.0, 4500.0, 6500.0, 9000.0, 15000.0}) {
    std::array<double, 3> const rgb = physics::blackbodyChromaLinearSrgb(t);
    double const ratio = rgb[2] / rgb[0];
    EXPECT_GT(ratio, previous) << "T = " << t;
    previous = ratio;
  }
  // 6500 K sits within 7% of equal-energy white in linear sRGB.
  std::array<double, 3> const white = physics::blackbodyChromaLinearSrgb(6500.0);
  EXPECT_NEAR(white[0], white[1], 0.07);
  EXPECT_NEAR(white[2], white[1], 0.07);
}

TEST(DiskTransfer, RedshiftLutStoresEmitterRedshift) {
  // Negative spin is a retrograde disk: its domain starts at the retrograde
  // ISCO, where the signed emitter redshift is finite.
  for (double const aStar : {0.0, 0.9, 0.998, -0.9}) {
    physics::Lut1D const lut = physics::generateRedshiftLut(64, 4.0e6, aStar);
    ASSERT_EQ(lut.values.size(), 64U);
    // First sample sits at the ISCO: z = 1/g - 1 of the face-on emitter.
    double const g = physics::diskTransferG(physics::pageThorneIscoRadius(aStar), aStar, 0.0);
    double const expected = std::fmin((1.0 / g) - 1.0, 10.0);
    EXPECT_NEAR(static_cast<double>(lut.values.front()), expected, 1e-5 * (1.0 + expected))
        << "a = " << aStar;
    EXPECT_GT(lut.values.front(), lut.values.back());
  }
}

TEST(DiskTransfer, EmissivityLutCoversTheSignedDisk) {
  // At a* = -0.9 the retrograde disk starts at 8.72 M; its LUT domain must
  // start there too, so every sample past the zero-torque edge carries flux.
  for (double const aStar : {0.9, -0.9}) {
    physics::Lut1D const lut = physics::generateEmissivityLut(64, 4.0e6, aStar, 0.1);
    ASSERT_EQ(lut.values.size(), 64U);
    EXPECT_NEAR(2.0 * static_cast<double>(lut.rMin), physics::pageThorneIscoRadius(aStar), 1e-5)
        << "a = " << aStar;
    for (std::size_t i = 1; i < lut.values.size(); ++i) {
      EXPECT_GT(lut.values.at(i), 0.0F) << "a = " << aStar << " sample " << i;
    }
    EXPECT_FLOAT_EQ(*std::ranges::max_element(lut.values), 1.0F) << "a = " << aStar;
  }
}
