/**
 * @file observer_sky_view_test.cpp
 * @brief Gates for the observer-sky scene's CPU side (render/observer_sky_view.h):
 *        the observer clock against kerr_observer's circular orbits and the
 *        canon Miller numbers, the sky phase, the camera geometry, and the
 *        blackbody table against the luminous efficacy of a Planck spectrum.
 *
 * Runs from the repository root (WORKING_DIRECTORY) so the committed
 * assets/luts/blackbody_cie_lut.csv resolves.
 */

#include <array>
#include <chrono>
#include <cmath>
#include <filesystem>
#include <format>
#include <memory>
#include <numbers>
#include <optional>
#include <random>
#include <string>
#include <system_error>
#include <thread>

#include <gtest/gtest.h>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "render/observer_sky_view.h"
#include "render/render_state.h"
#include "ui/observer_panels.h"

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;
using blackhole::ObserverKind;

constexpr double K_PI = std::numbers::pi;
constexpr double K_STEFAN_BOLTZMANN = 5.670374419e-8; // W m^-2 K^-4 (CODATA 2018, exact form)

sky::ObserverKey requireKey(const std::optional<sky::ObserverKey> &key) {
  EXPECT_TRUE(key.has_value());
  return key.value_or(sky::ObserverKey{});
}

/** @brief A fresh directory under the system temporary path, removed with
 *         its contents when the scope ends (including an early ASSERT return). */
class ScratchDirectory {
public:
  ScratchDirectory() {
    std::random_device device;
    constexpr int attempts = 16;
    for (int attempt = 0; attempt < attempts && path_.empty(); ++attempt) {
      const std::filesystem::path candidate =
          std::filesystem::temp_directory_path() /
          std::format("observer_sky_view_test_{:08x}{:08x}", device(), device());
      std::error_code error;
      if (std::filesystem::create_directory(candidate, error)) {
        path_ = candidate;
      }
    }
  }
  ScratchDirectory(const ScratchDirectory &) = delete;
  ScratchDirectory &operator=(const ScratchDirectory &) = delete;
  ScratchDirectory(ScratchDirectory &&) = delete;
  ScratchDirectory &operator=(ScratchDirectory &&) = delete;
  ~ScratchDirectory() {
    if (!path_.empty()) {
      std::error_code error;
      std::filesystem::remove_all(path_, error);
    }
  }
  [[nodiscard]] const std::filesystem::path &path() const { return path_; }

private:
  std::filesystem::path path_;
};

/** @brief Polls until the renderer leaves Building, for at most `limit`. */
blackhole::ObserverSkyRenderer::Status
settle(blackhole::ObserverSkyRenderer &renderer,
       std::chrono::milliseconds limit = std::chrono::milliseconds(10000)) {
  const auto deadline = std::chrono::steady_clock::now() + limit;
  renderer.poll();
  while (renderer.status() == blackhole::ObserverSkyRenderer::Status::Building &&
         std::chrono::steady_clock::now() < deadline) {
    std::this_thread::sleep_for(std::chrono::milliseconds(5));
    renderer.poll();
  }
  return renderer.status();
}

sky::ObserverKey canonMiller() {
  const double x = ko::iscoOffset(blackhole::K_GARGANTUA_SPIN_DEFICIT, ko::OrbitSense::Prograde);
  const auto key =
      blackhole::observerKeyFor(blackhole::K_GARGANTUA_SPIN_DEFICIT, x, ObserverKind::Prograde);
  EXPECT_TRUE(key.has_value());
  return key.value_or(sky::ObserverKey{});
}

/**
 * The clock model's general form, dtau/dt = alpha sqrt(1 - v^2) and
 * Omega = omega + v alpha / varpi, must reproduce the Bardeen-Press-Teukolsky
 * orbit it is fed. At the canon Miller orbit (1 - a = 1.33e-14, prograde
 * ISCO) the canon numbers of docs/audits/physics-and-game-engine/03-game-engine.md
 * (section 4) follow: dtau/dt = 1.6286e-5 (one hour there is
 * seven years outside), Omega -> 1/(2M), a coordinate period of 4 pi M =
 * 1.72 h and a proper period of 0.10 s at M = 1e8 M_sun.
 */
TEST(ObserverSkyView, CanonClockMatchesMillerNumbers) {
  const sky::ObserverKey key = canonMiller();
  const ko::CircularOrbit orbit = ko::circularOrbit(key.epsilon, key.x, ko::OrbitSense::Prograde);
  const blackhole::ObserverClockModel clock = blackhole::observerClockModel(key, 1.0e8);
  EXPECT_NEAR(clock.properTimeRate / orbit.properTimeRate, 1.0, 1e-9);
  EXPECT_NEAR(clock.angularVelocity / orbit.angularVelocity, 1.0, 1e-12);
  EXPECT_NEAR(clock.properTimeRate, 1.6286e-5, 0.0001e-5);
  EXPECT_NEAR(1.0 / clock.properTimeRate / (7.0 * 365.25 * 24.0), 1.0, 0.005)
      << "one hour at Miller against seven outside years";
  EXPECT_NEAR(clock.secondsPerM, 492.549, 0.001);
  EXPECT_NEAR(clock.coordinatePeriodSeconds / (4.0 * K_PI * clock.secondsPerM), 1.0, 1e-4);
  EXPECT_NEAR(clock.coordinatePeriodSeconds / 3600.0, 1.719, 0.001);
  EXPECT_NEAR(clock.properPeriodSeconds, 0.1008, 0.0001);
}

TEST(ObserverSkyView, HoveringClocksAreTheLapseAndTheStaticRate) {
  const sky::ObserverKey zamo = requireKey(blackhole::observerKeyFor(0.1, 2.0, ObserverKind::Zamo));
  const ko::EquatorialFrame frame = ko::equatorialFrame(0.1, 2.0);
  const blackhole::ObserverClockModel zamoClock = blackhole::observerClockModel(zamo, 1.0);
  EXPECT_DOUBLE_EQ(zamoClock.properTimeRate, frame.alpha);
  EXPECT_DOUBLE_EQ(zamoClock.angularVelocity, frame.omega);

  // a = 0: the static observer is the ZAMO, dtau/dt = sqrt(1 - 2/r), Omega = 0.
  const sky::ObserverKey rest =
      requireKey(blackhole::observerKeyFor(1.0, 9.0, ObserverKind::Static));
  const blackhole::ObserverClockModel restClock = blackhole::observerClockModel(rest, 1.0);
  EXPECT_NEAR(restClock.properTimeRate, std::sqrt(1.0 - 0.2), 1e-15);
  EXPECT_EQ(restClock.angularVelocity, 0.0);
  EXPECT_EQ(restClock.coordinatePeriodSeconds, 0.0);
  EXPECT_EQ(blackhole::skyPhaseRadians(restClock, 1.0e6), 0.0);

  // Inside the ergoregion no observer is static.
  EXPECT_FALSE(blackhole::observerKeyFor(0.1, 0.5, ObserverKind::Static).has_value());
}

TEST(ObserverSkyView, SkyPhaseTurnsOncePerProperPeriod) {
  const blackhole::ObserverClockModel clock = blackhole::observerClockModel(canonMiller(), 1.0e8);
  const double period = clock.properPeriodSeconds;
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 0.25 * period), 0.5 * K_PI, 1e-9);
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 0.5 * period), K_PI, 1e-9);
  // A thousand turns later the double-precision phase is still exact to 1e-9.
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 1000.25 * period), 0.5 * K_PI, 1e-9);
}

/** @brief One look direction's camera basis: orthonormal, forward on the
 *         look, up toward the spin axis, and the look projecting to the
 *         screen center while its antipode projects nowhere. */
void checkViewBasis(double longitudeDeg, double latitudeDeg) {
  const double longitude = longitudeDeg * K_PI / 180.0;
  const double latitude = latitudeDeg * K_PI / 180.0;
  const auto basis = blackhole::observerViewBasis(longitude, latitude);
  const sky::Vec3 forward = sky::lookDirection(longitude, latitude);
  const auto dot = [](const sky::Vec3 &a, const sky::Vec3 &b) {
    return (a.at(0) * b.at(0)) + (a.at(1) * b.at(1)) + (a.at(2) * b.at(2));
  };
  EXPECT_NEAR(dot(basis.at(2), forward), 1.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(0), basis.at(1)), 0.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(0), basis.at(0)), 1.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(1), basis.at(1)), 1.0, 1e-15);
  EXPECT_LT(basis.at(1).at(1), 0.0) << "up leans toward the spin axis (-e_theta)";
  const auto center = blackhole::projectToPixel(basis, forward, 1.0, 1920, 1080);
  if (!center.has_value()) {
    GTEST_FAIL() << "the look direction projects off screen";
  }
  EXPECT_NEAR(center->at(0), 960.0, 1e-9);
  EXPECT_NEAR(center->at(1), 540.0, 1e-9);
  const sky::Vec3 behind{-forward.at(0), -forward.at(1), -forward.at(2)};
  EXPECT_FALSE(blackhole::projectToPixel(basis, behind, 1.0, 1920, 1080).has_value());
}

TEST(ObserverSkyView, ViewBasisIsRightHandedAndProjectsItsAxis) {
  checkViewBasis(0.0, 0.0);
  checkViewBasis(150.0, 0.0);
  checkViewBasis(-100.0, 40.0);
  checkViewBasis(30.0, -70.0);
}

/**
 * The table is the photopic luminance of a Planck spectrum. Its luminous
 * efficacy, luminance over radiance sigma T^4 / pi, is a textbook curve:
 * about 16 lm/W for CIE illuminant A's 2856 K, about 92 lm/W at the Sun's
 * 5772 K, peaking near 95 lm/W around 6500 K; D65's temperature renders
 * near-white; and on the Rayleigh-Jeans tail luminance grows as T.
 */
TEST(ObserverSkyView, BlackbodyTableHasPlanckEfficacyAndColor) {
  const auto table = blackhole::loadBlackbodyTable("assets/luts/blackbody_cie_lut.csv");
  if (!table.has_value()) {
    GTEST_FAIL() << "assets/luts/blackbody_cie_lut.csv did not load";
  }
  const auto efficacy = [&table](double temperature) {
    const double radiance = K_STEFAN_BOLTZMANN * std::pow(temperature, 4.0) / K_PI;
    return std::pow(10.0, table->at(std::log10(temperature)).at(3)) / radiance;
  };
  EXPECT_NEAR(efficacy(2856.0), 16.5, 1.0);
  EXPECT_NEAR(efficacy(5772.0), 92.0, 2.0);
  EXPECT_NEAR(efficacy(6504.0), 95.4, 2.0);
  const std::array<double, 4> d65 = table->at(std::log10(6504.0));
  EXPECT_NEAR(d65.at(0), 1.0, 0.06);
  EXPECT_NEAR(d65.at(1), 1.0, 0.06);
  EXPECT_NEAR(d65.at(2), 1.0, 0.06);
  const double slope = table->at(7.0).at(3) - table->at(6.0).at(3);
  EXPECT_NEAR(slope, 1.0, 0.01) << "log10 luminance per decade of T on the Rayleigh-Jeans tail";
}

/**
 * GLS 2017 (arXiv:1710.11112) Eq. A.12a: the NHEKline sits at alpha = -2 csc i
 * with |beta| < sqrt(3 + cos^2 i - 4 cot^2 i), which is sqrt(3) edge-on and
 * vanishes at i = arctan((4/3)^(1/4)) = 47.06 deg (Eq. A.7, "about 47"); Eq. A.6 puts the
 * r = 1 ends of the extremal shadow edge exactly on the line's ends.
 */
TEST(ObserverSkyView, NhekLineMatchesGrallaLupsascaStrominger) {
  const auto edgeOn = blackhole::nhekLine(0.5 * K_PI);
  if (!edgeOn.has_value()) {
    GTEST_FAIL() << "no NHEKline edge-on";
  }
  EXPECT_NEAR(edgeOn->alpha, -2.0, 1e-15);
  EXPECT_NEAR(edgeOn->halfLength, std::numbers::sqrt3, 1e-15);
  const double critical = std::atan(std::pow(4.0 / 3.0, 0.25));
  EXPECT_NEAR(critical * 180.0 / K_PI, 47.06, 0.01);
  EXPECT_FALSE(blackhole::nhekLine(critical - 1e-6).has_value());
  EXPECT_TRUE(blackhole::nhekLine(critical + 1e-6).has_value());
  const double inclination = 70.0 * K_PI / 180.0;
  const auto line = blackhole::nhekLine(inclination);
  const auto edge = blackhole::extremalShadowEdge(inclination, 3000);
  if (!line.has_value() || edge.empty()) {
    GTEST_FAIL() << "no NHEKline or shadow edge at 70 deg";
  }
  EXPECT_NEAR(edge.front().at(0), line->alpha, 1e-12);
  EXPECT_NEAR(edge.front().at(1), line->halfLength, 1e-12);
}

/**
 * The emission-side reading of the traced sky. At the Schwarzschild ISCO the
 * orbiter's received g spans 1/sqrt(2)..3/sqrt(2) (Opatrny et al. Eq. A12),
 * so its light leaves with g_emit in sqrt(2)/3..sqrt(2), and 12.2% of its sky
 * is shadow. At the paper's Miller orbit the received floor 1/sqrt(3) becomes
 * the emitted ceiling sqrt(3) -- the bound GLS derive (Eq. 3.14) for
 * near-extremal ISCO light at infinity, from the other end of the ray.
 */
TEST(ObserverSkyView, EmissionMirrorsTheReceivedSky) {
  const sky::LutDimensions small{.width = 128, .height = 64, .tileRadial = 64, .tileAzimuth = 64};
  const sky::ObserverSkyLut isco = sky::buildObserverSkyLut(
      requireKey(blackhole::observerKeyFor(1.0, 5.0, ObserverKind::Prograde)), small,
      sky::TraceSettings{});
  const blackhole::EmissionSummary schwarzschild = blackhole::summarizeEmission(isco);
  EXPECT_NEAR(schwarzschild.gEmitMax, std::sqrt(2.0), 2e-3);
  EXPECT_NEAR(schwarzschild.gEmitMin, std::sqrt(2.0) / 3.0, 2e-3);
  EXPECT_NEAR(schwarzschild.escapingFraction, 1.0 - 0.122, 0.006);
  EXPECT_EQ(schwarzschild.directFraction, 0.0);

  const sky::ObserverSkyLut miller = sky::buildObserverSkyLut(
      requireKey(blackhole::observerKeyFor(1.3e-14, 3.79e-5, ObserverKind::Prograde)), small,
      sky::TraceSettings{});
  const blackhole::EmissionSummary nearExtremal = blackhole::summarizeEmission(miller);
  EXPECT_NEAR(nearExtremal.gEmitMax, std::numbers::sqrt3, 2e-3);
  EXPECT_LT(nearExtremal.gEmitMin, 1.0e-5) << "the patch's twin leaves redshifted below dtau/dt";
  EXPECT_NEAR(nearExtremal.escapingFraction, 1.0 - 0.453, 0.01);
  EXPECT_GT(nearExtremal.nhekFraction, 0.9 * nearExtremal.escapingFraction);
}

/**
 * Schwarzschild check of the delay: dt/dr = 1/(1 - 2/r) integrates to
 * (r2 - r1) + 2 ln((r2 - 2)/(r1 - 2)) in M.
 */
TEST(ObserverSkyView, SignalDelayIsTheRadialNullIntegral) {
  const sky::ObserverKey key = requireKey(blackhole::observerKeyFor(1.0, 5.0, ObserverKind::Zamo));
  const blackhole::ObserverClockModel clock = blackhole::observerClockModel(key, 1.0);
  const double expectedM = (400.0 - 6.0) + (2.0 * std::log((400.0 - 2.0) / (6.0 - 2.0)));
  EXPECT_NEAR(blackhole::signalDelaySeconds(key, clock, 399.0) / clock.secondsPerM, expectedM,
              1e-9);
}

/**
 * The disclosure follows the live render spin: fresh desktop settings (0),
 * the Interstellar button (0.6, a float), the showcase-orbit recording
 * (0.62), and Thorne's 0.998 limit, which a two-digit format would print as 1.
 */
TEST(ObserverSkyView, SpinDisclosureNamesTheRenderSpinItShows) {
  const auto rs = std::make_unique<blackhole::RenderState>();
  const auto disclosure = [&rs](float spin) {
    rs->physicsCore.kerrSpin = spin;
    return ui::observerSpinDisclosure(*rs);
  };
  EXPECT_EQ(
      disclosure(0.0F),
      "physics spin 1-a = 1.33e-14 (this view); main render a = 0 (the film rendered a = 0.6)");
  EXPECT_EQ(disclosure(0.6F),
            "physics spin 1-a = 1.33e-14 (this view); main render a = 0.6 (film choice)");
  EXPECT_EQ(
      disclosure(0.62F),
      "physics spin 1-a = 1.33e-14 (this view); main render a = 0.62 (the film rendered a = 0.6)");
  EXPECT_EQ(
      disclosure(0.998F),
      "physics spin 1-a = 1.33e-14 (this view); main render a = 0.998 (the film rendered a = 0.6)");
}

/**
 * A static observer cannot exist inside the ergoregion, so Static at the
 * canon near-extremal ISCO has no key. invalidate() then leaves no resident
 * sky and reports the reason as the status message.
 */
TEST(ObserverSkyView, InvalidObserverReleasesTheSkyAndSaysWhy) {
  const double isco = ko::iscoOffset(blackhole::K_GARGANTUA_SPIN_DEFICIT, ko::OrbitSense::Prograde);
  EXPECT_FALSE(
      blackhole::observerKeyFor(blackhole::K_GARGANTUA_SPIN_DEFICIT, isco, ObserverKind::Static)
          .has_value());
  blackhole::ObserverSkyRenderer renderer;
  renderer.invalidate("no static observer here");
  EXPECT_EQ(renderer.status(), blackhole::ObserverSkyRenderer::Status::InvalidObserver);
  EXPECT_EQ(renderer.message(), "no static observer here");
  EXPECT_FALSE(renderer.lut().has_value());
  EXPECT_FALSE(renderer.ready());
  renderer.shutdown();
}

/**
 * A load that fails (here: no blackbody table) latches Failed for its key:
 * requesting the same key again starts nothing, and a different key does.
 */
TEST(ObserverSkyView, FailedBuildLatchesUntilTheKeyChanges) {
  using Status = blackhole::ObserverSkyRenderer::Status;
  const ScratchDirectory scratch;
  ASSERT_FALSE(scratch.path().empty()) << "no scratch directory";
  const sky::LutDimensions tiny{.width = 8, .height = 4, .tileRadial = 4, .tileAzimuth = 4};
  const std::filesystem::path missing = scratch.path() / "missing_blackbody.csv";
  const sky::ObserverKey first =
      requireKey(blackhole::observerKeyFor(1.0, 5.0, ObserverKind::Zamo));
  const sky::ObserverKey second =
      requireKey(blackhole::observerKeyFor(1.0, 6.0, ObserverKind::Zamo));
  blackhole::ObserverSkyRenderer renderer;
  renderer.request(first, tiny, scratch.path(), missing, 2.725);
  EXPECT_EQ(renderer.status(), Status::Building);
  EXPECT_EQ(settle(renderer), Status::Failed);
  EXPECT_NE(renderer.message().find("missing"), std::string::npos) << renderer.message();
  renderer.request(first, tiny, scratch.path(), missing, 2.725);
  EXPECT_EQ(renderer.status(), Status::Failed) << "a failed key restarted";
  renderer.request(second, tiny, scratch.path(), missing, 2.725);
  EXPECT_EQ(renderer.status(), Status::Building) << "a new key did not start";
  EXPECT_EQ(settle(renderer), Status::Failed);
  renderer.shutdown();
  EXPECT_EQ(renderer.status(), Status::Idle);
}

/**
 * Invalidating the observer mid-build stops the trace between rows: shutdown
 * returns in a fraction of the canon Miller build's tens of seconds, and the
 * stopped bundle never reaches the cache.
 */
TEST(ObserverSkyView, InvalidatingStopsTheBuildAndCachesNothing) {
  const ScratchDirectory scratch;
  ASSERT_FALSE(scratch.path().empty()) << "no scratch directory";
  blackhole::ObserverSkyRenderer renderer;
  const auto start = std::chrono::steady_clock::now();
  renderer.request(canonMiller(), sky::LutDimensions{}, scratch.path(),
                   "assets/luts/blackbody_cie_lut.csv", 2.725);
  // Let the worker reach the equirectangular rows before the stop.
  std::this_thread::sleep_for(std::chrono::milliseconds(300));
  renderer.invalidate("observer changed");
  renderer.shutdown();
  const double seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  EXPECT_LT(seconds, 10.0) << "shutdown waited for the whole build";
  std::error_code error;
  EXPECT_TRUE(std::filesystem::is_empty(scratch.path(), error)) << "a stopped build was cached";
}

} // namespace
