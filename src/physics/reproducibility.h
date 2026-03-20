/**
 * @file reproducibility.h
 * @brief Reproducibility manifest for scientific output.
 *
 * WHY: Scientific results must be reproducible. Every output file
 * (FITS, HDF5, image) should record exactly how it was generated:
 * code version, build parameters, physics settings, and RNG seeds.
 *
 * WHAT: Collects build-time and runtime metadata into a manifest
 * that can be written as FITS header keywords, HDF5 attributes,
 * or JSON sidecar files.
 *
 * HOW: Call buildManifest() to get compile-time info. Add runtime
 * parameters before writing to output.
 */

#ifndef PHYSICS_REPRODUCIBILITY_H
#define PHYSICS_REPRODUCIBILITY_H

#include <ctime>
#include <iomanip>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace physics {

/**
 * @brief Key-value pair for manifest entries.
 */
using ManifestEntry = std::pair<std::string, std::string>;

/**
 * @brief Reproducibility manifest.
 *
 * Collects all metadata needed to reproduce a simulation output.
 */
struct ReproducibilityManifest {
  std::vector<ManifestEntry> entries;

  void add(const std::string& key, const std::string& value) {
    entries.emplace_back(key, value);
  }

  void add(const std::string& key, double value) {
    std::ostringstream oss;
    oss << std::setprecision(15) << value;
    entries.emplace_back(key, oss.str());
  }

  void add(const std::string& key, int value) {
    entries.emplace_back(key, std::to_string(value));
  }

  [[nodiscard]] std::string get(const std::string& key) const {
    for (const auto& [k, v] : entries) {
      if (k == key) { return v; }
    }
    return "";
  }

  /**
   * @brief Serialize manifest to JSON string.
   */
  [[nodiscard]] std::string toJson() const {
    std::ostringstream oss;
    oss << "{\n";
    for (std::size_t i = 0; i < entries.size(); ++i) {
      oss << "  \"" << entries.at(i).first << "\": \""
          << entries.at(i).second << "\"";
      if (i + 1 < entries.size()) { oss << ","; }
      oss << "\n";
    }
    oss << "}";
    return oss.str();
  }
};

/**
 * @brief Build-time manifest with compiler and standard info.
 *
 * Captures compile-time information that cannot change at runtime.
 */
inline ReproducibilityManifest buildManifest() {
  ReproducibilityManifest m;

  m.add("code", "Blackhole");

#ifdef BLACKHOLE_VERSION
  m.add("version", BLACKHOLE_VERSION);
#else
  m.add("version", "dev");
#endif

  // Compiler identification
#ifdef __clang__
  m.add("compiler", "Clang " + std::to_string(__clang_major__) + "." +
        std::to_string(__clang_minor__) + "." +
        std::to_string(__clang_patchlevel__));
#elifdef __GNUC__
  m.add("compiler", "GCC " + std::to_string(__GNUC__) + "." +
        std::to_string(__GNUC_MINOR__) + "." +
        std::to_string(__GNUC_PATCHLEVEL__));
#else
  m.add("compiler", "unknown");
#endif

  // C++ standard
#ifdef BLACKHOLE_CXX_STANDARD
  m.add("cxx_standard", std::to_string(BLACKHOLE_CXX_STANDARD));
#else
  m.add("cxx_standard", std::to_string(__cplusplus));
#endif

  // Build type
#ifdef NDEBUG
  m.add("build_type", "Release");
#else
  m.add("build_type", "Debug");
#endif

  // Platform
#ifdef __linux__
  m.add("platform", "Linux");
#elifdef __APPLE__
  m.add("platform", "macOS");
#elifdef _WIN32
  m.add("platform", "Windows");
#else
  m.add("platform", "unknown");
#endif

  // SIMD tier
#ifdef __AVX512F__
  m.add("simd", "AVX-512");
#elifdef __AVX2__
  m.add("simd", "AVX2");
#elifdef __AVX__
  m.add("simd", "AVX");
#elifdef __SSE4_2__
  m.add("simd", "SSE4.2");
#else
  m.add("simd", "SSE2");
#endif

  // Timestamp
  auto t = std::time(nullptr);
  // NOLINTNEXTLINE(concurrency-mt-unsafe)
  // WHY: gmtime is not thread-safe on POSIX but this manifest function is
  // intended to be called once at startup before worker threads launch.
  auto tm = *std::gmtime(&t);
  std::ostringstream ts;
  ts << std::put_time(&tm, "%Y-%m-%dT%H:%M:%SZ");
  m.add("build_time", ts.str());

  return m;
}

/**
 * @brief Add physics simulation parameters to a manifest.
 *
 * @param m Manifest to populate
 * @param massMsun Black hole mass [Msun]
 * @param spin Dimensionless spin a*
 * @param inclinationDeg Observer inclination [degrees]
 * @param freqHz Observing frequency [Hz]
 * @param nx Image width [pixels]
 * @param ny Image height [pixels]
 * @param fovUas Field of view [microarcseconds]
 */
inline void addPhysicsParams(ReproducibilityManifest& m,
                              double massMsun, double spin,
                              double inclinationDeg,
                              double freqHz,
                              int nx, int ny,
                              double fovUas) {
  m.add("bh_mass_msun", massMsun);
  m.add("bh_spin", spin);
  m.add("inclination_deg", inclinationDeg);
  m.add("freq_hz", freqHz);
  m.add("image_nx", nx);
  m.add("image_ny", ny);
  m.add("fov_uas", fovUas);
}

} // namespace physics

#endif // PHYSICS_REPRODUCIBILITY_H
