#include <chrono>
#include <cmath>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>

#include "physics/constants.h"
#include "physics/kerr.h"
#include "physics/lut.h"
#include "physics/raytracer.h"
#include "physics/schwarzschild.h"

struct BenchConfig {
  int rays = 2000;
  int steps = 2000;
  int iterations = 5;
  int warmup = 1;
  int lutSize = 256;
  double spin = 0.0;
  double massSolar = 4.0e6;
  double mdotEdd = 0.1;
  std::string jsonPath;
  std::string csvPath;
};

static BenchConfig parseArgs(int argc, char **argv) {
  BenchConfig cfg;
  for (int i = 1; i < argc; ++i) {
    if (std::strcmp(argv[i], "--rays") == 0 && i + 1 < argc) {
      cfg.rays = std::stoi(argv[++i]);
    } else if (std::strcmp(argv[i], "--steps") == 0 && i + 1 < argc) {
      cfg.steps = std::stoi(argv[++i]);
    } else if (std::strcmp(argv[i], "--iterations") == 0 && i + 1 < argc) {
      cfg.iterations = std::stoi(argv[++i]);
    } else if (std::strcmp(argv[i], "--lut-size") == 0 && i + 1 < argc) {
      cfg.lutSize = std::stoi(argv[++i]);
    } else if (std::strcmp(argv[i], "--spin") == 0 && i + 1 < argc) {
      cfg.spin = std::stod(argv[++i]);
    } else if (std::strcmp(argv[i], "--mass-solar") == 0 && i + 1 < argc) {
      cfg.massSolar = std::stod(argv[++i]);
    } else if (std::strcmp(argv[i], "--mdot") == 0 && i + 1 < argc) {
      cfg.mdotEdd = std::stod(argv[++i]);
    } else if (std::strcmp(argv[i], "--warmup") == 0 && i + 1 < argc) {
      cfg.warmup = std::stoi(argv[++i]);
    } else if (std::strcmp(argv[i], "--json") == 0 && i + 1 < argc) {
      cfg.jsonPath = argv[++i];
    } else if (std::strcmp(argv[i], "--csv") == 0 && i + 1 < argc) {
      cfg.csvPath = argv[++i];
    }
  }
  cfg.rays = std::max(cfg.rays, 1);
  cfg.steps = std::max(cfg.steps, 1);
  cfg.iterations = std::max(cfg.iterations, 1);
  cfg.warmup = std::max(cfg.warmup, 0);
  cfg.lutSize = std::max(cfg.lutSize, 8);
  cfg.spin = std::clamp(cfg.spin, -0.99, 0.99);
  return cfg;
}

struct BenchResult {
  std::string name;
  double avgMs = 0.0;
  double minMs = 0.0;
  double maxMs = 0.0;
  double workUnits = 0.0;
  double unitsPerSec = 0.0;
  int iterations = 0;
};

template <typename Fn>
static BenchResult runBench(const std::string &label, int iterations, int warmup,
                            double workUnits, Fn fn) {
  using clock = std::chrono::high_resolution_clock;
  for (int i = 0; i < warmup; ++i) {
    fn();
  }
  double minMs = std::numeric_limits<double>::max();
  double maxMs = 0.0;
  double totalMs = 0.0;

  for (int i = 0; i < iterations; ++i) {
    auto start = clock::now();
    fn();
    auto end = clock::now();
    double ms = std::chrono::duration<double, std::milli>(end - start).count();
    minMs = std::min(minMs, ms);
    maxMs = std::max(maxMs, ms);
    totalMs += ms;
  }

  double avgMs = totalMs / static_cast<double>(iterations);
  double unitsPerSec = avgMs > 0.0 ? workUnits / (avgMs / 1000.0) : 0.0;
  std::cout << std::fixed << std::setprecision(3);
  std::cout << label << " avg=" << avgMs << " ms"
            << " (min=" << minMs << ", max=" << maxMs << ")"
            << " units/s=" << unitsPerSec << "\n";
  BenchResult result;
  result.name = label;
  result.avgMs = avgMs;
  result.minMs = minMs;
  result.maxMs = maxMs;
  result.workUnits = workUnits;
  result.unitsPerSec = unitsPerSec;
  result.iterations = iterations;
  return result;
}

static void writeCsv(const std::string &path, const BenchConfig &cfg,
                     const std::vector<BenchResult> &results, double accum) {
  std::ofstream out(path);
  if (!out) {
    std::cerr << "Failed to write CSV: " << path << "\n";
    return;
  }
  out << "name,avg_ms,min_ms,max_ms,work_units,units_per_sec,iterations,rays,steps,lut_size,spin,"
         "mass_solar,mdot,accum\n";
  out << std::fixed << std::setprecision(6);
  for (const auto &result : results) {
    out << result.name << "," << result.avgMs << "," << result.minMs << "," << result.maxMs << ","
        << result.workUnits << "," << result.unitsPerSec << "," << result.iterations << ","
        << cfg.rays << "," << cfg.steps << "," << cfg.lutSize << "," << cfg.spin << ","
        << cfg.massSolar << "," << cfg.mdotEdd << "," << accum << "\n";
  }
}

static void writeJson(const std::string &path, const BenchConfig &cfg,
                      const std::vector<BenchResult> &results, double accum) {
  std::ofstream out(path);
  if (!out) {
    std::cerr << "Failed to write JSON: " << path << "\n";
    return;
  }
  out << std::fixed << std::setprecision(6);
  out << "{\n";
  out << "  \"config\": {\n";
  out << "    \"rays\": " << cfg.rays << ",\n";
  out << "    \"steps\": " << cfg.steps << ",\n";
  out << "    \"iterations\": " << cfg.iterations << ",\n";
  out << "    \"warmup\": " << cfg.warmup << ",\n";
  out << "    \"lut_size\": " << cfg.lutSize << ",\n";
  out << "    \"spin\": " << cfg.spin << ",\n";
  out << "    \"mass_solar\": " << cfg.massSolar << ",\n";
  out << "    \"mdot\": " << cfg.mdotEdd << "\n";
  out << "  },\n";
  out << "  \"results\": [\n";
  for (size_t i = 0; i < results.size(); ++i) {
    const auto &result = results[i];
  out << "    {\n";
  out << "      \"name\": \"" << result.name << "\",\n";
  out << "      \"avg_ms\": " << result.avgMs << ",\n";
  out << "      \"min_ms\": " << result.minMs << ",\n";
  out << "      \"max_ms\": " << result.maxMs << ",\n";
  out << "      \"work_units\": " << result.workUnits << ",\n";
  out << "      \"units_per_sec\": " << result.unitsPerSec << ",\n";
  out << "      \"iterations\": " << result.iterations << "\n";
  out << "    }" << (i + 1 < results.size() ? "," : "") << "\n";
  }
  out << "  ],\n";
  out << "  \"accumulator\": " << accum << "\n";
  out << "}\n";
}

int main(int argc, char **argv) {
  BenchConfig cfg = parseArgs(argc, argv);

  std::cout << "=== Blackhole Physics Bench ===\n";
  std::cout << "rays=" << cfg.rays << " steps=" << cfg.steps
            << " iterations=" << cfg.iterations << " warmup=" << cfg.warmup
            << " lutSize=" << cfg.lutSize << " spin=" << cfg.spin
            << " massSolar=" << cfg.massSolar
            << " mdot=" << cfg.mdotEdd << "\n\n";

  double accum = 0.0;
  std::vector<BenchResult> results;

  results.push_back(runBench("Schwarzschild raytracer", cfg.iterations, cfg.warmup,
                             static_cast<double>(cfg.rays), [&]() {
    const double mass = cfg.massSolar * physics::M_SUN;
    const double r_s = physics::schwarzschild_radius(mass);
    physics::SchwarzschildRaytracer tracer(mass);
    tracer.set_step_size(0.02 * r_s);
    tracer.set_max_steps(cfg.steps);

    for (int i = 0; i < cfg.rays; ++i) {
      double angle = (static_cast<double>(i) / cfg.rays) * (physics::PI * 0.9);
      physics::PhotonRay ray{};
      ray.position = {30.0 * r_s, physics::PI * 0.5, 0.0};
      ray.direction = {std::cos(angle), std::sin(angle), 0.0};
      ray.frequency = 1.0;
      ray.status = physics::RayStatus::PROPAGATING;
      ray.energy = 1.0;
      ray.angular_momentum = 0.0;
      ray.carter_constant = 0.0;

      auto result = tracer.trace(ray);
      accum += result.total_distance + result.redshift + result.steps_taken;
    }
  }));

  results.push_back(runBench("Kerr potential eval", cfg.iterations, cfg.warmup,
                             static_cast<double>(cfg.rays * 10), [&]() {
    const double mass = cfg.massSolar * physics::M_SUN;
    const double r_g = physics::G * mass / physics::C2;
    const double a = cfg.spin * r_g;
    physics::KerrGeodesicConsts c{1.0, 2.0, 3.0};

    for (int i = 0; i < cfg.rays * 10; ++i) {
      double u = static_cast<double>(i) / (cfg.rays * 10);
      double r = (6.0 + 20.0 * u) * r_g;
      double theta = physics::PI * (0.25 + 0.5 * u);
      auto p = physics::kerr_potentials(r, theta, mass, a, c);
      accum += p.R + p.Theta + p.dRdr + p.dThetadtheta;
    }
  }));

  results.push_back(runBench("Kerr raytracer (mino)", cfg.iterations, cfg.warmup,
                             static_cast<double>(cfg.rays), [&]() {
    const double mass = cfg.massSolar * physics::M_SUN;
    const double r_s = physics::schwarzschild_radius(mass);
    const double r_g = physics::G * mass / physics::C2;
    const double a = cfg.spin * r_g;

    physics::KerrRaytracer tracer(mass, a);
    tracer.set_step_size(0.02 * r_s);
    tracer.set_max_steps(cfg.steps);

    double impact = 3.0 * std::sqrt(3.0) * r_g;
    auto c = physics::kerr_equatorial_consts(impact, 1.0);

    for (int i = 0; i < cfg.rays; ++i) {
      double phi = (static_cast<double>(i) / cfg.rays) * physics::TWO_PI;
      auto state = physics::kerr_equatorial_state(12.0 * r_s, phi, -1.0);
      auto result = tracer.trace(state, c);
      accum += result.total_distance + result.redshift + result.steps_taken;
    }
  }));

  results.push_back(runBench("LUT generation", cfg.iterations, cfg.warmup,
                             static_cast<double>(cfg.lutSize), [&]() {
    auto emissivity = physics::generate_emissivity_lut(cfg.lutSize, cfg.massSolar, cfg.spin,
                                                       cfg.mdotEdd, true);
    auto redshift = physics::generate_redshift_lut(cfg.lutSize, cfg.massSolar, cfg.spin);
    for (float v : emissivity.values) {
      accum += static_cast<double>(v);
    }
    for (float v : redshift.values) {
      accum += static_cast<double>(v);
    }
  }));

  std::cout << "\nAccumulator: " << std::setprecision(6) << accum << "\n";

  if (!cfg.csvPath.empty()) {
    writeCsv(cfg.csvPath, cfg, results, accum);
  }
  if (!cfg.jsonPath.empty()) {
    writeJson(cfg.jsonPath, cfg, results, accum);
  }
  return 0;
}
