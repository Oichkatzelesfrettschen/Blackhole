/**
 * @file parallel_lut.h
 * @brief Parallel LUT generation using Taskflow.
 *
 * Provides parallel variants of LUT generation functions for improved
 * performance when generating multiple LUTs or large parameter sweeps.
 *
 * Usage:
 *   #if BLACKHOLE_ENABLE_TASKFLOW
 *   auto luts = physics::parallel::generateEmissivityLutSweep(...);
 *   #endif
 */

#ifndef PHYSICS_PARALLEL_LUT_H
#define PHYSICS_PARALLEL_LUT_H

#include "constants.h"
#include "kerr.h"
#include "lut.h"
#include "schwarzschild.h"
#include <algorithm>
#include <cstddef>
#include <vector>

#if BLACKHOLE_ENABLE_TASKFLOW
#include <taskflow/taskflow.hpp>
#endif

namespace physics::parallel {

/**
 * @brief Generate multiple emissivity LUTs for a sweep of spin values.
 *
 * Uses Taskflow to parallelize across spin values when available.
 *
 * @param size LUT resolution per table
 * @param massSolar Black hole mass in solar masses
 * @param spins Vector of spin values to generate LUTs for
 * @param mdotEdd Eddington accretion rate fraction
 * @param prograde Prograde orbit flag
 * @return Vector of LUTs, one per spin value
 */
inline std::vector<Lut1D> generateEmissivityLutSweep(
    int size,
    double massSolar,
    const std::vector<double>& spins,
    double mdotEdd,
    bool prograde = true) {

    std::vector<Lut1D> results(spins.size());

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(std::size_t{0}, spins.size(), std::size_t{1},
        [&](std::size_t i) {
            results.at(i) = generateEmissivityLut(size, massSolar, spins.at(i), mdotEdd, prograde);
        }
    );

    executor.run(taskflow).wait();
#else
    // Fallback to serial execution
    for (std::size_t i = 0; i < spins.size(); ++i) {
        results.at(i) = generateEmissivityLut(size, massSolar, spins.at(i), mdotEdd, prograde);
    }
#endif

    return results;
}

/**
 * @brief Generate multiple redshift LUTs for a sweep of spin values.
 *
 * @param size LUT resolution per table
 * @param massSolar Black hole mass in solar masses
 * @param spins Vector of spin values
 * @param theta Viewing angle in radians
 * @return Vector of LUTs
 */
inline std::vector<Lut1D> generateRedshiftLutSweep(
    int size,
    double massSolar,
    const std::vector<double>& spins,
    double theta = 0.5 * PI) {

    std::vector<Lut1D> results(spins.size());

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(std::size_t{0}, spins.size(), std::size_t{1},
        [&](std::size_t i) {
            results.at(i) = generateRedshiftLut(size, massSolar, spins.at(i), theta);
        }
    );

    executor.run(taskflow).wait();
#else
    for (std::size_t i = 0; i < spins.size(); ++i) {
        results.at(i) = generateRedshiftLut(size, massSolar, spins.at(i), theta);
    }
#endif

    return results;
}

/**
 * @brief Generate a batch of spin radii LUTs with parallel inner loop.
 *
 * Parallelizes the per-spin computation within generateSpinRadiiLut.
 *
 * @param size Number of spin samples
 * @param massSolar Black hole mass in solar masses
 * @param spinMin Minimum spin value (-0.99 to 0.99)
 * @param spinMax Maximum spin value (-0.99 to 0.99)
 * @return SpinRadiiLut with parallel-computed values
 */
inline SpinRadiiLut generateSpinRadiiLutParallel(
    int size,
    double massSolar,
    double spinMin = -0.99,
    double spinMax = 0.99) {

    SpinRadiiLut lut;
    if (size <= 1) {
        return lut;
    }

    spinMin = std::clamp(spinMin, -0.99, 0.99);
    spinMax = std::clamp(spinMax, -0.99, 0.99);
    if (spinMax <= spinMin) {
        spinMax = std::min(spinMin + 0.01, 0.99);
    }

    const double mass = massSolar * M_SUN;
    const double rS = schwarzschildRadius(mass);
    const double rG = G * mass / C2;

    lut.spins.resize(static_cast<std::size_t>(size));
    lut.rIscoOverRs.resize(static_cast<std::size_t>(size));
    lut.rPhOverRs.resize(static_cast<std::size_t>(size));

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(0, size, 1,
        [&](int i) {
            double u = static_cast<double>(i) / (size - 1);
            double spin = spinMin + u * (spinMax - spinMin);
            double a = spin * rG;
            bool prograde = spin >= 0.0;
            double rIsco = kerrIscoRadius(mass, a, prograde);
            double rPh = prograde ? kerrPhotonOrbitPrograde(mass, a)
                                   : kerrPhotonOrbitRetrograde(mass, a);

            lut.spins.at(static_cast<std::size_t>(i)) = static_cast<float>(spin);
            lut.rIscoOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rIsco / rS);
            lut.rPhOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rPh / rS);
        }
    );

    executor.run(taskflow).wait();
#else
    // Fallback to serial (same as generateSpinRadiiLut)
    for (int i = 0; i < size; ++i) {
      double const u = static_cast<double>(i) / (size - 1);
      double const spin = spinMin + (u * (spinMax - spinMin));
      double const a = spin * rG;
      bool const prograde = spin >= 0.0;
      double const rIsco = kerrIscoRadius(mass, a, prograde);
      double const rPh =
          prograde ? kerrPhotonOrbitPrograde(mass, a) : kerrPhotonOrbitRetrograde(mass, a);

      lut.spins.at(static_cast<std::size_t>(i)) = static_cast<float>(spin);
      lut.rIscoOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rIsco / rS);
      lut.rPhOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rPh / rS);
    }
#endif

    return lut;
}

/**
 * @brief Execute a batch of arbitrary tasks in parallel.
 *
 * Generic parallel execution for custom LUT generation patterns.
 *
 * @tparam F Callable type
 * @param tasks Vector of tasks to execute
 */
template <typename F>
inline void parallelExecute(const std::vector<F>& tasks) {
#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    for (const auto& task : tasks) {
        taskflow.emplace(task);
    }

    executor.run(taskflow).wait();
#else
    for (const auto& task : tasks) {
        task();
    }
#endif
}

/**
 * @brief Check if parallel execution is available.
 */
inline bool isAvailable() {
#if BLACKHOLE_ENABLE_TASKFLOW
    return true;
#else
    return false;
#endif
}

/**
 * @brief Get the number of worker threads available.
 */
inline unsigned int workerCount() {
#if BLACKHOLE_ENABLE_TASKFLOW
    return std::thread::hardware_concurrency();
#else
    return 1;
#endif
}

} // namespace physics::parallel

#endif // PHYSICS_PARALLEL_LUT_H
