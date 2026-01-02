/**
 * @file parallel_lut.h
 * @brief Parallel LUT generation using Taskflow.
 *
 * Provides parallel variants of LUT generation functions for improved
 * performance when generating multiple LUTs or large parameter sweeps.
 *
 * Usage:
 *   #if BLACKHOLE_ENABLE_TASKFLOW
 *   auto luts = physics::parallel::generate_emissivity_lut_sweep(...);
 *   #endif
 */

#ifndef PHYSICS_PARALLEL_LUT_H
#define PHYSICS_PARALLEL_LUT_H

#include "lut.h"
#include <functional>
#include <vector>

#if BLACKHOLE_ENABLE_TASKFLOW
#include <taskflow/taskflow.hpp>
#endif

namespace physics {
namespace parallel {

/**
 * @brief Generate multiple emissivity LUTs for a sweep of spin values.
 *
 * Uses Taskflow to parallelize across spin values when available.
 *
 * @param size LUT resolution per table
 * @param mass_solar Black hole mass in solar masses
 * @param spins Vector of spin values to generate LUTs for
 * @param mdot_edd Eddington accretion rate fraction
 * @param prograde Prograde orbit flag
 * @return Vector of LUTs, one per spin value
 */
inline std::vector<Lut1D> generate_emissivity_lut_sweep(
    int size,
    double mass_solar,
    const std::vector<double>& spins,
    double mdot_edd,
    bool prograde = true) {

    std::vector<Lut1D> results(spins.size());

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(std::size_t{0}, spins.size(), std::size_t{1},
        [&](std::size_t i) {
            results[i] = generate_emissivity_lut(size, mass_solar, spins[i], mdot_edd, prograde);
        }
    );

    executor.run(taskflow).wait();
#else
    // Fallback to serial execution
    for (std::size_t i = 0; i < spins.size(); ++i) {
        results[i] = generate_emissivity_lut(size, mass_solar, spins[i], mdot_edd, prograde);
    }
#endif

    return results;
}

/**
 * @brief Generate multiple redshift LUTs for a sweep of spin values.
 *
 * @param size LUT resolution per table
 * @param mass_solar Black hole mass in solar masses
 * @param spins Vector of spin values
 * @param theta Viewing angle in radians
 * @return Vector of LUTs
 */
inline std::vector<Lut1D> generate_redshift_lut_sweep(
    int size,
    double mass_solar,
    const std::vector<double>& spins,
    double theta = 0.5 * PI) {

    std::vector<Lut1D> results(spins.size());

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(std::size_t{0}, spins.size(), std::size_t{1},
        [&](std::size_t i) {
            results[i] = generate_redshift_lut(size, mass_solar, spins[i], theta);
        }
    );

    executor.run(taskflow).wait();
#else
    for (std::size_t i = 0; i < spins.size(); ++i) {
        results[i] = generate_redshift_lut(size, mass_solar, spins[i], theta);
    }
#endif

    return results;
}

/**
 * @brief Generate a batch of spin radii LUTs with parallel inner loop.
 *
 * Parallelizes the per-spin computation within generate_spin_radii_lut.
 *
 * @param size Number of spin samples
 * @param mass_solar Black hole mass in solar masses
 * @param spin_min Minimum spin value (-0.99 to 0.99)
 * @param spin_max Maximum spin value (-0.99 to 0.99)
 * @return SpinRadiiLut with parallel-computed values
 */
inline SpinRadiiLut generate_spin_radii_lut_parallel(
    int size,
    double mass_solar,
    double spin_min = -0.99,
    double spin_max = 0.99) {

    SpinRadiiLut lut;
    if (size <= 1) {
        return lut;
    }

    spin_min = std::clamp(spin_min, -0.99, 0.99);
    spin_max = std::clamp(spin_max, -0.99, 0.99);
    if (spin_max <= spin_min) {
        spin_max = std::min(spin_min + 0.01, 0.99);
    }

    const double mass = mass_solar * M_SUN;
    const double r_s = schwarzschild_radius(mass);
    const double r_g = G * mass / C2;

    lut.spins.resize(static_cast<std::size_t>(size));
    lut.r_isco_over_rs.resize(static_cast<std::size_t>(size));
    lut.r_ph_over_rs.resize(static_cast<std::size_t>(size));

#if BLACKHOLE_ENABLE_TASKFLOW
    tf::Executor executor;
    tf::Taskflow taskflow;

    taskflow.for_each_index(0, size, 1,
        [&](int i) {
            double u = static_cast<double>(i) / (size - 1);
            double spin = spin_min + u * (spin_max - spin_min);
            double a = spin * r_g;
            bool prograde = spin >= 0.0;
            double r_isco = kerr_isco_radius(mass, a, prograde);
            double r_ph = prograde ? kerr_photon_orbit_prograde(mass, a)
                                   : kerr_photon_orbit_retrograde(mass, a);

            lut.spins[static_cast<std::size_t>(i)] = static_cast<float>(spin);
            lut.r_isco_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_isco / r_s);
            lut.r_ph_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_ph / r_s);
        }
    );

    executor.run(taskflow).wait();
#else
    // Fallback to serial (same as generate_spin_radii_lut)
    for (int i = 0; i < size; ++i) {
        double u = static_cast<double>(i) / (size - 1);
        double spin = spin_min + u * (spin_max - spin_min);
        double a = spin * r_g;
        bool prograde = spin >= 0.0;
        double r_isco = kerr_isco_radius(mass, a, prograde);
        double r_ph = prograde ? kerr_photon_orbit_prograde(mass, a)
                               : kerr_photon_orbit_retrograde(mass, a);

        lut.spins[static_cast<std::size_t>(i)] = static_cast<float>(spin);
        lut.r_isco_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_isco / r_s);
        lut.r_ph_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_ph / r_s);
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
inline void parallel_execute(const std::vector<F>& tasks) {
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

} // namespace parallel
} // namespace physics

#endif // PHYSICS_PARALLEL_LUT_H
