/**
 * @file gpu_raytracer_wrapper.h
 * @brief GPU ray-tracer wrapper for integration with batch.h
 *
 * Provides convenience functions to integrate GPU ray-tracing kernels
 * with the existing physics::batch system.
 *
 * Architecture:
 * - Thin wrapper around physics::gpu kernels from gpu_raytracer_kernel.hpp
 * - Interfaces with batch.h BatchRayResult and state management
 * - Compatible with both CPU and GPU execution paths
 * - Memory management via standard vectors (CPU-friendly) or device memory (GPU)
 */

#ifndef PHYSICS_GPU_RAYTRACER_WRAPPER_H
#define PHYSICS_GPU_RAYTRACER_WRAPPER_H

#include <cstddef>
#include <vector>

#include "gpu_raytracer_kernel.hpp"
#include "verified/energy_conserving_geodesic.hpp"
#include "verified/geodesic.hpp"
#include "verified/kerr.hpp"
#include "verified/rk4.hpp"

namespace physics::gpu {

/**
 * @brief GPU-friendly ray batch with aligned memory layout
 *
 * Manages batch of rays in Structure-of-Arrays layout for optimal GPU memory access.
 * Can be transferred to GPU device memory via CUDA/HIP memcpy or used for CPU testing.
 */
struct GPURayBatch {
    std::vector<GPUGeodesicState> rays;
    std::vector<int> rayIds;       ///< Original ray IDs for output mapping
    std::vector<float> energies;   ///< Conserved energy per ray
    std::vector<float> angularMomentum; ///< Conserved L per ray

    explicit GPURayBatch(std::size_t batchSize = KernelConfig::BLOCK_SIZE)
        : rays(batchSize), rayIds(batchSize), energies(batchSize), angularMomentum(batchSize) {}

    [[nodiscard]] std::size_t size() const { return rays.size(); }
};

/**
 * @brief Convert batch ray state to GPU format
 *
 * @param rays Input rays (verified::StateVector format)
 * @param m Black hole mass
 * @param a Spin parameter
 * @param scale Coordinate scale factor (default 1.0 for geometric units)
 * @return GPU-formatted rays with conserved quantities pre-computed
 */
[[nodiscard]] inline GPURayBatch prepareRayBatch(const std::vector<verified::StateVector> &rays,
                                                 double m, double a, double scale = 1.0) noexcept {

  GPURayBatch batch(rays.size());

  // Metric computation function for energy/angular momentum
  auto computeMetric = [m, a](const verified::StateVector &state, double,
                              double) -> verified::MetricComponents {
    const double sigma = verified::kerr_Sigma(state.x1, state.x2, a);
    const double delta = verified::kerr_Delta(state.x1, m, a);
    const double a = verified::kerr_A(state.x1, state.x2, m, a);

    return verified::MetricComponents{
        verified::kerr_g_tt(state.x1, state.x2, m, a),
        verified::kerr_g_rr(state.x1, state.x2, m, a), sigma, a / sigma,
        verified::frame_dragging_omega(state.x1, state.x2, m, a) * a / sigma};
  };

  // Convert each ray and compute conserved quantities
  for (std::size_t i = 0; i < rays.size(); ++i) {
    batch.rays.at(i) = GPUGeodesicState::from_verified(rays.at(i), scale);
    batch.rayIds.at(i) = static_cast<int>(i);

    // Pre-compute conserved quantities
    const auto g = computeMetric(rays.at(i), m, a);
    batch.energies.at(i) = static_cast<float>(verified::compute_energy(g, rays.at(i)));
    batch.angularMomentum.at(i) = static_cast<float>(verified::compute_angular_momentum(g, rays.at(i)));
  }

  return batch;
}

/**
 * @brief Trace rays in batch mode (CPU implementation)
 *
 * GPU implementation would replace this with __global__ kernel launch.
 * This version uses CPU-friendly loop for validation and testing.
 *
 * @param batch Input rays
 * @param m Black hole mass
 * @param a Spin parameter
 * @param h Integration step size
 * @param maxSteps Maximum iterations
 * @param outStates Output states after integration
 * @return Number of successfully integrated rays
 */
inline int traceBatchCpu(const GPURayBatch &batch, double m, double a, double h, int maxSteps,
                         std::vector<verified::StateVector> &outStates) noexcept {

  // Convert GPU states back to verified format for RK4 integration
  std::vector<verified::StateVector> raysVerified;
  rays_verified.reserve(batch.rays.size());
  for (const auto &gpuRay : batch.rays) {
    raysVerified.push_back(gpuRay.to_verified(0.0, 1.0));
  }

  // Call GPU batch integrator (CPU-friendly version)
  outStates.resize(raysVerified.size());
  int const successful =
      gpu_batch_integrate_geodesics(raysVerified, outStates, m, a, h, maxSteps, 1e-8);

  return successful;
}

} // namespace physics::gpu

#endif  // PHYSICS_GPU_RAYTRACER_WRAPPER_H
