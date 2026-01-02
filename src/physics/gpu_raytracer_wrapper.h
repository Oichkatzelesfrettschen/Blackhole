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

#include "gpu_raytracer_kernel.hpp"
#include "verified/kerr.hpp"
#include <vector>
#include <cstddef>

namespace physics {
namespace gpu {

/**
 * @brief GPU-friendly ray batch with aligned memory layout
 *
 * Manages batch of rays in Structure-of-Arrays layout for optimal GPU memory access.
 * Can be transferred to GPU device memory via CUDA/HIP memcpy or used for CPU testing.
 */
struct GPURayBatch {
    std::vector<GPUGeodesicState> rays;
    std::vector<int> ray_ids;      ///< Original ray IDs for output mapping
    std::vector<float> energies;   ///< Conserved energy per ray
    std::vector<float> angular_momentum;  ///< Conserved L per ray

    explicit GPURayBatch(std::size_t batch_size = KernelConfig::BLOCK_SIZE)
        : rays(batch_size), ray_ids(batch_size),
          energies(batch_size), angular_momentum(batch_size) {}

    [[nodiscard]] std::size_t size() const { return rays.size(); }
};

/**
 * @brief Convert batch ray state to GPU format
 *
 * @param rays Input rays (verified::StateVector format)
 * @param M Black hole mass
 * @param a Spin parameter
 * @param scale Coordinate scale factor (default 1.0 for geometric units)
 * @return GPU-formatted rays with conserved quantities pre-computed
 */
[[nodiscard]] inline GPURayBatch prepare_ray_batch(
    const std::vector<verified::StateVector>& rays,
    double M, double a,
    double scale = 1.0) noexcept {

    GPURayBatch batch(rays.size());

    // Metric computation function for energy/angular momentum
    auto compute_metric = [M, a](const verified::StateVector& state,
                                  double, double) -> verified::MetricComponents {
        const double Sigma = verified::kerr_Sigma(state.x1, state.x2, a);
        const double Delta = verified::kerr_Delta(state.x1, M, a);
        const double A = verified::kerr_A(state.x1, state.x2, M, a);

        return verified::MetricComponents{
            verified::kerr_g_tt(state.x1, state.x2, M, a),
            verified::kerr_g_rr(state.x1, state.x2, M, a),
            Sigma,
            A / Sigma,
            verified::frame_dragging_omega(state.x1, state.x2, M, a) * A / Sigma
        };
    };

    // Convert each ray and compute conserved quantities
    for (std::size_t i = 0; i < rays.size(); ++i) {
        batch.rays[i] = GPUGeodesicState::from_verified(rays[i], scale);
        batch.ray_ids[i] = static_cast<int>(i);

        // Pre-compute conserved quantities
        const auto g = compute_metric(rays[i], M, a);
        batch.energies[i] = static_cast<float>(
            verified::compute_energy(g, rays[i])
        );
        batch.angular_momentum[i] = static_cast<float>(
            verified::compute_angular_momentum(g, rays[i])
        );
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
 * @param M Black hole mass
 * @param a Spin parameter
 * @param h Integration step size
 * @param max_steps Maximum iterations
 * @param out_states Output states after integration
 * @return Number of successfully integrated rays
 */
inline int trace_batch_cpu(
    const GPURayBatch& batch,
    double M, double a,
    double h, int max_steps,
    std::vector<verified::StateVector>& out_states) noexcept {

    // Convert GPU states back to verified format for RK4 integration
    std::vector<verified::StateVector> rays_verified;
    for (const auto& gpu_ray : batch.rays) {
        rays_verified.push_back(gpu_ray.to_verified(0.0, 1.0));
    }

    // Call GPU batch integrator (CPU-friendly version)
    out_states.resize(rays_verified.size());
    int successful = gpu_batch_integrate_geodesics(
        rays_verified, out_states, M, a, h, max_steps, 1e-8
    );

    return successful;
}

}  // namespace gpu
}  // namespace physics

#endif  // PHYSICS_GPU_RAYTRACER_WRAPPER_H
