/**
 * @file bridge_integrator.h
 * @brief Integrator the Blender bridge's CUDA renderer selects.
 *
 * The Kerr Mino-time integrator is exact at a = 0 (Schwarzschild is the
 * a = 0 member of the family), and the desktop lane runs it at every spin
 * (blackhole::bindCudaLaunchParams sets kerr_enabled = 1). A spin-gated
 * switch to the Schwarzschild RK4 lane would make a bridge render jump at
 * zero spin, so the bridge selects the Mino integrator at every spin too;
 * BLACKHOLE_BRIDGE_KERR_ENABLED=0 keeps the RK4 lane reachable for tests.
 *
 * Plain host code so that cuda_renderer.cu, compiled by nvcc as C++17, and
 * the host tests share one definition.
 */

#ifndef BLACKHOLE_BLENDER_BRIDGE_INTEGRATOR_H
#define BLACKHOLE_BLENDER_BRIDGE_INTEGRATOR_H

namespace bridge {

/**
 * @brief BH_LaunchParams::kerr_enabled for a bridge launch.
 *
 * @param spin     Dimensionless spin a* of the launch (any value, including 0)
 * @param override Value of BLACKHOLE_BRIDGE_KERR_ENABLED as env_flag reads it
 *                 (1 when unset)
 * @return 1 (Mino integrator) unless the override selects the RK4 lane
 */
[[nodiscard]] inline int kerrIntegratorFlag(float spin, int override) noexcept {
  static_cast<void>(spin);
  return override != 0 ? 1 : 0;
}

} // namespace bridge

#endif // BLACKHOLE_BLENDER_BRIDGE_INTEGRATOR_H
