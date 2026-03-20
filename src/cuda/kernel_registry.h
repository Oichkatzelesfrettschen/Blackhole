/**
 * @file kernel_registry.h
 * @brief Kernel variant metadata table and auto-selection interface.
 *
 * Following the YSU-engine lbm_kernels.h pattern: an enum-indexed metadata
 * table (name, min_sm, tpb, estimated_registers) drives automatic variant
 * selection based on the current device's SM version and register budget.
 */

#ifndef BLACKHOLE_CUDA_KERNEL_REGISTRY_H
#define BLACKHOLE_CUDA_KERNEL_REGISTRY_H

#include "kernel_launch.h"

/* NOLINTBEGIN(readability-identifier-naming)
 * WHY: Member names follow YSU-engine physics kernel registry conventions
 * (snake_case). These are shared across C++17 CUDA TUs; renaming to camelCase
 * would break parity with YSU-engine's lbm_kernels.h reference patterns. */
/**
 * @brief Per-variant metadata used for device capability gating and occupancy estimation.
 *
 * Fields follow YSU-engine physics kernel registry conventions (snake_case).
 */
struct RtKernelInfo {
  const char *name;        /**< @brief Human-readable variant name for logging. */
  int min_sm;              /**< @brief Minimum SM version required (e.g. 80 = SM8.0). */
  int rays_per_thread;     /**< @brief Number of rays each thread processes. */
  int tpb;                 /**< @brief Threads per block for this variant. */
  int estimated_registers; /**< @brief Conservative per-thread register estimate from ptxas. */
};
// NOLINTEND(readability-identifier-naming)

/** @brief Metadata table indexed by BH_KernelVariant. */
// NOLINTNEXTLINE(readability-identifier-naming,bugprone-dynamic-static-initializers)
extern const RtKernelInfo RT_KERNEL_INFO[BH_KERNEL_COUNT];

/**
 * @brief Select the best kernel variant for the current CUDA device.
 *
 * Queries cudaDeviceGetAttribute for SM version and per-SM register file size,
 * then walks variants from most to least capable, returning the first that
 * achieves at least 2 concurrent blocks per SM.
 *
 * @return BH_KernelVariant index, or BH_KERNEL_FP32_BASELINE on any error.
 */
// NOLINTNEXTLINE(readability-identifier-naming)
int registry_select_variant();

/**
 * @brief Get the metadata record for a given variant index.
 *
 * @param variant BH_KernelVariant index.
 * @return Pointer to the corresponding RtKernelInfo, or nullptr if out of range.
 */
// NOLINTNEXTLINE(readability-identifier-naming)
const RtKernelInfo *registry_get_info(int variant);

#endif /* BLACKHOLE_CUDA_KERNEL_REGISTRY_H */
