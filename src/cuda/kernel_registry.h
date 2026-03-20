/*
 * kernel_registry.h
 * Kernel variant metadata and auto-selection.
 *
 * Following YSU-engine lbm_kernels.h pattern: enum-based variant selection
 * with metadata table (name, min_sm, tpb, estimated_registers).
 */

#ifndef BLACKHOLE_CUDA_KERNEL_REGISTRY_H
#define BLACKHOLE_CUDA_KERNEL_REGISTRY_H

#include "kernel_launch.h"

struct RtKernelInfo {
    const char* name;
    int min_sm;             /* Minimum SM version (e.g. 80 = SM8.0) */
    int rays_per_thread;
    int tpb;                /* Threads per block */
    int estimated_registers;/* Conservative register estimate per thread */
};

/* Metadata table indexed by BH_KernelVariant */
extern const RtKernelInfo RT_KERNEL_INFO[BH_KERNEL_COUNT];

/* Select the best variant for the current device.
 * Queries cudaDeviceGetAttribute for SM version and register limits. */
int registry_select_variant(void);

/* Get info for a given variant. */
const RtKernelInfo* registry_get_info(int variant);

#endif /* BLACKHOLE_CUDA_KERNEL_REGISTRY_H */
