/*
 * kernel_registry.cu
 * Kernel variant metadata table and auto-selection logic.
 *
 * Following YSU-engine lbm_kernels.h: enum -> metadata -> auto-select by SM.
 */

#include "kernel_registry.h"
#include <cuda_runtime.h>
#include <stdio.h>

/* Metadata table indexed by BH_KernelVariant.
 *
 * min_sm: minimum SM version for correctness (e.g. 89 = SM8.9 Ada).
 * estimated_registers: conservative register count per thread from ncu
 *   ptxas report. Used to gate occupancy: if the variant would exceed
 *   max_registers_per_thread on the device, fall back.
 *
 * H2 ILP min_sm = 89: the 2-ray dual-issue benefit is Ada/Hopper specific.
 *   On SM8.0 (Ampere) the dual-issue FP32 pipeline is narrower and the
 *   extra register pressure from doubling live state can reduce occupancy
 *   enough to negate ILP gains. Benchmarked in YSU-engine against A100.
 */
const RtKernelInfo RT_KERNEL_INFO[BH_KERNEL_COUNT] = {
    /* FP32_BASELINE: safe default, works everywhere */
    {"FP32 Baseline (1 ray/thread)",    50, 1, 256, 48},
    /* FP32_COARSENED: 2 rays/thread ILP at FP32, Turing+ recommended */
    {"FP32 Coarsened (2 rays/thread)",  75, 2, 256, 80},
    /* FP16_STORAGE: FP16 ray state, FP32 compute, Ampere+ */
    {"FP16 Storage / FP32 Compute",     80, 1, 256, 40},
    /* FP16_H2_ILP: 2 rays/thread with __half2, Ada/Hopper dual-issue */
    {"FP16 H2 ILP (2 rays/thread)",     89, 2, 128, 96},
};

int registry_select_variant(void) {
    int device;
    if (cudaGetDevice(&device) != cudaSuccess) {
        return BH_KERNEL_FP32_BASELINE;
    }

    int sm_major = 0, sm_minor = 0;
    cudaDeviceGetAttribute(&sm_major, cudaDevAttrComputeCapabilityMajor, device);
    cudaDeviceGetAttribute(&sm_minor, cudaDevAttrComputeCapabilityMinor, device);
    int sm_version = sm_major * 10 + sm_minor;

    /* Maximum registers per thread = floor(regs_per_sm / (max_warps * 32)).
     * cudaDevAttrMaxRegistersPerMultiprocessor gives the SM register file size.
     * cudaDevAttrMaxThreadsPerMultiProcessor / 32 gives the warp slots.
     * This bounds the per-thread register budget at full occupancy. */
    int regs_per_sm = 0, max_threads_per_sm = 0;
    cudaDeviceGetAttribute(&regs_per_sm,
                           cudaDevAttrMaxRegistersPerMultiprocessor, device);
    cudaDeviceGetAttribute(&max_threads_per_sm,
                           cudaDevAttrMaxThreadsPerMultiProcessor, device);

    int max_regs_per_thread = 255; /* SM default cap */
    if (regs_per_sm > 0 && max_threads_per_sm > 0) {
        /* Register limit for sustaining at least one full warp per block */
        max_regs_per_thread = regs_per_sm / max_threads_per_sm;
    }

    /* Walk variants from most capable to least, pick first that fits */
    for (int v = BH_KERNEL_COUNT - 1; v >= 0; --v) {
        const RtKernelInfo& info = RT_KERNEL_INFO[v];
        if (sm_version < info.min_sm) continue;
        /* Reject if this variant's estimated register pressure exceeds the
         * per-thread budget at target occupancy. */
        if (info.estimated_registers > max_regs_per_thread) continue;
        return v;
    }

    return BH_KERNEL_FP32_BASELINE;
}

const RtKernelInfo* registry_get_info(int variant) {
    if (variant < 0 || variant >= BH_KERNEL_COUNT) return nullptr;
    return &RT_KERNEL_INFO[variant];
}
