/**
 * @file cuda_render_manager.h
 * @brief C++ wrapper that consolidates BhCudaState lifecycle into one class.
 *
 * WHY: The 14 scattered #if BLACKHOLE_HAS_CUDA blocks in main.cpp each call
 *      bhCuda* C functions with direct access to a module-level BhCudaState
 *      struct. That couples the CUDA lifecycle to main.cpp's local state and
 *      makes each call site responsible for its own init/null guards, error
 *      handling, and retry logic. CudaRenderManager collects all of that into
 *      one place so each call site in main.cpp becomes a single line.
 *
 * WHAT: Header-only C++ class wrapping BhCudaState + the bhCuda* C functions.
 *       Not a CUDA translation unit -- compiles with the C++23 host compiler.
 *
 * HOW:
 *   #if BLACKHOLE_HAS_CUDA
 *   #include "cuda/cuda_render_manager.h"
 *   ...
 *   static CudaRenderManager cudaManager;
 *   ...
 *   cudaManager.ensureInit(texBlackhole, width, height);
 *   cudaManager.registerLut(slot, tex, target);   // no-op when not ready
 *   cudaManager.renderFrame(&params);
 *   cudaManager.resize(texBlackhole, newW, newH);
 *   #endif
 *
 * Thread safety: render-thread only (mirrors cuda_backend.h contract).
 */

#pragma once

#include "cuda_backend.h"

#include <cstdio>

/**
 * @brief Manages the full CUDA render backend lifecycle.
 *
 * Holds BhCudaState and translates higher-level render-loop events (init,
 * resize, LUT upload, frame render, shutdown) into the corresponding bhCuda*
 * calls.  Each method is safe to call regardless of the current state: null
 * checks and attempt guards are handled internally.
 */
class CudaRenderManager {
public:
    // -------------------------------------------------------------------------
    // Accessors used by the ImGui panel and render dispatch
    // -------------------------------------------------------------------------

    /** @brief True when the user has enabled the CUDA render path via ImGui. */
    [[nodiscard]] bool isEnabled()       const noexcept { return state_.enabled; }

    /** @brief True when the backend has been successfully initialized. */
    [[nodiscard]] bool isReady()         const noexcept { return state_.backend != nullptr; }

    /** @brief True after the first init attempt (success or failure). */
    [[nodiscard]] bool wasInitAttempted() const noexcept { return state_.initAttempted; }

    /** @brief Raw pointer to the opaque backend (nullptr when not ready). */
    [[nodiscard]] BH_CudaBackend* backend() const noexcept { return state_.backend; }

    /**
     * @brief User's kernel variant preference: -1 = auto, 0-3 = explicit.
     * Does not reflect the variant actually running (see activeVariant()).
     */
    [[nodiscard]] int kernelVariant() const noexcept { return state_.kernelVariant; }

    /** @brief Active variant as reported by the backend, or -1 when not ready. */
    [[nodiscard]] int activeVariant() const noexcept {
        return (state_.backend != nullptr) ? bhCudaGetVariant(state_.backend) : -1;
    }

    // -------------------------------------------------------------------------
    // Mutators used by the ImGui panel
    // -------------------------------------------------------------------------

    /**
     * @brief Toggle the CUDA render path on or off.
     *
     * Toggling off also resets the init-attempted flag so that re-enabling
     * triggers a clean retry the next frame rather than staying permanently
     * disabled after a past failure.
     */
    void setEnabled(bool enabled) noexcept {
        state_.enabled = enabled;
        if (!enabled) {
            state_.initAttempted = false;
        }
    }

    /**
     * @brief Set the preferred kernel variant (-1 = auto).
     *
     * If the backend is already initialized, the change takes effect
     * immediately via bhCudaSetVariant.
     */
    void setKernelVariant(int variant) noexcept {
        state_.kernelVariant = variant;
        if (state_.backend != nullptr) {
            bhCudaSetVariant(state_.backend, variant);
        }
    }

    // -------------------------------------------------------------------------
    // Lifecycle methods
    // -------------------------------------------------------------------------

    /**
     * @brief Initialize the CUDA backend on first use.
     *
     * No-op when the backend is already initialized or when initialization
     * was already attempted (preventing per-frame retry spam).  Applies the
     * stored kernelVariant on success.
     *
     * @param glTexture  GL texture handle for the primary output (texBlackhole).
     * @param width      Initial framebuffer width.
     * @param height     Initial framebuffer height.
     * @return true on success (backend is now ready), false otherwise.
     */
    bool ensureInit(unsigned int glTexture, int width, int height) noexcept {
        if (state_.backend != nullptr)  return true;
        if (state_.initAttempted)       return false;

        state_.initAttempted = true;
        state_.backend = bhCudaInit(glTexture, width, height);

        if (state_.backend != nullptr) {
            if (state_.kernelVariant >= 0) {
                bhCudaSetVariant(state_.backend, state_.kernelVariant);
            }
            return true;
        }

        // NOLINT(cert-err33-c) -- diagnostic, return value intentionally unused
        (void)fprintf(stderr, "CUDA: bhCudaInit failed -- toggle checkbox to retry\n");
        return false;
    }

    /**
     * @brief Register a GL texture as a CUDA LUT for kernel sampling.
     *
     * Safe to call when the backend is not yet initialized: the call is
     * silently dropped.  Re-registration is idempotent.
     *
     * @param slot      BhLutSlot index (0=emissivity, 1=redshift, ..., 4=galaxy).
     * @param glTexture GL texture ID.
     * @param target    GL texture target (e.g. GL_TEXTURE_2D, GL_TEXTURE_CUBE_MAP).
     */
    void registerLut(int slot, unsigned int glTexture, unsigned int target) noexcept {
        if (state_.backend == nullptr) return;
        bhCudaRegisterLut(state_.backend, slot, glTexture, target);
    }

    /**
     * @brief Handle a framebuffer resize.
     *
     * No-op when the backend is not initialized.  On error, the backend is
     * shut down so that ensureInit() can re-initialize it on the next frame.
     *
     * @param glTexture New GL texture handle (may differ after GL recreation).
     * @param width     New width.
     * @param height    New height.
     */
    void resize(unsigned int glTexture, int width, int height) noexcept {
        if (state_.backend == nullptr) return;
        if (bhCudaResize(state_.backend, glTexture, width, height) != 0) {
            // NOLINT(cert-err33-c) -- diagnostic
            (void)fprintf(stderr, "CUDA: bhCudaResize failed -- reinitializing\n");
            shutdown();
        }
    }

    /**
     * @brief Render one frame using the CUDA backend.
     *
     * No-op when the backend is not initialized.  On error, the backend is
     * shut down; ensureInit() will attempt reinitialization on the next frame
     * if the user leaves CUDA enabled.
     *
     * @param params Scene and camera parameters for this frame.
     */
    void renderFrame(const BH_LaunchParams *params) noexcept {
        if (state_.backend == nullptr) return;
        if (bhCudaRenderFrame(state_.backend, params) != 0) {
            // NOLINT(cert-err33-c) -- diagnostic
            (void)fprintf(stderr, "CUDA: render frame failed -- shutting down backend\n");
            shutdown();
        }
    }

    /**
     * @brief Release all CUDA resources.
     *
     * Resets initAttempted so that re-enabling the CUDA path triggers a fresh
     * initialization attempt.
     */
    void shutdown() noexcept {
        bhCudaShutdown(state_.backend);   // safe with nullptr
        state_.backend       = nullptr;
        state_.initAttempted = false;
    }

private:
    BhCudaState state_{nullptr, -1, false, false};
};
