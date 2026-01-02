#pragma once
/**
 * @file depth_prepass.h
 * @brief Depth pre-pass utilities for reducing overdraw in mesh-based rendering.
 *
 * A depth pre-pass renders opaque geometry to the depth buffer only (no color writes),
 * then the main pass uses GL_DEPTH_FUNC(GL_EQUAL) to avoid shading occluded fragments.
 *
 * This is most effective when:
 * - Fragment shaders are expensive (complex ray marching, heavy lighting)
 * - Significant overdraw exists due to overlapping geometry
 * - Geometry is opaque (transparent objects require separate handling)
 *
 * Currently the main black hole rendering uses a full-screen quad with ray marching,
 * which has zero overdraw and doesn't benefit from depth pre-pass. This infrastructure
 * is prepared for future mesh-based disk rendering.
 *
 * Usage:
 *   // In render loop
 *   if (depthPrepassEnabled && hasMeshGeometry) {
 *     DepthPrepass::begin();
 *     drawOpaqueGeometry(depthOnlyShader);
 *     DepthPrepass::end();
 *
 *     DepthPrepass::beginMainPass();
 *     drawOpaqueGeometry(fullShader);
 *     DepthPrepass::endMainPass();
 *   }
 */

#include <glbinding/gl46core/gl.h>
using namespace gl46core;

namespace DepthPrepass {

/// Configuration for depth pre-pass behavior
struct Config {
    bool enabled = false;           ///< Master toggle for depth pre-pass
    bool useEarlyZ = true;          ///< Use GL_EQUAL in main pass (requires pre-pass)
    bool clearDepth = true;         ///< Clear depth buffer before pre-pass
    float clearDepthValue = 1.0f;   ///< Depth clear value
};

/**
 * @brief Global configuration instance.
 */
inline Config& config() {
    static Config cfg;
    return cfg;
}

/**
 * @brief Begin depth pre-pass phase.
 *
 * Disables color writes and configures depth for writing.
 * Call drawOpaqueGeometry() with depth-only shader after this.
 */
inline void begin() {
    // Disable color writes
    glColorMask(GL_FALSE, GL_FALSE, GL_FALSE, GL_FALSE);

    // Enable depth test and writes
    glEnable(GL_DEPTH_TEST);
    glDepthMask(GL_TRUE);
    glDepthFunc(GL_LESS);

    // Optionally clear depth
    if (config().clearDepth) {
        glClearDepthf(config().clearDepthValue);
        glClear(GL_DEPTH_BUFFER_BIT);
    }
}

/**
 * @brief End depth pre-pass phase.
 *
 * Re-enables color writes. Depth buffer now contains closest surfaces.
 */
inline void end() {
    glColorMask(GL_TRUE, GL_TRUE, GL_TRUE, GL_TRUE);
}

/**
 * @brief Begin main pass with optional early-Z optimization.
 *
 * If useEarlyZ is enabled, sets depth func to GL_EQUAL so only fragments
 * matching the pre-pass depth are shaded (zero overdraw for opaque geometry).
 */
inline void beginMainPass() {
    glEnable(GL_DEPTH_TEST);

    if (config().useEarlyZ) {
        // Only shade fragments that exactly match pre-pass depth
        glDepthFunc(GL_EQUAL);
        // Disable depth writes (already written in pre-pass)
        glDepthMask(GL_FALSE);
    } else {
        // Standard depth testing
        glDepthFunc(GL_LESS);
        glDepthMask(GL_TRUE);
    }
}

/**
 * @brief End main pass.
 *
 * Restores default depth state.
 */
inline void endMainPass() {
    glDepthFunc(GL_LESS);
    glDepthMask(GL_TRUE);
}

/**
 * @brief Check if depth pre-pass should be used.
 *
 * Returns true if enabled and we have geometry that benefits from it.
 */
inline bool shouldUse() {
    return config().enabled;
}

/**
 * @brief RAII helper for depth pre-pass phase.
 */
class ScopedPrepass {
public:
    ScopedPrepass() {
        if (shouldUse()) {
            begin();
            active_ = true;
        }
    }
    ~ScopedPrepass() {
        if (active_) {
            end();
        }
    }
    explicit operator bool() const { return active_; }

private:
    bool active_ = false;
};

/**
 * @brief RAII helper for main pass phase.
 */
class ScopedMainPass {
public:
    ScopedMainPass() {
        if (shouldUse()) {
            beginMainPass();
            active_ = true;
        }
    }
    ~ScopedMainPass() {
        if (active_) {
            endMainPass();
        }
    }
    explicit operator bool() const { return active_; }

private:
    bool active_ = false;
};

} // namespace DepthPrepass
