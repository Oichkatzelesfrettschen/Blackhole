#pragma once
/**
 * @file mesh_optimizer.h
 * @brief Mesh optimization utilities using meshoptimizer library.
 *
 * Provides overdraw optimization and vertex cache optimization for geometry.
 * Currently used for future mesh-based disk rendering; the main black hole
 * visualization uses procedural ray marching and doesn't require mesh optimization.
 *
 * Usage:
 *   #if BLACKHOLE_ENABLE_MESHOPTIMIZER
 *   MeshOptimizer::optimizeOverdraw(indices, vertices, vertexCount, stride);
 *   #endif
 */

#include <cstddef>
#include <vector>

#if BLACKHOLE_ENABLE_MESHOPTIMIZER
#include <meshoptimizer.h>
#endif

namespace MeshOptimizer {

/**
 * @brief Optimize index buffer for vertex cache efficiency.
 *
 * Reorders triangles to improve GPU vertex cache hit rate.
 *
 * @param indices Index buffer (modified in place)
 * @param indexCount Number of indices (must be multiple of 3)
 * @param vertexCount Number of unique vertices
 * @return true if optimization was performed
 */
inline bool optimizeVertexCache(std::vector<unsigned int>& indices, std::size_t vertexCount) {
#if BLACKHOLE_ENABLE_MESHOPTIMIZER
    if (indices.empty() || indices.size() % 3 != 0) {
        return false;
    }
    meshopt_optimizeVertexCache(indices.data(), indices.data(), indices.size(), vertexCount);
    return true;
#else
    (void)indices;
    (void)vertexCount;
    return false;
#endif
}

/**
 * @brief Optimize index buffer to reduce overdraw.
 *
 * Reorders triangles to minimize fragment shader invocations for occluded pixels.
 * Should be called after optimizeVertexCache for best results.
 *
 * @param indices Index buffer (modified in place)
 * @param vertices Vertex position buffer (float x,y,z per vertex)
 * @param vertexCount Number of unique vertices
 * @param stride Bytes between consecutive vertex positions (usually sizeof(float)*3 or sizeof(Vertex))
 * @param threshold Overdraw threshold (1.0 = no overdraw allowed, higher = more relaxed)
 * @return true if optimization was performed
 */
inline bool optimizeOverdraw(std::vector<unsigned int>& indices,
                             const float* vertices,
                             std::size_t vertexCount,
                             std::size_t stride,
                             float threshold = 1.05f) {
#if BLACKHOLE_ENABLE_MESHOPTIMIZER
    if (indices.empty() || indices.size() % 3 != 0 || vertices == nullptr) {
        return false;
    }
    meshopt_optimizeOverdraw(indices.data(), indices.data(), indices.size(),
                             vertices, vertexCount, stride, threshold);
    return true;
#else
    (void)indices;
    (void)vertices;
    (void)vertexCount;
    (void)stride;
    (void)threshold;
    return false;
#endif
}

/**
 * @brief Optimize vertex buffer for fetch efficiency.
 *
 * Reorders vertices to match index buffer access patterns.
 * Must also remap index buffer.
 *
 * @tparam Vertex Vertex type
 * @param indices Index buffer (modified in place to use new vertex order)
 * @param vertices Vertex buffer (modified in place)
 * @return Number of unique vertices after optimization
 */
template <typename Vertex>
inline std::size_t optimizeVertexFetch(std::vector<unsigned int>& indices,
                                       std::vector<Vertex>& vertices) {
#if BLACKHOLE_ENABLE_MESHOPTIMIZER
    if (indices.empty() || vertices.empty()) {
        return vertices.size();
    }

    std::vector<unsigned int> remap(vertices.size());
    std::size_t uniqueVertexCount = meshopt_optimizeVertexFetchRemap(
        remap.data(), indices.data(), indices.size(), vertices.size());

    meshopt_remapIndexBuffer(indices.data(), indices.data(), indices.size(), remap.data());
    meshopt_remapVertexBuffer(vertices.data(), vertices.data(), vertices.size(),
                              sizeof(Vertex), remap.data());

    vertices.resize(uniqueVertexCount);
    return uniqueVertexCount;
#else
    (void)indices;
    return vertices.size();
#endif
}

/**
 * @brief Full optimization pipeline for indexed geometry.
 *
 * Applies all optimizations in the recommended order:
 * 1. Vertex cache optimization
 * 2. Overdraw optimization
 * 3. Vertex fetch optimization
 *
 * @tparam Vertex Vertex type (must have x,y,z as first 3 floats)
 * @param indices Index buffer
 * @param vertices Vertex buffer
 * @param positionOffset Byte offset of position in Vertex struct (usually 0)
 * @return true if any optimization was performed
 */
template <typename Vertex>
inline bool optimizeMesh(std::vector<unsigned int>& indices,
                         std::vector<Vertex>& vertices,
                         std::size_t positionOffset = 0) {
#if BLACKHOLE_ENABLE_MESHOPTIMIZER
    if (indices.empty() || vertices.empty() || indices.size() % 3 != 0) {
        return false;
    }

    // Step 1: Vertex cache optimization
    meshopt_optimizeVertexCache(indices.data(), indices.data(), indices.size(), vertices.size());

    // Step 2: Overdraw optimization
    const auto* positions = reinterpret_cast<const float*>(
        reinterpret_cast<const char*>(vertices.data()) + positionOffset);
    meshopt_optimizeOverdraw(indices.data(), indices.data(), indices.size(),
                             positions, vertices.size(), sizeof(Vertex), 1.05f);

    // Step 3: Vertex fetch optimization
    optimizeVertexFetch(indices, vertices);

    return true;
#else
    (void)indices;
    (void)vertices;
    (void)positionOffset;
    return false;
#endif
}

/**
 * @brief Check if meshoptimizer is available at runtime.
 */
inline bool isAvailable() {
#if BLACKHOLE_ENABLE_MESHOPTIMIZER
    return true;
#else
    return false;
#endif
}

} // namespace MeshOptimizer
