/**
 * @file grmhd_octree.glsl
 * @brief GPU octree traversal for GRMHD tile-based streaming
 *
 * WHY: Enable efficient ray marching through sparse GRMHD volumes without loading entire dataset
 * WHAT: Octree spatial indexing, multi-resolution LOD, tile lookup, and trilinear interpolation
 * HOW: DDA-style octree traversal, texture atlas sampling, adaptive step sizing
 *
 * Architecture:
 *   - 8-way octree subdivision (0 = full resolution, higher levels = coarser)
 *   - Tile-based storage (each node = 64^3 or 32^3 voxel cube)
 *   - Texture array for tile storage (3D texture slices)
 *   - Ray marching with adaptive LOD based on distance
 *
 * Performance:
 *   - Target: <1ms per frame for 1920x1080 @ 60fps
 *   - Cache-friendly: access tiles in spatial order
 *   - Early ray termination: skip empty tiles
 *
 * References:
 *   - Revelles et al. (2000) - "An efficient parametric algorithm for octree traversal"
 *   - Laine & Karras (2011) - "Efficient sparse voxel octrees"
 *   - Event Horizon Telescope (2019) - GRMHD simulation visualization
 */

#version 460 core

// ============================================================================
// Constants and Configuration
// ============================================================================

// Octree configuration
const uint OCTREE_MAX_DEPTH = 8u;        // Max subdivision levels
const uint TILE_SIZE = 32u;               // Voxels per tile edge (32^3 = 32K voxels)
const float TILE_SIZE_F = float(TILE_SIZE);
const vec3 TILE_SIZE_VEC = vec3(TILE_SIZE_F);

// GRMHD domain bounds (in gravitational radii r_g = GM/c^2)
const vec3 GRMHD_MIN = vec3(-100.0, -100.0, -100.0);
const vec3 GRMHD_MAX = vec3(100.0, 100.0, 100.0);
const vec3 GRMHD_EXTENT = GRMHD_MAX - GRMHD_MIN;

// Octree node structure (packed into uvec4 for efficiency)
// x: child pointer (0 = leaf node)
// y: tile index (texture array layer)
// z: occupancy mask (8 bits, one per child)
// w: reserved for future use
struct OctreeNode {
    uint childPtr;
    uint tileIndex;
    uint occupancyMask;
    uint reserved;
};

// ============================================================================
// Uniforms (bound from C++ side)
// ============================================================================

// Octree structure buffer (SSBO)
layout(std430, binding = 4) readonly buffer OctreeBuffer {
    uvec4 nodes[];  // Packed OctreeNode data
} octreeBuffer;

// GRMHD tile data (3D texture array)
// Format: RGBA32F
//   R: rest-mass density (rho)
//   G: internal energy density (u)
//   B: radial velocity (v^r)
//   A: angular velocity (v^phi)
layout(binding = 5) uniform sampler2DArray grmhdTileAtlas;

// Current frame index
uniform uint u_frameIndex = 0u;

// Ray marching parameters
uniform float u_stepSizeMultiplier = 1.0;
uniform float u_lodBias = 0.0;  // Negative = higher detail, positive = coarser

// ============================================================================
// Octree Node Access
// ============================================================================

OctreeNode unpackNode(uint nodeIndex) {
    uvec4 packed = octreeBuffer.nodes[nodeIndex];
    OctreeNode node;
    node.childPtr = packed.x;
    node.tileIndex = packed.y;
    node.occupancyMask = packed.z;
    node.reserved = packed.w;
    return node;
}

bool isLeafNode(OctreeNode node) {
    return node.childPtr == 0u;
}

bool isOccupied(OctreeNode node, uint childIndex) {
    return ((node.occupancyMask >> childIndex) & 1u) != 0u;
}

uint getChildIndex(vec3 localPos) {
    // Map position to child index [0,7]
    // Binary: ZYX (Z=most significant, X=least significant)
    uint idx = 0u;
    if (localPos.x >= 0.5) idx |= 1u;
    if (localPos.y >= 0.5) idx |= 2u;
    if (localPos.z >= 0.5) idx |= 4u;
    return idx;
}

// ============================================================================
// Coordinate Transformations
// ============================================================================

// World space (r_g units) to normalized octree space [0,1]^3
vec3 worldToOctree(vec3 worldPos) {
    return (worldPos - GRMHD_MIN) / GRMHD_EXTENT;
}

// Normalized octree space to world space
vec3 octreeToWorld(vec3 octreePos) {
    return octreePos * GRMHD_EXTENT + GRMHD_MIN;
}

// Tile-local normalized coordinates [0,1]^3 to texture coordinates
vec3 tileLocalToTexCoord(vec3 localPos, uint tileIndex) {
    // localPos is in [0,1]^3 within the tile
    // tileIndex selects the texture array layer
    return vec3(localPos.xy, float(tileIndex));
}

// ============================================================================
// Octree Traversal (DDA-style)
// ============================================================================

struct TraversalState {
    uint nodeIndex;
    uint level;
    vec3 nodeBoundsMin;  // In octree space [0,1]^3
    vec3 nodeBoundsMax;
    bool valid;
};

// Initialize traversal at root
TraversalState initTraversal(vec3 octreePos) {
    TraversalState state;
    state.nodeIndex = 0u;  // Root node
    state.level = 0u;
    state.nodeBoundsMin = vec3(0.0);
    state.nodeBoundsMax = vec3(1.0);
    state.valid = true;

    // Check if position is within bounds
    if (any(lessThan(octreePos, state.nodeBoundsMin)) ||
        any(greaterThanEqual(octreePos, state.nodeBoundsMax))) {
        state.valid = false;
    }

    return state;
}

// Descend octree to find leaf node containing position
TraversalState descendToLeaf(vec3 octreePos, uint maxDepth) {
    TraversalState state = initTraversal(octreePos);

    if (!state.valid) {
        return state;
    }

    // Traverse down the octree
    for (uint depth = 0u; depth < maxDepth; ++depth) {
        OctreeNode node = unpackNode(state.nodeIndex);

        // If leaf node, we are done
        if (isLeafNode(node)) {
            state.level = depth;
            return state;
        }

        // Compute position within current node [0,1]^3
        vec3 nodeExtent = state.nodeBoundsMax - state.nodeBoundsMin;
        vec3 localPos = (octreePos - state.nodeBoundsMin) / nodeExtent;

        // Determine which child octant contains the position
        uint childIndex = getChildIndex(localPos);

        // Check occupancy
        if (!isOccupied(node, childIndex)) {
            // Empty node, ray exits
            state.valid = false;
            return state;
        }

        // Descend to child
        state.nodeIndex = node.childPtr + childIndex;

        // Update bounds
        vec3 childCenter = state.nodeBoundsMin + nodeExtent * 0.5;
        if ((childIndex & 1u) != 0u) {
            state.nodeBoundsMin.x = childCenter.x;
        } else {
            state.nodeBoundsMax.x = childCenter.x;
        }
        if ((childIndex & 2u) != 0u) {
            state.nodeBoundsMin.y = childCenter.y;
        } else {
            state.nodeBoundsMax.y = childCenter.y;
        }
        if ((childIndex & 4u) != 0u) {
            state.nodeBoundsMin.z = childCenter.z;
        } else {
            state.nodeBoundsMax.z = childCenter.z;
        }
    }

    state.level = maxDepth;
    return state;
}

// ============================================================================
// GRMHD Data Sampling
// ============================================================================

struct GRMHDSample {
    float rho;        // Rest-mass density
    float u;          // Internal energy density
    float v_r;        // Radial velocity (Boyer-Lindquist)
    float v_phi;      // Angular velocity
    bool valid;
};

// Sample GRMHD data at world position with adaptive LOD
GRMHDSample sampleGRMHD(vec3 worldPos, float lodBias) {
    GRMHDSample sample;
    sample.valid = false;

    // Transform to octree space
    vec3 octreePos = worldToOctree(worldPos);

    // Compute LOD based on distance from origin (camera at singularity)
    float dist = length(worldPos);
    float lod = log2(max(1.0, dist / 10.0)) + lodBias;
    uint maxDepth = uint(clamp(float(OCTREE_MAX_DEPTH) - lod, 1.0, float(OCTREE_MAX_DEPTH)));

    // Traverse to leaf node
    TraversalState state = descendToLeaf(octreePos, maxDepth);

    if (!state.valid) {
        return sample;
    }

    // Get leaf node
    OctreeNode node = unpackNode(state.nodeIndex);

    if (node.tileIndex == 0u) {
        // No tile data (empty or not yet loaded)
        return sample;
    }

    // Compute tile-local coordinates [0,1]^3
    vec3 nodeExtent = state.nodeBoundsMax - state.nodeBoundsMin;
    vec3 localPos = (octreePos - state.nodeBoundsMin) / nodeExtent;

    // Sample from texture atlas with trilinear interpolation
    vec3 texCoord = tileLocalToTexCoord(localPos, node.tileIndex);
    vec4 texel = texture(grmhdTileAtlas, texCoord);

    // Unpack GRMHD variables
    sample.rho = texel.r;
    sample.u = texel.g;
    sample.v_r = texel.b;
    sample.v_phi = texel.a;
    sample.valid = true;

    return sample;
}

// Sample with default LOD bias
GRMHDSample sampleGRMHD(vec3 worldPos) {
    return sampleGRMHD(worldPos, u_lodBias);
}

// ============================================================================
// Ray Marching Integration
// ============================================================================

// Compute adaptive step size based on local octree resolution
float computeStepSize(vec3 octreePos, float baseDt) {
    TraversalState state = descendToLeaf(octreePos, OCTREE_MAX_DEPTH);

    if (!state.valid) {
        return baseDt;
    }

    // Step size proportional to node size
    vec3 nodeExtent = state.nodeBoundsMax - state.nodeBoundsMin;
    float nodeSize = (nodeExtent.x + nodeExtent.y + nodeExtent.z) / 3.0;

    // Convert to world space
    float worldNodeSize = nodeSize * length(GRMHD_EXTENT) / sqrt(3.0);

    // Step at 1/4 to 1/2 of node size for good sampling
    return worldNodeSize * 0.25 * u_stepSizeMultiplier;
}

// Check if position is within GRMHD domain bounds
bool inGRMHDBounds(vec3 worldPos) {
    return all(greaterThanEqual(worldPos, GRMHD_MIN)) &&
           all(lessThanEqual(worldPos, GRMHD_MAX));
}

// ============================================================================
// Emission and Absorption Coefficients (Placeholder)
// ============================================================================

// Compute emission coefficient from GRMHD data
// Returns specific intensity I_nu [erg/s/cm^2/Hz/sr]
vec3 grmhdEmission(GRMHDSample sample, float nu) {
    if (!sample.valid) {
        return vec3(0.0);
    }

    // Placeholder: simple power-law scaling
    // TODO: Replace with proper synchrotron emission formula
    float emissivity = sample.rho * sample.u * pow(nu / 2.3e11, -0.7);

    // Map to RGB (false color visualization)
    vec3 color = vec3(1.0, 0.6, 0.3);  // Orange glow
    return color * emissivity;
}

// Compute absorption coefficient from GRMHD data
// Returns opacity alpha [dimensionless]
float grmhdAbsorption(GRMHDSample sample, float nu) {
    if (!sample.valid) {
        return 0.0;
    }

    // Placeholder: density-based opacity
    // TODO: Replace with proper synchrotron self-absorption
    return sample.rho * 0.01;
}

// ============================================================================
// Public API Functions
// ============================================================================

/**
 * @brief Sample GRMHD density at world position
 * @param worldPos Position in gravitational radii (r_g)
 * @return Rest-mass density rho [g/cm^3] or 0 if invalid
 */
float getGRMHDDensity(vec3 worldPos) {
    GRMHDSample sample = sampleGRMHD(worldPos);
    return sample.valid ? sample.rho : 0.0;
}

/**
 * @brief Sample GRMHD velocity at world position
 * @param worldPos Position in gravitational radii (r_g)
 * @return 4-velocity components (v^r, v^theta, v^phi, 0) or zero if invalid
 */
vec4 getGRMHDVelocity(vec3 worldPos) {
    GRMHDSample sample = sampleGRMHD(worldPos);
    if (!sample.valid) {
        return vec4(0.0);
    }
    return vec4(sample.v_r, 0.0, sample.v_phi, 0.0);
}

/**
 * @brief Check if GRMHD data is available at position
 * @param worldPos Position in gravitational radii (r_g)
 * @return true if valid data exists, false otherwise
 */
bool hasGRMHDData(vec3 worldPos) {
    GRMHDSample sample = sampleGRMHD(worldPos);
    return sample.valid;
}
