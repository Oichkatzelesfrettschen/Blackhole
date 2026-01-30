/**
 * @file grmhd_octree.glsl
 * @brief GRMHD octree cell traversal for multi-resolution field sampling
 *
 * Phase 6.2b: GPU-resident octree for efficient GRMHD data access
 * - Coarse: root grid (nx, ny, nz cells)
 * - Fine: adaptive refinement (factor of 2 per level)
 * - Leaf: stores 8 conservative variables (rho, uu, u1, u2, u3, B1, B2, B3)
 *
 * Traversal: world coordinate -> cell index -> leaf node -> variables
 * Complexity: O(log N) for N total cells
 */

#ifndef GRMHD_OCTREE_GLSL
#define GRMHD_OCTREE_GLSL

// ============================================================================
// Octree Node Structure
// ============================================================================

/**
 * OctreeNode: 32-byte entry for one cell/node in hierarchy
 * Packed for efficient GPU memory layout
 */
struct OctreeNode {
    // Cell data (8 floats = 32 bytes)
    float rho;        // Density
    float uu;         // Internal energy density
    float u1, u2, u3; // Contravariant 3-velocity
    float B1, B2;     // Contravariant magnetic field (B3 implicit)
};

// ============================================================================
// GRMHD Grid Metadata (UBO)
// ============================================================================

layout(std140, binding = 0) uniform GRMHDGridMetadata {
    uvec3 gridDims;         // (nx, ny, nz) root grid size
    uint refinementLevels;  // Tree depth
    vec4 coordMin;          // (r_min, theta_min, phi_min, unused)
    vec4 coordMax;          // (r_max, theta_max, phi_max, unused)
    uint cellsPerBlock;     // Block size (512 typical)
    uint totalCells;        // Total nx*ny*nz
    uint blockStrideBytes;  // Stride to next block
    uint nodesPerBlock;     // Nodes per 4KB block
} grmhdGrid;

// ============================================================================
// GRMHD Octree SSBO Bindings
// ============================================================================

layout(std430, binding = 1) readonly buffer OctreeNodesSSBO {
    OctreeNode cells[];
} octreeNodes;

layout(std430, binding = 2) readonly buffer BlockIndexSSBO {
    uvec4 childOffsets[];  // (blockIdx, cellOffset, refinement_level, unused)
} blockIndex;

// ============================================================================
// Octree Access Functions
// ============================================================================

/**
 * CoordinateToCell: convert Boyer-Lindquist coord to grid index
 */
uvec3 coordinateToCell(vec3 coord) {
    vec3 normalized = vec3(
        (coord.x - grmhdGrid.coordMin.x) / (grmhdGrid.coordMax.x - grmhdGrid.coordMin.x),
        (coord.y - grmhdGrid.coordMin.y) / (grmhdGrid.coordMax.y - grmhdGrid.coordMin.y),
        (coord.z - grmhdGrid.coordMin.z) / (grmhdGrid.coordMax.z - grmhdGrid.coordMin.z)
    );

    normalized = clamp(normalized, vec3(0.0), vec3(0.99999));

    uvec3 cellIdx = uvec3(
        uint(normalized.x * grmhdGrid.gridDims.x),
        uint(normalized.y * grmhdGrid.gridDims.y),
        uint(normalized.z * grmhdGrid.gridDims.z)
    );

    return cellIdx;
}

/**
 * CellData: result of octree lookup
 */
struct CellData {
    float rho, uu;
    float u1, u2, u3;
    float B1, B2, B3;
};

/**
 * SampleOctree: retrieve cell data at world coordinate
 */
CellData sampleOctree(vec3 coord) {
    CellData result;

    uvec3 cellIdx = coordinateToCell(coord);

    uint cellLinearIdx = cellIdx.z * (grmhdGrid.gridDims.x * grmhdGrid.gridDims.y) +
                         cellIdx.y * grmhdGrid.gridDims.x +
                         cellIdx.x;

    if (cellLinearIdx >= grmhdGrid.totalCells) {
        result = CellData(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
        return result;
    }

    uint nodeOffset = cellLinearIdx;

    if (nodeOffset >= octreeNodes.cells.length()) {
        result = CellData(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
        return result;
    }

    OctreeNode node = octreeNodes.cells[nodeOffset];

    result.rho = node.rho;
    result.uu = node.uu;
    result.u1 = node.u1;
    result.u2 = node.u2;
    result.u3 = node.u3;
    result.B1 = node.B1;
    result.B2 = node.B2;
    result.B3 = 0.0;  // Placeholder: computed from divergence-free constraint

    return result;
}

#endif  // GRMHD_OCTREE_GLSL
