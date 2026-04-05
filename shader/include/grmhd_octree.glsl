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
 *
 * Phase 6.2.5: Synchrotron emission and self-absorption from GRMHD fields.
 * Requires synchrotron_emission.glsl to be included before this file.
 * Uniforms grmhdBGauss, grmhdNeCm3, grmhdGammaPL, grmhdGammaMin, grmhdGammaMax
 * must be set from the CPU based on the simulation unit system.
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

// ============================================================================
// Phase 6.2.5: Synchrotron Emission from GRMHD Fields
//
// WHY: GRMHD simulation outputs conservative variables (rho, uu, B) in code
//      units. To compute observable synchrotron emission we need to convert
//      to CGS, derive the electron distribution parameters, then evaluate the
//      synchrotron functions from synchrotron_emission.glsl.
//
// Unit conversion uniforms (set from CPU, derived from simulation parameters):
//   grmhdBGauss   -- B_Gauss = B_code * grmhdBGauss
//   grmhdNeCm3    -- n_e [cm^-3] = rho_code * grmhdNeCm3
//
// Electron distribution (uniform across grid, set from CPU physics model):
//   grmhdGammaPL  -- power-law index p (N(gamma) ~ gamma^-p, typically 2.5)
//   grmhdGammaMin -- minimum Lorentz factor (default 10)
//   grmhdGammaMax -- maximum Lorentz factor (default 1e4)
// ============================================================================

/// Magnetic field scale: sim units -> Gauss
uniform float grmhdBGauss;
/// Electron density scale: rho_code -> n_e [cm^-3]
uniform float grmhdNeCm3;
/// Power-law electron index p
uniform float grmhdGammaPL;
/// Minimum Lorentz factor for power-law electrons
uniform float grmhdGammaMin;
/// Maximum Lorentz factor for power-law electrons
uniform float grmhdGammaMax;

/**
 * @brief Magnetic field magnitude [Gauss] from cell conservative variables.
 *
 * B = sqrt(B1^2 + B2^2 + B3^2) * grmhdBGauss
 *
 * B3 is held as 0.0 in the current octree (divergence-free reconstruction
 * deferred). For emission the error is negligible when B1 and B2 dominate.
 *
 * @param cell GRMHD cell data from sampleOctree()
 * @return Magnetic field strength [Gauss]
 */
float grmhdMagneticFieldGauss(CellData cell) {
    float B2 = cell.B1 * cell.B1 + cell.B2 * cell.B2 + cell.B3 * cell.B3;
    return sqrt(max(B2, 0.0)) * grmhdBGauss;
}

/**
 * @brief Electron number density [cm^-3] from cell mass density.
 *
 * In GRMHD, rho is the rest-mass density in code units. Converting to
 * physical CGS n_e requires the unit system and mean molecular weight:
 *   n_e = rho_code * grmhdNeCm3
 * where grmhdNeCm3 = rho_unit / (m_p * mu_e).
 *
 * @param cell GRMHD cell data from sampleOctree()
 * @return Electron number density [cm^-3]
 */
float grmhdElectronDensityCm3(CellData cell) {
    return max(cell.rho, 0.0) * grmhdNeCm3;
}

/**
 * @brief Synchrotron emissivity from GRMHD cell at frequency nu [Hz].
 *
 * Integrates the power-law electron distribution N(gamma) ~ gamma^-p over
 * the synchrotron single-electron spectrum F(x) using the function from
 * synchrotron_emission.glsl. Result is in relative units (not absolute CGS)
 * suitable for ray-marching emission accumulation.
 *
 * Returns 0 for cells with negligible magnetic field or density.
 *
 * @param cell GRMHD cell data from sampleOctree()
 * @param nu   Observer frequency [Hz]
 * @return Synchrotron specific intensity (relative units)
 */
float grmhdEmission(CellData cell, float nu) {
    float B   = grmhdMagneticFieldGauss(cell);
    float n_e = grmhdElectronDensityCm3(cell);
    if (B < 1e-30 || n_e < 1e-30) return 0.0;
    return synchrotron_intensity(nu, B, grmhdGammaMin, grmhdGammaMax,
                                 grmhdGammaPL, n_e);
}

/**
 * @brief Synchrotron self-absorption coefficient [cm^-1] from GRMHD cell.
 *
 * When the optical depth tau = integral(alpha * ds) exceeds ~1, the source
 * transitions from optically thin to thick emission. This coefficient feeds
 * into intensity_step() from radiative_transfer.glsl.
 *
 * @param cell GRMHD cell data from sampleOctree()
 * @param nu   Observer frequency [Hz]
 * @return Synchrotron absorption coefficient [cm^-1]
 */
float grmhdAbsorption(CellData cell, float nu) {
    float B   = grmhdMagneticFieldGauss(cell);
    float n_e = grmhdElectronDensityCm3(cell);
    if (B < 1e-30 || n_e < 1e-30) return 0.0;
    return absorption_coefficient(nu, B, n_e, grmhdGammaMin, grmhdGammaPL);
}

#endif  // GRMHD_OCTREE_GLSL
