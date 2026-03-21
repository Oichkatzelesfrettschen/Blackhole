/**
 * @file grmhd_hdf5_loader.h
 * @brief Single-snapshot GRMHD loader for iharm3d/KORAL/BHAC HDF5 dump files.
 *
 * WHY: The GRMHDStreamer handles nubhlight_pack JSON + flat binary streaming.
 *      Real simulation codes (iharm3d, KORAL, BHAC) emit per-timestep HDF5 dumps
 *      that must be read directly rather than requiring a pre-processing step.
 *      This loader reads HDF5 and produces a GRMHDTile + header info in one call,
 *      compatible with the existing RGBA32F tile pipeline.
 *
 * WHAT: Three format variants are supported:
 *   - iharm3d / KORAL: "prims" dataset [n1,n2,n3,NVAR] (channels-last) or
 *                      [NVAR,n1,n2,n3] (channels-first); n1/n2/n3/t/gam at root
 *                      or in "header" group.  NVAR >= 5: RHO,UU,U1,U2,U3,...
 *   - BHAC:            "Grid" group + individual scalar datasets "dens","ener",
 *                      "vx","vy","vz"; grid dims NX/NY/NZ at root.
 *
 * HOW: HighFive 3.x used for all HDF5 I/O.  Format is auto-detected from
 *      the file structure by GRMHDHdf5Loader::detectCode().  Output packs
 *      channels as RGBA32F: R=rho, G=ug, B=u1, A=u2 -- matching the
 *      nubhlight_pack convention so the same shader/CUDA paths consume the tile.
 */

#pragma once

#include <memory>
#include <string>
#include <vector>

#include "grmhd_streaming.h"

namespace blackhole {

/** @brief GRMHD simulation code that produced the HDF5 dump. */
enum class GRMHDCode {
    IHARM3D, ///< iharm3d / HARM2D / KORAL (prims dataset, root or header attrs)
    BHAC,    ///< Black Hole Accretion Code (Grid group, individual scalar fields)
    UNKNOWN, ///< Format not recognized
};

/** @brief Metadata extracted from an HDF5 dump header. */
struct GRMHDHdf5Info {
    GRMHDCode code = GRMHDCode::UNKNOWN;
    std::size_t n1{};  ///< Radial grid cells
    std::size_t n2{};  ///< Polar grid cells
    std::size_t n3{};  ///< Azimuthal grid cells
    double time{};     ///< Simulation time in M units
    double gamma{};    ///< Adiabatic index (0 if absent)
    std::vector<std::string> fields; ///< Channel labels in RGBA output order
};

/**
 * @brief Loader for single-snapshot GRMHD HDF5 dump files.
 *
 * All methods are static.  Call load() to read one snapshot; use the returned
 * tile directly or inject it into a TileCache for streaming.
 */
class GRMHDHdf5Loader {
public:
    /**
     * @brief Load one GRMHD snapshot from an HDF5 dump file.
     *
     * Auto-detects the simulation code from the file structure.  The tile
     * channels are packed as RGBA32F: R=rho, G=ug, B=u1, A=u2.
     *
     * @param path  Path to the .h5 or .hdf5 dump file.
     * @param info  Optional output: populated with header metadata on success.
     * @return Shared pointer to the loaded tile, or nullptr on any error.
     */
    static std::shared_ptr<GRMHDTile> load(const std::string &path,
                                            GRMHDHdf5Info *info = nullptr);

    /**
     * @brief Detect which simulation code produced the HDF5 file.
     *
     * Inspects dataset and group names without reading array data.
     *
     * @param path Path to the HDF5 file.
     * @return Detected GRMHDCode, or GRMHDCode::UNKNOWN if unrecognized.
     */
    static GRMHDCode detectCode(const std::string &path);
};

} // namespace blackhole
