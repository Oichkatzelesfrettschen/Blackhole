/**
 * @file grmhd_hdf5_loader.cpp
 * @brief Implementation of GRMHDHdf5Loader for iharm3d/KORAL/BHAC HDF5 dumps.
 *
 * WHY: iharm3d (and derivatives) is the primary code used by the EHT
 *      collaboration for GRMHD simulations of M87* and Sgr A*.  Enabling
 *      direct HDF5 loading without a nubhlight_pack pre-processing step
 *      reduces the iteration cycle for EHT comparison work.
 *
 * WHAT: Two format implementations -- iharm3d (with KORAL as a near-alias)
 *       and BHAC.  Auto-detection inspects dataset/group names; no data is
 *       read until the format is confirmed.
 *
 * HOW: HighFive 3.x API.  Primitives are read as double and converted to
 *      float32 for the tile, avoiding precision loss on the read path while
 *      keeping the GPU tile format compact.
 *
 * References:
 *   - iharm3d: Noble et al. (2006) ApJ 641, 626; Ryan et al. (2017)
 *   - BHAC: Porth et al. (2017) Comput. Astrophys. Cosmol. 4, 1
 *   - KORAL: Sadowski et al. (2013) MNRAS 429, 3533
 */

#include "grmhd_hdf5_loader.h"
#include "grmhd_streaming.h"   // GRMHDTile (misc-include-cleaner: used directly here)

#include <cstddef>
#include <exception>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include <highfive/H5DataSet.hpp>  // HighFive::DataSet
#include <highfive/H5File.hpp>     // HighFive::File

namespace blackhole {

namespace {

// ---------------------------------------------------------------------------
// Attribute helpers
// ---------------------------------------------------------------------------

/** @brief Read an attribute from the file root; fall back to "header" group. */
template <typename T>
bool tryReadAttr(const HighFive::File &file, const std::string &name, T &out) {
    if (file.hasAttribute(name)) {
        file.getAttribute(name).read(out);
        return true;
    }
    if (file.exist("header") &&
        file.getGroup("header").hasAttribute(name)) {
        file.getGroup("header").getAttribute(name).read(out);
        return true;
    }
    return false;
}

/**
 * @brief Read an integer grid dimension, trying a lowercase and an uppercase
 *        variant of the attribute name.
 */
bool readGridDim(const HighFive::File &file,
                 const std::string &lower,
                 const std::string &upper,
                 std::size_t &out) {
    int val = 0;
    if (tryReadAttr(file, lower, val) || tryReadAttr(file, upper, val)) {
        if (val <= 0) {
            return false;
        }
        out = static_cast<std::size_t>(val);
        return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// iharm3d / KORAL format loader
//
// Expected structure (both old HARM and modern iharm3d):
//   Root attributes (or in "header" group):
//     n1 / N1  -- radial cells
//     n2 / N2  -- polar cells
//     n3 / N3  -- azimuthal cells
//     t        -- simulation time in M units
//     gam      -- adiabatic index (optional)
//   Dataset "prims":
//     channels-last:  shape [n1, n2, n3, NVAR], NVAR >= 5
//     channels-first: shape [NVAR, n1, n2, n3]
//     Channel mapping: 0=RHO, 1=UU, 2=U1, 3=U2, 4=U3, 5=B1, 6=B2, 7=B3
//
// RGBA32F output packing: R=RHO, G=UU, B=U1, A=U2
// WHY this packing: matches nubhlight_pack convention so shaders/CUDA kernels
// that read channel R as rho and channel G as internal energy work unmodified.
// ---------------------------------------------------------------------------

std::shared_ptr<GRMHDTile> loadIharm3d(const std::string &path,
                                         GRMHDHdf5Info *info) {
    const HighFive::File file(path, HighFive::File::ReadOnly);

    std::size_t n1{};
    std::size_t n2{};
    std::size_t n3{};
    if (!readGridDim(file, "n1", "N1", n1) ||
        !readGridDim(file, "n2", "N2", n2) ||
        !readGridDim(file, "n3", "N3", n3)) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: missing n1/n2/n3 in " << path << "\n";
        return nullptr;
    }

    double t = 0.0;
    double gam = 4.0 / 3.0;
    tryReadAttr(file, "t", t);
    tryReadAttr(file, "gam", gam);

    if (!file.exist("prims")) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: dataset 'prims' not found in "
                  << path << "\n";
        return nullptr;
    }

    const HighFive::DataSet primsDs = file.getDataSet("prims");
    std::vector<std::size_t> dims = primsDs.getSpace().getDimensions();
    if (dims.size() != 4) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: 'prims' must be 4D, got "
                  << dims.size() << "D in " << path << "\n";
        return nullptr;
    }

    /* WHY: Detect channel layout by matching the header grid dimensions
     * (n1,n2,n3) against the dataset shape.  For channels-last the first
     * three dimensions equal (n1,n2,n3); for channels-first the last three
     * equal (n1,n2,n3).  We prefer the direct match over a size heuristic
     * so that small test grids (where NVAR >= n1) work correctly. */
    const bool tryLast  = (dims.at(0) == n1 && dims.at(1) == n2 && dims.at(2) == n3);
    const bool tryFirst = (dims.at(1) == n1 && dims.at(2) == n2 && dims.at(3) == n3);

    if (!tryLast && !tryFirst) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: spatial dims mismatch in "
                  << path << "\n";
        return nullptr;
    }

    /* Prefer channels-last (iharm3d convention); channels-first as fallback. */
    const bool channelsLast = tryLast;

    std::size_t nvar{};
    if (channelsLast) {
        nvar = dims.at(3);
    } else {
        nvar = dims.at(0);
    }

    if (nvar < 5) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: need >= 5 channels, got "
                  << nvar << " in " << path << "\n";
        return nullptr;
    }

    /* WHY: read_raw() reads the flat buffer regardless of dataset shape,
     * matching the nubhlight_pack convention.  read() fails if the target
     * std::vector does not match the dataset's multidimensional shape. */
    const std::size_t voxels = n1 * n2 * n3;
    const std::size_t expectedElems = primsDs.getSpace().getElementCount();
    if (expectedElems != voxels * nvar) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: element count mismatch in "
                  << path << "\n";
        return nullptr;
    }
    std::vector<double> raw(expectedElems);
    primsDs.read_raw(raw.data());

    if (raw.size() != voxels * nvar) {
        std::cerr << "[GRMHDHdf5Loader] iharm3d: unexpected prims size in "
                  << path << "\n";
        return nullptr;
    }

    auto tile = std::make_shared<GRMHDTile>();
    tile->width  = n1;
    tile->height = n2;
    tile->depth  = n3;
    tile->data.resize(voxels * 4, 0.0f);

    /* Pack RGBA32F: R=RHO(0), G=UU(1), B=U1(2), A=U2(3).
     * Channels 4+ (U3, B1..B3) are not stored in the tile; they are available
     * in the original HDF5 if needed for a future polarized RT path. */
    for (std::size_t k = 0; k < voxels; ++k) {
        auto chanVal = [&](std::size_t ch) -> float {
            const double v = channelsLast
                                 ? raw.at((k * nvar) + ch)
                                 : raw.at((ch * voxels) + k);
            return static_cast<float>(v);
        };
        tile->data.at((k * 4) + 0) = chanVal(0); // RHO
        tile->data.at((k * 4) + 1) = chanVal(1); // UU
        tile->data.at((k * 4) + 2) = chanVal(2); // U1
        tile->data.at((k * 4) + 3) = chanVal(3); // U2
    }

    if (info != nullptr) {
        info->code   = GRMHDCode::IHARM3D;
        info->n1     = n1;
        info->n2     = n2;
        info->n3     = n3;
        info->time   = t;
        info->gamma  = gam;
        info->fields = {"rho", "ug", "u1", "u2"};
    }

    return tile;
}

// ---------------------------------------------------------------------------
// BHAC format loader
//
// Expected structure:
//   Root attributes: n1/NX, n2/NY, n3/NZ (or N1/N2/N3), t
//   Group "Grid":    coordinate arrays (not read here)
//   Datasets at root (all 3D, shape [n1,n2,n3]):
//     "dens" = mass density (rho)
//     "ener" = internal energy density (ug)
//     "vx"   = x-velocity component (u1 proxy)
//     "vy"   = y-velocity component (u2 proxy)
//
// RGBA32F packing: R=dens, G=ener, B=vx, A=vy
// ---------------------------------------------------------------------------

std::shared_ptr<GRMHDTile> loadBhac(const std::string &path,
                                     GRMHDHdf5Info *info) {
    const HighFive::File file(path, HighFive::File::ReadOnly);

    std::size_t n1{};
    std::size_t n2{};
    std::size_t n3{};
    if (!readGridDim(file, "n1", "NX", n1) ||
        !readGridDim(file, "n2", "NY", n2) ||
        !readGridDim(file, "n3", "NZ", n3)) {
        /* Fallback: try N1/N2/N3 (some BHAC versions use uppercase) */
        if (!readGridDim(file, "N1", "NX", n1) ||
            !readGridDim(file, "N2", "NY", n2) ||
            !readGridDim(file, "N3", "NZ", n3)) {
            std::cerr << "[GRMHDHdf5Loader] BHAC: missing grid dimensions in "
                      << path << "\n";
            return nullptr;
        }
    }

    double t = 0.0;
    tryReadAttr(file, "t", t);

    /* Read scalar fields; missing fields default to zero in the tile. */
    auto readField = [&](const std::string &name) -> std::vector<double> {
        if (!file.exist(name)) {
            return {};
        }
        const HighFive::DataSet ds = file.getDataSet(name);
        const std::size_t count = ds.getSpace().getElementCount();
        std::vector<double> data(count);
        ds.read_raw(data.data());
        return data;
    };

    const std::vector<double> rho = readField("dens");
    const std::vector<double> ug  = readField("ener");
    const std::vector<double> u1  = readField("vx");
    const std::vector<double> u2  = readField("vy");

    const std::size_t voxels = n1 * n2 * n3;
    if (rho.size() < voxels) {
        std::cerr << "[GRMHDHdf5Loader] BHAC: 'dens' dataset too small in "
                  << path << "\n";
        return nullptr;
    }

    auto tile = std::make_shared<GRMHDTile>();
    tile->width  = n1;
    tile->height = n2;
    tile->depth  = n3;
    tile->data.resize(voxels * 4, 0.0f);

    for (std::size_t k = 0; k < voxels; ++k) {
        tile->data.at((k * 4) + 0) = static_cast<float>(rho.at(k));
        tile->data.at((k * 4) + 1) = (ug.size() > k) ? static_cast<float>(ug.at(k))  : 0.0f;
        tile->data.at((k * 4) + 2) = (u1.size() > k) ? static_cast<float>(u1.at(k))  : 0.0f;
        tile->data.at((k * 4) + 3) = (u2.size() > k) ? static_cast<float>(u2.at(k))  : 0.0f;
    }

    if (info != nullptr) {
        info->code   = GRMHDCode::BHAC;
        info->n1     = n1;
        info->n2     = n2;
        info->n3     = n3;
        info->time   = t;
        info->gamma  = 0.0;
        info->fields = {"dens", "ener", "vx", "vy"};
    }

    return tile;
}

} // namespace

// ---------------------------------------------------------------------------
// GRMHDHdf5Loader::detectCode
// ---------------------------------------------------------------------------

GRMHDCode GRMHDHdf5Loader::detectCode(const std::string &path) {
    try {
        const HighFive::File file(path, HighFive::File::ReadOnly);

        /* iharm3d / KORAL: identified by the "prims" primitives dataset. */
        if (file.exist("prims")) {
            return GRMHDCode::IHARM3D;
        }

        /* KORAL time-series: prims may live inside a "harm_3d" group. */
        if (file.exist("harm_3d") &&
            file.getGroup("harm_3d").exist("prims")) {
            return GRMHDCode::IHARM3D;
        }

        /* BHAC: identified by the "Grid" group and "dens" scalar dataset. */
        if (file.exist("Grid") && file.exist("dens")) {
            return GRMHDCode::BHAC;
        }

    } catch (const std::exception &e) {
        std::cerr << "[GRMHDHdf5Loader] detectCode error: " << e.what() << "\n";
    }

    return GRMHDCode::UNKNOWN;
}

// ---------------------------------------------------------------------------
// GRMHDHdf5Loader::load
// ---------------------------------------------------------------------------

std::shared_ptr<GRMHDTile> GRMHDHdf5Loader::load(const std::string &path,
                                                    GRMHDHdf5Info *info) {
    const GRMHDCode code = detectCode(path);

    switch (code) {
        case GRMHDCode::IHARM3D:
            return loadIharm3d(path, info);
        case GRMHDCode::BHAC:
            return loadBhac(path, info);
        case GRMHDCode::UNKNOWN:
            std::cerr << "[GRMHDHdf5Loader] Unrecognized HDF5 format: "
                      << path << "\n";
            return nullptr;
    }

    return nullptr;
}

} // namespace blackhole
