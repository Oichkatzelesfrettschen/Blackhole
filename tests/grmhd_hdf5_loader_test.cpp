/*
 * grmhd_hdf5_loader_test.cpp
 * Unit tests for GRMHDHdf5Loader: format detection, metadata parsing,
 * data loading for iharm3d (channels-last + channels-first) and BHAC.
 *
 * WHY: GRMHDHdf5Loader is the entry point for real simulation data from
 *      iharm3d/KORAL/BHAC codes.  Failures here are silent on real datasets
 *      (wrong channel mapping, off-by-one dims) so we validate against known
 *      synthetic files with exact expected values.
 *
 * WHAT: Creates synthetic HDF5 files in /tmp using HighFive, then loads them
 *       through GRMHDHdf5Loader and asserts:
 *       1. testIharm3dChannelsLast -- basic iharm3d load (channels-last)
 *       2. testIharm3dChannelsFirst -- load with [NVAR,n1,n2,n3] layout
 *       3. testIharm3dHeaderGroup -- n1/n2/n3 in "header" group, not root
 *       4. testBhac -- BHAC scalar-field format
 *       5. testMissingFile -- nullptr returned for nonexistent path
 *       6. testUnknownFormat -- nullptr returned for unrecognized HDF5
 *
 * HOW: Assert-based (no external test framework).  Each test creates a unique
 *      /tmp file using getpid() + sequential index to avoid parallelism
 *      collisions.  Files are removed on success.
 */

#include <cassert>
#include <cstdio>
#include <iostream>
#include <string>
#include <vector>

#include <unistd.h>  // getpid

#include <highfive/H5DataSpace.hpp> // HighFive::DataSpace
#include <highfive/H5File.hpp>

#include "grmhd_hdf5_loader.h"

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

namespace {

// Grid: 4x4x4, NVAR=5 for iharm3d tests
constexpr std::size_t N1 = 4;
constexpr std::size_t N2 = 4;
constexpr std::size_t N3 = 4;
constexpr std::size_t NVAR = 5;

/** @brief Build a flat channels-last prims array: channel k set to (k+1)*10. */
std::vector<double> makePrimsChannelsLast() {
    std::vector<double> data(N1 * N2 * N3 * NVAR, 0.0);
    for (std::size_t vox = 0; vox < N1 * N2 * N3; ++vox) {
        for (std::size_t ch = 0; ch < NVAR; ++ch) {
            data.at((vox * NVAR) + ch) = static_cast<double>((ch + 1) * 10);
        }
    }
    return data;
}

/** @brief Build a flat channels-first prims array: channel k set to (k+1)*10. */
std::vector<double> makePrimsChannelsFirst() {
    std::vector<double> data(NVAR * N1 * N2 * N3, 0.0);
    for (std::size_t ch = 0; ch < NVAR; ++ch) {
        for (std::size_t vox = 0; vox < N1 * N2 * N3; ++vox) {
            data.at((ch * N1 * N2 * N3) + vox) = static_cast<double>((ch + 1) * 10);
        }
    }
    return data;
}

/** @brief Remove a file (best-effort, ignore errors). */
void removeFile(const std::string &path) {
    (void)std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

int testIharm3dChannelsLast(const std::string &path) {
    /* Create synthetic iharm3d file: channels-last [N1,N2,N3,NVAR] */
    {
        HighFive::File f(path, HighFive::File::Truncate);
        f.createAttribute("n1", static_cast<int>(N1));
        f.createAttribute("n2", static_cast<int>(N2));
        f.createAttribute("n3", static_cast<int>(N3));
        f.createAttribute("t",   1.5);
        f.createAttribute("gam", 5.0 / 3.0);

        const std::vector<double> prims = makePrimsChannelsLast();
        auto ds = f.createDataSet<double>("prims",
                      HighFive::DataSpace({N1, N2, N3, NVAR}));
        ds.write_raw(prims.data());
    }

    blackhole::GRMHDHdf5Info info;
    const auto tile = blackhole::GRMHDHdf5Loader::load(path, &info);

    if (!tile) {
        std::cerr << "FAIL testIharm3dChannelsLast: load() returned nullptr\n";
        return 1;
    }
    if (info.n1 != N1 || info.n2 != N2 || info.n3 != N3) {
        std::cerr << "FAIL testIharm3dChannelsLast: grid dims wrong\n";
        return 1;
    }
    if (info.time != 1.5) {
        std::cerr << "FAIL testIharm3dChannelsLast: time wrong (" << info.time << ")\n";
        return 1;
    }
    if (info.code != blackhole::GRMHDCode::IHARM3D) {
        std::cerr << "FAIL testIharm3dChannelsLast: code wrong\n";
        return 1;
    }
    /* Channel 0 (RHO) = 10.0 for every voxel */
    if (tile->data.at(0) != 10.0f) {
        std::cerr << "FAIL testIharm3dChannelsLast: R channel = "
                  << tile->data.at(0) << " (expected 10.0)\n";
        return 1;
    }
    /* Channel 1 (UU) = 20.0 */
    if (tile->data.at(1) != 20.0f) {
        std::cerr << "FAIL testIharm3dChannelsLast: G channel = "
                  << tile->data.at(1) << " (expected 20.0)\n";
        return 1;
    }
    /* Channel 2 (U1) = 30.0 */
    if (tile->data.at(2) != 30.0f) {
        std::cerr << "FAIL testIharm3dChannelsLast: B channel = "
                  << tile->data.at(2) << " (expected 30.0)\n";
        return 1;
    }
    /* Channel 3 (U2) = 40.0 */
    if (tile->data.at(3) != 40.0f) {
        std::cerr << "FAIL testIharm3dChannelsLast: A channel = "
                  << tile->data.at(3) << " (expected 40.0)\n";
        return 1;
    }
    if (tile->width != N1 || tile->height != N2 || tile->depth != N3) {
        std::cerr << "FAIL testIharm3dChannelsLast: tile dims wrong\n";
        return 1;
    }

    removeFile(path);
    std::cout << "PASS testIharm3dChannelsLast\n";
    return 0;
}

int testIharm3dChannelsFirst(const std::string &path) {
    /* Create iharm3d file with channels-first [NVAR, N1, N2, N3] layout */
    {
        HighFive::File f(path, HighFive::File::Truncate);
        f.createAttribute("n1", static_cast<int>(N1));
        f.createAttribute("n2", static_cast<int>(N2));
        f.createAttribute("n3", static_cast<int>(N3));
        f.createAttribute("t",   2.5);
        f.createAttribute("gam", 4.0 / 3.0);

        const std::vector<double> prims = makePrimsChannelsFirst();
        auto ds = f.createDataSet<double>("prims",
                      HighFive::DataSpace({NVAR, N1, N2, N3}));
        ds.write_raw(prims.data());
    }

    blackhole::GRMHDHdf5Info info;
    const auto tile = blackhole::GRMHDHdf5Loader::load(path, &info);

    if (!tile) {
        std::cerr << "FAIL testIharm3dChannelsFirst: load() returned nullptr\n";
        return 1;
    }
    /* Same channel values regardless of layout */
    if (tile->data.at(0) != 10.0f) {
        std::cerr << "FAIL testIharm3dChannelsFirst: R=" << tile->data.at(0)
                  << " (expected 10.0)\n";
        return 1;
    }
    if (tile->data.at(1) != 20.0f) {
        std::cerr << "FAIL testIharm3dChannelsFirst: G=" << tile->data.at(1)
                  << " (expected 20.0)\n";
        return 1;
    }

    removeFile(path);
    std::cout << "PASS testIharm3dChannelsFirst\n";
    return 0;
}

int testIharm3dHeaderGroup(const std::string &path) {
    /* n1/n2/n3 stored in "header" group, not at root */
    {
        HighFive::File f(path, HighFive::File::Truncate);
        auto hdr = f.createGroup("header");
        hdr.createAttribute("n1", static_cast<int>(N1));
        hdr.createAttribute("n2", static_cast<int>(N2));
        hdr.createAttribute("n3", static_cast<int>(N3));
        hdr.createAttribute("t",   0.0);
        hdr.createAttribute("gam", 4.0 / 3.0);

        const std::vector<double> prims = makePrimsChannelsLast();
        auto ds = f.createDataSet<double>("prims",
                      HighFive::DataSpace({N1, N2, N3, NVAR}));
        ds.write_raw(prims.data());
    }

    blackhole::GRMHDHdf5Info info;
    const auto tile = blackhole::GRMHDHdf5Loader::load(path, &info);

    if (!tile) {
        std::cerr << "FAIL testIharm3dHeaderGroup: load() returned nullptr\n";
        return 1;
    }
    if (info.n1 != N1 || info.n2 != N2 || info.n3 != N3) {
        std::cerr << "FAIL testIharm3dHeaderGroup: grid dims wrong\n";
        return 1;
    }

    removeFile(path);
    std::cout << "PASS testIharm3dHeaderGroup\n";
    return 0;
}

int testBhac(const std::string &path) {
    /* Create synthetic BHAC file: individual scalar datasets + Grid group */
    {
        HighFive::File f(path, HighFive::File::Truncate);
        f.createAttribute("n1", static_cast<int>(N1));
        f.createAttribute("n2", static_cast<int>(N2));
        f.createAttribute("n3", static_cast<int>(N3));
        f.createAttribute("t",   3.0);
        f.createGroup("Grid"); // presence triggers BHAC detection

        const std::size_t vox = N1 * N2 * N3;
        const std::vector<double> dens(vox, 5.0);
        const std::vector<double> ener(vox, 10.0);
        const std::vector<double> vx(vox, 0.1);
        const std::vector<double> vy(vox, 0.2);

        auto dsSpace = HighFive::DataSpace({N1, N2, N3});
        f.createDataSet<double>("dens", dsSpace).write_raw(dens.data());
        f.createDataSet<double>("ener", dsSpace).write_raw(ener.data());
        f.createDataSet<double>("vx",   dsSpace).write_raw(vx.data());
        f.createDataSet<double>("vy",   dsSpace).write_raw(vy.data());
    }

    blackhole::GRMHDHdf5Info info;
    const auto tile = blackhole::GRMHDHdf5Loader::load(path, &info);

    if (!tile) {
        std::cerr << "FAIL testBhac: load() returned nullptr\n";
        return 1;
    }
    if (info.code != blackhole::GRMHDCode::BHAC) {
        std::cerr << "FAIL testBhac: code != BHAC\n";
        return 1;
    }
    if (info.n1 != N1 || info.n2 != N2 || info.n3 != N3) {
        std::cerr << "FAIL testBhac: grid dims wrong\n";
        return 1;
    }
    if (tile->data.at(0) != 5.0f) {
        std::cerr << "FAIL testBhac: R (dens) = " << tile->data.at(0)
                  << " (expected 5.0)\n";
        return 1;
    }
    if (tile->data.at(1) != 10.0f) {
        std::cerr << "FAIL testBhac: G (ener) = " << tile->data.at(1)
                  << " (expected 10.0)\n";
        return 1;
    }

    removeFile(path);
    std::cout << "PASS testBhac\n";
    return 0;
}

int testMissingFile() {
    const auto tile = blackhole::GRMHDHdf5Loader::load(
        "/tmp/does_not_exist_grmhd_hdf5_42.h5");
    if (tile != nullptr) {
        std::cerr << "FAIL testMissingFile: expected nullptr, got tile\n";
        return 1;
    }
    std::cout << "PASS testMissingFile\n";
    return 0;
}

int testUnknownFormat(const std::string &path) {
    /* Create an HDF5 file with no recognizable structure */
    {
        HighFive::File f(path, HighFive::File::Truncate);
        f.createAttribute("some_attr", 42);
        const std::vector<double> data = {1.0, 2.0, 3.0};
        f.createDataSet<double>("irrelevant_dataset",
                                HighFive::DataSpace({3})).write_raw(data.data());
    }

    const auto tile = blackhole::GRMHDHdf5Loader::load(path);
    if (tile != nullptr) {
        std::cerr << "FAIL testUnknownFormat: expected nullptr for unknown format\n";
        removeFile(path);
        return 1;
    }

    removeFile(path);
    std::cout << "PASS testUnknownFormat\n";
    return 0;
}

} // namespace

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; HDF5 exceptions propagate to crash with useful messages
int main() {
    const std::string base = "/tmp/grmhd_hdf5_test_" + std::to_string(getpid());

    int failures = 0;
    failures += testIharm3dChannelsLast(base + "_cl.h5");
    failures += testIharm3dChannelsFirst(base + "_cf.h5");
    failures += testIharm3dHeaderGroup(base + "_hg.h5");
    failures += testBhac(base + "_bhac.h5");
    failures += testMissingFile();
    failures += testUnknownFormat(base + "_unk.h5");

    if (failures == 0) {
        std::cout << "All grmhd_hdf5_loader tests passed.\n";
        return 0;
    }
    std::cerr << failures << " test(s) failed.\n";
    return 1;
}
