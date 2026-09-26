/**
 * @file kerr_disk_reference.h
 * @brief Double-precision reference for a camera ray that lands on the disk.
 *
 * The GPU tracers follow the time-reversed photon in Kerr spin -a from the
 * camera (kerrTraceSpin, d_kerr_trace_spin). traceDiskHitReference repeats
 * that trace with physics::kerrNullGeodesicFromBL and physics::kerrStepMino
 * in double and reports the Boyer-Lindquist radius where it first crosses the
 * equator and the physical photon's Lz / E = -lz of the traced ray. Inputs
 * are in the physics frame (spin along +z) and scene units with r_s = 2 M.
 *
 * makeMirrorPair places a camera on the physics +x side at (D, 0, h) M,
 * aimed at the hole, and returns the two rays tilted by atan(fovScale) toward
 * physics -y and +y. A disk orbiting in +phi moves toward that camera on its
 * -y side, so ray 0 lands on the approaching side and ray 1 on the receding
 * side.
 *
 * The header compiles as C++17 for nvcc-built tests; the implementation in
 * kerr_disk_reference.cpp carries the C++23 physics headers.
 */

#ifndef BLACKHOLE_TESTS_SUPPORT_KERR_DISK_REFERENCE_H
#define BLACKHOLE_TESTS_SUPPORT_KERR_DISK_REFERENCE_H

#include <array>

namespace bhtest {

using Vec3d = std::array<double, 3>;

struct DiskHitReference {
  bool hitDisk = false;
  double radius = 0.0; ///< Boyer-Lindquist r of the first equatorial crossing (scene units).
  double lambda = 0.0; ///< Lz / E of the physical photon reaching the camera (scene units).
};

/// Trace from cam along dir until the first equatorial crossing, capture, or
/// escape; hitDisk is true when the crossing radius lies in [rDiskIn, rDiskOut].
DiskHitReference traceDiskHitReference(const Vec3d &cam, const Vec3d &dir, double rs,
                                       double spin, double rDiskIn, double rDiskOut);

struct MirrorPair {
  Vec3d cam{};              ///< Physics-frame camera position (scene units).
  Vec3d forward{};          ///< Unit vector from the camera toward the hole.
  std::array<Vec3d, 2> dir{}; ///< [0] tilted toward -y (approaching), [1] toward +y (receding).
};

/// Camera at (distanceM, 0, heightM) * rs / 2 in the physics frame.
MirrorPair makeMirrorPair(double rs, double distanceM, double heightM, double fovScale);

} // namespace bhtest

#endif // BLACKHOLE_TESTS_SUPPORT_KERR_DISK_REFERENCE_H
