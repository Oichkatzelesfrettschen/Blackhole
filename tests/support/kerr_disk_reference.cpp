#include "support/kerr_disk_reference.h"

#include <cmath>
#include <cstddef>

#include "physics/constants.h"
#include "physics/kerr.h"

namespace bhtest {

namespace {

double dot(const Vec3d &u, const Vec3d &v) { return (u[0] * v[0]) + (u[1] * v[1]) + (u[2] * v[2]); }

Vec3d normalized(const Vec3d &v) {
  const double inv = 1.0 / std::sqrt(dot(v, v));
  return {v[0] * inv, v[1] * inv, v[2] * inv};
}

} // namespace

DiskHitReference traceDiskHitReference(const Vec3d &cam, const Vec3d &dir, double rs,
                                       double spin, double rDiskIn, double rDiskOut) {
  const double m = 0.5 * rs;
  const double mass = m * physics::C2 / physics::G;
  const double aTrace = -spin * m;

  // Boyer-Lindquist projection of the Cartesian direction, as in
  // kerrInitGeodesic.
  const double r0 = std::sqrt(dot(cam, cam));
  const double cosT = cam[2] / r0;
  const double sinT = std::sqrt(1.0 - (cosT * cosT));
  const double phi0 = std::atan2(cam[1], cam[0]);
  const double cosP = std::cos(phi0);
  const double sinP = std::sin(phi0);
  const Vec3d eR = {sinT * cosP, sinT * sinP, cosT};
  const Vec3d eTheta = {cosT * cosP, cosT * sinP, -sinT};
  const Vec3d ePhi = {-sinP, cosP, 0.0};
  const Vec3d n = normalized(dir);
  const physics::KerrNullGeodesic g =
      physics::kerrNullGeodesicFromBL(r0, std::acos(cosT), phi0, dot(n, eR), dot(n, eTheta) / r0,
                                      dot(n, ePhi) / (r0 * sinT), mass, aTrace);

  DiskHitReference out;
  out.lambda = -g.consts.lz;
  const double rPlus = m + std::sqrt((m * m) - (aTrace * aTrace));
  const double halfPi = 0.5 * physics::PI;
  physics::KerrGeodesicState s = g.state;
  // dlambda = k / r moves r by about k r per step (dr/dlambda ~ r^2 far out),
  // a scale-free step that resolves the crossing to well below 1e-6 r.
  constexpr double K_STEP = 2e-4;
  for (int step = 0; step < 10'000'000; ++step) {
    if (s.r <= 1.001 * rPlus || s.r > 1.0e3 * r0) {
      return out;
    }
    const physics::KerrGeodesicState next =
        physics::kerrStepMino(s, mass, aTrace, g.consts, K_STEP / s.r);
    const double before = s.theta - halfPi;
    const double after = next.theta - halfPi;
    if ((before > 0.0) != (after > 0.0)) {
      const double t = before / (before - after);
      out.radius = s.r + (t * (next.r - s.r));
      out.hitDisk = out.radius >= rDiskIn && out.radius <= rDiskOut;
      return out;
    }
    s = next;
  }
  return out;
}

MirrorPair makeMirrorPair(double rs, double distanceM, double heightM, double fovScale) {
  const double m = 0.5 * rs;
  MirrorPair pair;
  pair.cam = {distanceM * m, 0.0, heightM * m};
  pair.forward = normalized({-pair.cam[0], 0.0, -pair.cam[2]});
  for (int side = 0; side < 2; ++side) {
    const double y = side == 0 ? -fovScale : fovScale;
    pair.dir.at(static_cast<std::size_t>(side)) =
        normalized({pair.forward[0], y, pair.forward[2]});
  }
  return pair;
}

} // namespace bhtest
