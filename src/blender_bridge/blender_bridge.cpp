/**
 * @file blender_bridge.cpp
 * @brief Implementation of the C-linkage Blender bridge API.
 *
 * WHY: Wrap the C++ physics:: namespace into a flat C ABI for ctypes.
 * WHAT: Each bhb_* function delegates to the corresponding physics:: call
 *       with unit conversions between geometric units and CGS.
 * HOW: Compiled as part of libblackhole_bridge.so (SHARED library).
 */

#include "blender_bridge.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstring>
#include <numbers>

#include "../physics/constants.h"
#include "../physics/doppler.h"
#include "../physics/gravitational_waves.h"
#include "../physics/kerr.h"
#include "../physics/novikov_thorne.h"
#include "../physics/source_presets.h"
#include "../physics/synchrotron.h"
#include "../physics/thin_disk.h"

namespace {
/* Geometric unit helpers: convert between r_g-normalized and CGS. */
constexpr double K_REFERENCE_MASS_MSUN = 1.0;

/** @brief Return the gravitational radius r_g = GM/c^2 [cm] for a mass in solar masses. */
double rGFromMsun(double msun) {
  return physics::G * msun * physics::M_SUN / physics::C2;
}
} // namespace

/* ========================================================================
 * Version / capability
 * ======================================================================== */

int bhbVersionMajor(void) {
  return 1;
}
int bhbVersionMinor(void) {
  return 0;
}

int bhbHasCuda(void) {
#ifdef BLACKHOLE_HAS_CUDA
  return 1;
#else
  return 0;
#endif
}

int bhbHasBoost(void) {
#ifdef PHYSICS_HAS_BOOST_BESSEL
  return 1;
#else
  return 0;
#endif
}

int bhbSizeofSourceParams(void) {
  return static_cast<int>(sizeof(struct BhbSourceParams));
}

int bhbSizeofDiskParams(void) {
  return static_cast<int>(sizeof(struct BhbDiskParams));
}

/* ========================================================================
 * Source presets
 * ======================================================================== */

void bhbPresetM87(struct BhbSourceParams *out) {
  auto src = physics::sourceM87();
  *out = BhbSourceParams{};
  std::strncpy(out->name, src.name.c_str(), sizeof(out->name) - 1);
  out->massMsun = src.massMsun;
  out->spin = src.spin;
  out->distanceCm = src.distanceCm;
  out->inclinationDeg = src.inclinationDeg;
  out->freqHz = src.freqHz;
  out->rGCm = src.rG();
  out->shadowUas = src.shadowDiameterUas();
}

void bhbPresetSgra(struct BhbSourceParams *out) {
  auto src = physics::sourceSgra();
  *out = BhbSourceParams{};
  std::strncpy(out->name, src.name.c_str(), sizeof(out->name) - 1);
  out->massMsun = src.massMsun;
  out->spin = src.spin;
  out->distanceCm = src.distanceCm;
  out->inclinationDeg = src.inclinationDeg;
  out->freqHz = src.freqHz;
  out->rGCm = src.rG();
  out->shadowUas = src.shadowDiameterUas();
}

/* ========================================================================
 * Kerr metric (geometric units: M = 1, so r_g = 1)
 * ======================================================================== */

namespace {
/* Internal: use a 1-solar-mass BH for unit conversion, then normalize. */
constexpr double K_UNIT_MASS = 1.9885e33; /* 1 M_sun in grams */

/**
 * @brief Convert dimensionless spin a* to physical spin [cm] for the unit-mass BH.
 *
 * All bhbKerr* functions call physics:: with physical units then divide back
 * by the geometric mass M = G*M_unit/c^2 to recover dimensionless r_g ratios.
 */
double unitSpin(double aStar) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  return aStar * mGeom;
}
} // namespace

double bhbKerrOuterHorizon(double aStar) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::kerrOuterHorizon(K_UNIT_MASS, a) / mGeom;
}

double bhbKerrInnerHorizon(double aStar) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::kerrInnerHorizon(K_UNIT_MASS, a) / mGeom;
}

double bhbKerrErgosphere(double aStar, double thetaRad) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::ergosphereRadius(K_UNIT_MASS, a, thetaRad) / mGeom;
}

double bhbKerrIsco(double aStar, int prograde) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::kerrIscoRadius(K_UNIT_MASS, a, prograde != 0) / mGeom;
}

double bhbKerrPhotonOrbitPrograde(double aStar) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::kerrPhotonOrbitPrograde(K_UNIT_MASS, a) / mGeom;
}

double bhbKerrPhotonOrbitRetrograde(double aStar) {
  double const mGeom = physics::G * K_UNIT_MASS / physics::C2;
  double const a = unitSpin(aStar);
  return physics::kerrPhotonOrbitRetrograde(K_UNIT_MASS, a) / mGeom;
}

double bhbKerrSigma(double rRg, double aStar, double thetaRad) {
  /* Sigma / M^2 = (r/M)^2 + a*^2 cos^2(theta) */
  double const ct = std::cos(thetaRad);
  return (rRg * rRg) + (aStar * aStar * ct * ct);
}

double bhbKerrDelta(double rRg, double aStar) {
  /* Delta / M^2 = (r/M)^2 - 2(r/M) + a*^2 */
  return (rRg * rRg) - (2.0 * rRg) + (aStar * aStar);
}

/* ========================================================================
 * Geodesic tracing (CPU RK4)
 * ======================================================================== */

namespace {
/* Kerr geodesic RK4 in Boyer-Lindquist coordinates (equatorial, null).
 * Uses the effective potential approach for equatorial photons.
 * Coordinates: (t, r, theta=pi/2, phi) with affine parameter lambda. */

/**
 * @brief Phase-space state for a single equatorial null geodesic in Boyer-Lindquist coordinates.
 *
 * Only the equatorial slice (theta = pi/2) is represented; Q = 0 (Carter constant).
 */
struct KerrState {
  double r, phi, pr, pphi;
};

/**
 * @brief Evaluate the Hamilton-Jacobi equations of motion for an equatorial Kerr null geodesic.
 *
 * Fills @p ds with derivatives (dr/dlambda, dphi/dlambda, dpr/dlambda, dpphi/dlambda).
 *
 * @param aStar Dimensionless spin.
 * @param b     Impact parameter (conserved angular momentum with E = 1).
 * @param s     Current state.
 * @param ds    Output: derivatives at @p s.
 */
void kerrEquatorial(double aStar, double b, const KerrState &s, KerrState &ds) {
  double const r = s.r;
  double const r2 = r * r;
  double const a2 = aStar * aStar;
  double const delta = r2 - (2.0 * r) + a2;
  double const sigma = r2; /* equatorial: theta = pi/2, cos(theta) = 0 */

  /* Conserved quantities for null geodesic with E=1: L = b */
  double const l = b;

  /* Hamilton-Jacobi separated equations (equatorial, Q=0): */
  double const p = r2 + a2 - (aStar * l);

  ds.r = s.pr * delta / sigma;
  ds.phi = ((aStar * p / delta) - aStar + l) / sigma;
  ds.pr = -((r * s.pr * s.pr * ((2.0 * r) - 2.0) / (2.0 * sigma)) -
            (((2.0 * r * p) - (((2.0 * r) - 2.0) * (p * p / delta))) / (sigma * delta)) +
            (2.0 * r * s.pr * s.pr / sigma));
  ds.pphi = 0.0;
}

/**
 * @brief Advance the geodesic state by one classical fourth-order Runge-Kutta step.
 *
 * @param aStar Dimensionless spin.
 * @param b     Impact parameter.
 * @param s     State to update in-place.
 * @param h     Affine parameter step size.
 */
void rk4Step(double aStar, double b, KerrState &s, double h) {
  KerrState k1{};
  KerrState k2{};
  KerrState k3{};
  KerrState k4{};
  KerrState tmp{};

  kerrEquatorial(aStar, b, s, k1);

  tmp.r = s.r + (0.5 * h * k1.r);
  tmp.phi = s.phi + (0.5 * h * k1.phi);
  tmp.pr = s.pr + (0.5 * h * k1.pr);
  tmp.pphi = s.pphi + (0.5 * h * k1.pphi);
  kerrEquatorial(aStar, b, tmp, k2);

  tmp.r = s.r + (0.5 * h * k2.r);
  tmp.phi = s.phi + (0.5 * h * k2.phi);
  tmp.pr = s.pr + (0.5 * h * k2.pr);
  tmp.pphi = s.pphi + (0.5 * h * k2.pphi);
  kerrEquatorial(aStar, b, tmp, k3);

  tmp.r = s.r + (h * k3.r);
  tmp.phi = s.phi + (h * k3.phi);
  tmp.pr = s.pr + (h * k3.pr);
  tmp.pphi = s.pphi + (h * k3.pphi);
  kerrEquatorial(aStar, b, tmp, k4);

  s.r += h * (k1.r + (2.0 * k2.r) + (2.0 * k3.r) + k4.r) / 6.0;
  s.phi += h * (k1.phi + (2.0 * k2.phi) + (2.0 * k3.phi) + k4.phi) / 6.0;
  s.pr += h * (k1.pr + (2.0 * k2.pr) + (2.0 * k3.pr) + k4.pr) / 6.0;
  s.pphi += h * (k1.pphi + (2.0 * k2.pphi) + (2.0 * k3.pphi) + k4.pphi) / 6.0;
}
} // namespace

int bhbTraceGeodesicsEquatorial(double aStar, double observerRRg, double bMin, double bMax,
                                int nRays, int maxSteps, double stepSize, float *outXyz,
                                int *outCounts) {
  if ((outXyz == nullptr) || (outCounts == nullptr) || nRays <= 0 || maxSteps <= 0) {
    return -1;
  }

  double const rHorizon = bhbKerrOuterHorizon(aStar);

  for (int i = 0; i < nRays; ++i) {
    double const b = (nRays > 1) ? bMin + ((bMax - bMin) * static_cast<double>(i) / (nRays - 1))
                                 : (bMin + bMax) * 0.5;

    /* Initialize: photon at observer, moving inward. */
    KerrState state{};
    state.r = observerRRg;
    state.phi = 0.0;
    /* Initial radial momentum from impact parameter: pr ~ -sqrt(1 - b^2/r^2) */
    double const bOverR = b / observerRRg;
    state.pr = -std::sqrt(std::max(0.0, 1.0 - (bOverR * bOverR)));
    state.pphi = 0.0;

    float *rayOut = outXyz + (static_cast<ptrdiff_t>(i) * maxSteps * 3);
    int count = 0;

    for (int step = 0; step < maxSteps; ++step) {
      /* BL (r, phi) -> Cartesian (x, y, z=0 for equatorial) */
      double const x = state.r * std::cos(state.phi);
      double const y = state.r * std::sin(state.phi);

      rayOut[(count * 3) + 0] = static_cast<float>(x);
      rayOut[(count * 3) + 1] = static_cast<float>(y);
      rayOut[(count * 3) + 2] = 0.0f;
      ++count;

      rk4Step(aStar, b, state, stepSize);

      /* Stop if fallen into horizon or escaped */
      if (state.r < rHorizon * 1.01 || state.r > observerRRg * 3.0) {
        break;
      }
    }

    outCounts[i] = count;
  }

  return 0;
}

int bhbTraceGeodesicsImagePlane(double aStar, double observerRRg, double inclinationRad,
                                double alphaMin, double alphaMax, int nAlpha, double betaMin,
                                double betaMax, int nBeta, int maxSteps, double stepSize,
                                float *outXyz, int *outCounts) {
  if ((outXyz == nullptr) || (outCounts == nullptr)) {
    return -1;
  }

  double const rHorizon = bhbKerrOuterHorizon(aStar);
  double const cosInc = std::cos(inclinationRad);
  double const sinInc = std::sin(inclinationRad);

  for (int ib = 0; ib < nBeta; ++ib) {
    double const beta =
        (nBeta > 1) ? betaMin + ((betaMax - betaMin) * static_cast<double>(ib) / (nBeta - 1))
                    : (betaMin + betaMax) * 0.5;
    for (int ia = 0; ia < nAlpha; ++ia) {
      double const alpha =
          (nAlpha > 1) ? alphaMin + ((alphaMax - alphaMin) * static_cast<double>(ia) / (nAlpha - 1))
                       : (alphaMin + alphaMax) * 0.5;

      int const idx = (ib * nAlpha) + ia;
      float *rayOut = outXyz + (static_cast<ptrdiff_t>(idx) * maxSteps * 3);

      /* Impact parameters from image plane coords */
      double b = std::sqrt((alpha * alpha) + (beta * beta));
      b = std::max(b, 1e-10);

      KerrState state{};
      state.r = observerRRg;
      state.phi = std::atan2(alpha, observerRRg);

      double const bOverR = b / observerRRg;
      state.pr = -std::sqrt(std::max(0.0, 1.0 - (bOverR * bOverR)));

      int count = 0;
      for (int step = 0; step < maxSteps; ++step) {
        /* 3D position accounting for inclination */
        double const x = state.r * std::cos(state.phi);
        double const y = state.r * std::sin(state.phi) * cosInc;
        double const z = state.r * std::sin(state.phi) * sinInc;

        rayOut[(count * 3) + 0] = static_cast<float>(x);
        rayOut[(count * 3) + 1] = static_cast<float>(y);
        rayOut[(count * 3) + 2] = static_cast<float>(z);
        ++count;

        rk4Step(aStar, b, state, stepSize);

        if (state.r < rHorizon * 1.01 || state.r > observerRRg * 3.0) {
          break;
        }
      }

      outCounts[idx] = count;
    }
  }

  return 0;
}

/* ========================================================================
 * Accretion disk mesh
 * ======================================================================== */

int bhbGenerateDiskMesh(const struct BhbDiskParams *params, int nRadial, int nAzimuthal,
                        float *outPos, float *outNormals, float *outTemp, float *outUvs,
                        int *outIndices, int *outVertexCount, int *outIndexCount) {
  if ((params == nullptr) || nRadial < 2 || nAzimuthal < 3) {
    return -1;
  }

  double const massCgs = params->massMsun * physics::M_SUN;
  double const rG = physics::G * massCgs / physics::C2;
  double const aStar = params->aStar;
  double const rInRg = bhbKerrIsco(aStar, 1); /* ISCO in r_g */
  double const rOutRg = params->rOutRg;
  double const inc = params->inclinationRad;

  /* Eddington luminosity and accretion rate */
  double const lEdd = 1.26e38 * params->massMsun;
  double eta = bhbNtRadiativeEfficiency(aStar);
  eta = std::max(eta, 0.01);
  double const mDotCgs = params->mdotEdd * lEdd / (eta * physics::C2);

  int const nVerts = nRadial * nAzimuthal;
  int const nTris = 2 * (nRadial - 1) * nAzimuthal;

  double const cosInc = std::cos(inc);
  double const sinInc = std::sin(inc);

  for (int ir = 0; ir < nRadial; ++ir) {
    double const t = static_cast<double>(ir) / (nRadial - 1);
    double const rRg = rInRg + ((rOutRg - rInRg) * t);
    double const rCm = rRg * rG;

    /* Novikov-Thorne temperature (simplified Schwarzschild approx) */
    double const rRatio = rInRg * rG / rCm;
    double flux = (3.0 * physics::G * massCgs * mDotCgs) /
                  (8.0 * std::numbers::pi * rCm * rCm * rCm) * (1.0 - std::sqrt(rRatio));
    flux = std::max(flux, 0.0);
    double const temp = std::pow(flux / physics::STEFAN_BOLTZMANN, 0.25);

    for (int ia = 0; ia < nAzimuthal; ++ia) {
      double const phi = 2.0 * std::numbers::pi * static_cast<double>(ia) / nAzimuthal;

      int const vi = (ir * nAzimuthal) + ia;

      /* Position in BL -> Cartesian with inclination */
      double const x = rRg * std::cos(phi);
      double const yFlat = rRg * std::sin(phi);
      double const y = yFlat * cosInc;
      double const z = yFlat * sinInc;

      if (outPos != nullptr) {
        outPos[(vi * 3) + 0] = static_cast<float>(x);
        outPos[(vi * 3) + 1] = static_cast<float>(y);
        outPos[(vi * 3) + 2] = static_cast<float>(z);
      }
      if (outNormals != nullptr) {
        /* Normal is tilted by inclination */
        outNormals[(vi * 3) + 0] = 0.0f;
        outNormals[(vi * 3) + 1] = static_cast<float>(-sinInc);
        outNormals[(vi * 3) + 2] = static_cast<float>(cosInc);
      }
      if (outTemp != nullptr) {
        outTemp[vi] = static_cast<float>(temp);
      }
      if (outUvs != nullptr) {
        outUvs[(vi * 2) + 0] = static_cast<float>(t);
        outUvs[(vi * 2) + 1] = static_cast<float>(phi / (2.0 * std::numbers::pi));
      }
    }
  }

  /* Triangle indices (quad strip around each ring) */
  if (outIndices != nullptr) {
    int idx = 0;
    for (int ir = 0; ir < nRadial - 1; ++ir) {
      for (int ia = 0; ia < nAzimuthal; ++ia) {
        int const iaN = (ia + 1) % nAzimuthal;
        int const v00 = (ir * nAzimuthal) + ia;
        int const v01 = (ir * nAzimuthal) + iaN;
        int const v10 = ((ir + 1) * nAzimuthal) + ia;
        int const v11 = ((ir + 1) * nAzimuthal) + iaN;

        outIndices[idx++] = v00;
        outIndices[idx++] = v10;
        outIndices[idx++] = v11;

        outIndices[idx++] = v00;
        outIndices[idx++] = v11;
        outIndices[idx++] = v01;
      }
    }
  }

  if (outVertexCount != nullptr) {
    *outVertexCount = nVerts;
  }
  if (outIndexCount != nullptr) {
    *outIndexCount = nTris * 3;
  }

  return 0;
}

/* ========================================================================
 * Novikov-Thorne
 * ======================================================================== */

double bhbNtRadiativeEfficiency(double aStar) {
  return blackhole::physics::NovikovThorneDisk::radiativeEfficiency(aStar);
}

double bhbNtIscoRadius(double aStar) {
  /* Return in units of M (geometric r_g) */
  return bhbKerrIsco(aStar, 1);
}

int bhbNtTemperatureProfile(double aStar, double massMsun, double mdotEdd, const double *rValues,
                            int n, double *outTemp, double *outFlux) {
  if ((rValues == nullptr) || n <= 0) {
    return -1;
  }

  double const massCgs = massMsun * physics::M_SUN;
  double const rG = physics::G * massCgs / physics::C2;
  double eta = bhbNtRadiativeEfficiency(aStar);
  eta = std::max(eta, 0.01);
  double const lEdd = 1.26e38 * massMsun;
  double const mDotCgs = mdotEdd * lEdd / (eta * physics::C2);
  double const rIscoRg = bhbKerrIsco(aStar, 1);
  double const rIscoCm = rIscoRg * rG;

  for (int i = 0; i < n; ++i) {
    double const rCm = rValues[i] * rG;
    if (rCm <= rIscoCm) {
      if (outTemp != nullptr) {
        outTemp[i] = 0.0;
      }
      if (outFlux != nullptr) {
        outFlux[i] = 0.0;
      }
      continue;
    }
    double flux = (3.0 * physics::G * massCgs * mDotCgs) /
                  (8.0 * std::numbers::pi * rCm * rCm * rCm) * (1.0 - std::sqrt(rIscoCm / rCm));
    flux = std::max(flux, 0.0);

    if (outFlux != nullptr) {
      outFlux[i] = flux;
    }
    if (outTemp != nullptr) {
      outTemp[i] = std::pow(flux / physics::STEFAN_BOLTZMANN, 0.25);
    }
  }

  return 0;
}

/* ========================================================================
 * Doppler
 * ======================================================================== */

double bhbLorentzFactor(double beta) {
  return physics::lorentzFactor(beta);
}

double bhbDopplerFactor(double beta, double cosTheta) {
  double const gamma = physics::lorentzFactor(beta);
  return 1.0 / (gamma * (1.0 - (beta * cosTheta)));
}

double bhbBeamingFlux(double delta, double alphaSpectral) {
  return std::pow(delta, 3.0 + alphaSpectral);
}

/* ========================================================================
 * Synchrotron
 * ======================================================================== */

double bhbSynchrotronGyrofreq(double bGauss) {
  return physics::gyrofrequency(bGauss);
}

double bhbSynchrotronCriticalFreq(double bGauss, double gamma) {
  return physics::synchrotronFrequencyCritical(gamma, bGauss);
}

double bhbSynchrotronPower(double bGauss, double gamma) {
  return physics::synchrotronPowerSingleElectron(gamma, bGauss);
}

double bhbSynchrotronCoolingTime(double bGauss, double gamma) {
  return physics::synchrotronCoolingTime(gamma, bGauss);
}

/* ========================================================================
 * Texture generation (CPU)
 * ======================================================================== */

int bhbRenderLensingMap(double aStar, double observerRRg, double inclinationRad, int width,
                        int height, float *outRgba) {
  if ((outRgba == nullptr) || width <= 0 || height <= 0) {
    return -1;
  }

  double const rHorizon = bhbKerrOuterHorizon(aStar);
  double const fov = 30.0; /* r_g extent of the image plane */

  for (int iy = 0; iy < height; ++iy) {
    double const beta = fov * (0.5 - (static_cast<double>(iy) / height));
    for (int ix = 0; ix < width; ++ix) {
      double const alpha = fov * ((static_cast<double>(ix) / width) - 0.5);

      double b = std::sqrt((alpha * alpha) + (beta * beta));
      b = std::max(b, 1e-10);

      /* Trace a single ray to get landing position */
      KerrState state{};
      state.r = observerRRg;
      state.phi = 0.0;
      double const bOverR = b / observerRRg;
      state.pr = -std::sqrt(std::max(0.0, 1.0 - (bOverR * bOverR)));

      double const step = 0.05;
      int hitDisk = 0;
      double finalR = state.r;

      for (int s = 0; s < 2000; ++s) {
        rk4Step(aStar, b, state, step);
        if (state.r < rHorizon * 1.01) {
          finalR = 0.0;
          break;
        }
        if (state.r > observerRRg * 3.0) {
          finalR = state.r;
          break;
        }

        /* Check equatorial plane crossing (simplified) */
        double const rIsco = bhbKerrIsco(aStar, 1);
        if (state.r > rIsco && state.r < 100.0) {
          hitDisk = 1;
        }
        finalR = state.r;
      }

      /* Gravitational redshift: 1 + z ~ sqrt(1 - 2M/r) */
      double const redshift = (finalR > 2.0) ? std::sqrt(1.0 - (2.0 / finalR)) : 0.0;

      /* Doppler (simplified circular orbit) */
      double doppler = 1.0;
      if ((hitDisk != 0) && finalR > 3.0) {
        double const vOrb = 1.0 / std::sqrt(finalR);
        double const cosPhi = std::cos(state.phi);
        doppler = bhbDopplerFactor(vOrb, cosPhi * std::sin(inclinationRad));
      }

      int const pi = ((iy * width) + ix) * 4;
      outRgba[pi + 0] = static_cast<float>(redshift);
      outRgba[pi + 1] = static_cast<float>(doppler);
      outRgba[pi + 2] = static_cast<float>(hitDisk);
      outRgba[pi + 3] = 1.0f;
    }
  }

  return 0;
}

int bhbRenderDiskTexture(const struct BhbDiskParams *params, int width, int height,
                         float *outRgba) {
  if ((params == nullptr) || (outRgba == nullptr) || width <= 0 || height <= 0) {
    return -1;
  }

  double const rIsco = bhbKerrIsco(params->aStar, 1);
  double const rOut = params->rOutRg;

  /* Compute max temperature for normalization */
  double maxTemp = 0.0;
  for (int i = 0; i < 100; ++i) {
    double const rRg = rIsco + ((rOut - rIsco) * (i + 1.0) / 100.0);
    double temp = 0.0;
    bhbNtTemperatureProfile(params->aStar, params->massMsun, params->mdotEdd, &rRg, 1, &temp,
                            nullptr);
    maxTemp = std::max(temp, maxTemp);
  }
  maxTemp = std::max(maxTemp, 1.0);

  for (int iy = 0; iy < height; ++iy) {
    double const v = static_cast<double>(iy) / height;
    double const rRg = rIsco + ((rOut - rIsco) * v);

    double temp = 0.0;
    bhbNtTemperatureProfile(params->aStar, params->massMsun, params->mdotEdd, &rRg, 1, &temp,
                            nullptr);
    double const tNorm = temp / maxTemp;

    /* Simplified blackbody color from temperature */
    /* Hot = blue-white, cool = red-orange */
    double const r = std::min(1.0, tNorm * 2.0);
    double const g = std::min(1.0, std::max(0.0, (tNorm * 3.0) - 0.5));
    double const b = std::min(1.0, std::max(0.0, (tNorm * 4.0) - 1.5));

    for (int ix = 0; ix < width; ++ix) {
      double const u = static_cast<double>(ix) / width;
      /* Modulate by azimuthal angle for Doppler pattern */
      double const phi = u * 2.0 * std::numbers::pi;
      double const vOrb = (rRg > 3.0) ? 1.0 / std::sqrt(rRg) : 0.0;
      double const dopplerMod =
          1.0 + (0.5 * vOrb * std::sin(phi) * std::sin(params->inclinationRad));

      int const pi = ((iy * width) + ix) * 4;
      outRgba[pi + 0] = static_cast<float>(r * dopplerMod);
      outRgba[pi + 1] = static_cast<float>(g * dopplerMod);
      outRgba[pi + 2] = static_cast<float>(b * dopplerMod);
      outRgba[pi + 3] = static_cast<float>(tNorm);
    }
  }

  return 0;
}

/* ========================================================================
 * CUDA-accelerated paths
 *
 * WHY: Blender's rendering callbacks run on the render thread; GPU acceleration
 *      reduces texture generation latency from seconds (CPU) to milliseconds.
 * WHAT: bhbCudaRenderLensingMap and bhbCudaRenderDiskTexture delegate to
 *       CUDA kernels in cuda_renderer.cu when built with ENABLE_CUDA=ON.
 *       bhbCudaTraceGeodesics returns -1 (not implemented: per-step path
 *       storage requires a different kernel design than the framebuffer path).
 * ======================================================================== */

/* bhbCudaTraceGeodesics: not yet implemented -- per-ray path storage would
 * require nRays * maxSteps * 3 floats of device memory and a separate
 * path-tracing kernel.  Return -1 so callers fall back to the CPU path. */
int bhbCudaTraceGeodesics(double /*unused*/, double /*unused*/, double /*unused*/,
                          double /*unused*/, double /*unused*/, int /*unused*/, double /*unused*/,
                          double /*unused*/, int /*unused*/, int /*unused*/, double /*unused*/,
                          float * /*unused*/, int * /*unused*/) {
  return -1;
}

#ifdef BLACKHOLE_HAS_CUDA

/* Forward declarations for cuda_renderer.cu host wrappers */
extern "C" {
int bhb_cuda_render_lensing_map(float a_star, float obs_r, float inc_rad,
                                 int width, int height, float *out_rgba);
int bhb_cuda_render_disk_texture(float a_star, float r_out_rg, float inc_rad,
                                  int width, int height, float *out_rgba);
int bhb_cuda_render_raytraced(float spin, float observer_r, float inclination_rad,
                               int width, int height, float *out_rgba);
int bhb_cuda_render_raytraced_camera(float spin, float observer_r, float inclination_rad,
                                      float fov_scale, int width, int height, float *out_rgba);
int bhb_cuda_render_raytraced_view(float spin, const float *cam_pos, const float *cam_basis,
                                    float fov_scale, int width, int height, float *out_rgba);
int bhb_cuda_reset_device_impl(void);
}

int bhbCudaRenderLensingMap(double aStar, double observerRRg, double inclinationRad,
                             int width, int height, float *outRgba) {
  return bhb_cuda_render_lensing_map(static_cast<float>(aStar),
                                      static_cast<float>(observerRRg),
                                      static_cast<float>(inclinationRad),
                                      width, height, outRgba);
}

int bhbCudaRenderDiskTexture(const struct BhbDiskParams *params, int width, int height,
                              float *outRgba) {
  if (params == nullptr) { return -1; }
  return bhb_cuda_render_disk_texture(static_cast<float>(params->aStar),
                                       static_cast<float>(params->rOutRg),
                                       static_cast<float>(params->inclinationRad),
                                       width, height, outRgba);
}

int bhbCudaRenderRaytraced(float spin, float observerR, float inclinationRad,
                            int width, int height, float *outRgba) {
  return bhb_cuda_render_raytraced(spin, observerR, inclinationRad, width, height, outRgba);
}

int bhbCudaRenderRaytracedCamera(float spin, float observerR, float inclinationRad, float fovScale,
                                 int width, int height, float *outRgba) {
  return bhb_cuda_render_raytraced_camera(
      spin,
      observerR,
      inclinationRad,
      fovScale,
      width,
      height,
      outRgba);
}

int bhbCudaRenderRaytracedView(float spin, const float *camPos, const float *camBasis,
                               float fovScale, int width, int height, float *outRgba) {
  return bhb_cuda_render_raytraced_view(
      spin,
      camPos,
      camBasis,
      fovScale,
      width,
      height,
      outRgba);
}

int bhbCudaResetDevice(void) {
  return bhb_cuda_reset_device_impl();
}

#else /* !BLACKHOLE_HAS_CUDA */

int bhbCudaRenderLensingMap(double /*unused*/, double /*unused*/, double /*unused*/,
                             int /*unused*/, int /*unused*/, float * /*unused*/) {
  return -1;
}

int bhbCudaRenderDiskTexture(const struct BhbDiskParams * /*unused*/, int /*unused*/,
                              int /*unused*/, float * /*unused*/) {
  return -1;
}

/* Stub for ray-traced renderer when CUDA is not available. */
int bhbCudaRenderRaytraced(float /*spin*/, float /*observerR*/, float /*inclinationRad*/,
                            int /*width*/, int /*height*/, float * /*outRgba*/) {
  return -1;
}

int bhbCudaResetDevice(void) {
  return 0;
}

#endif /* BLACKHOLE_HAS_CUDA */

/* ========================================================================
 * Horizon / ergosphere meshes
 * ======================================================================== */

int bhbGenerateHorizonMesh(double aStar, int nTheta, int nPhi, float *outPos, int *outIndices,
                           int *outVertexCount, int *outIndexCount) {
  if (nTheta < 2 || nPhi < 3) {
    return -1;
  }

  double const rPlus = bhbKerrOuterHorizon(aStar);

  int const nVerts = nTheta * nPhi;
  for (int it = 0; it < nTheta; ++it) {
    double const theta = std::numbers::pi * static_cast<double>(it) / (nTheta - 1);
    /* Kerr horizon is an oblate spheroid in BL coords:
     * r = r_+ is constant, but the embedding in 3D uses
     * the BL->Cartesian map with the Kerr oblate geometry. */
    double const rEmbed =
        std::sqrt((rPlus * rPlus) + (aStar * aStar * std::sin(theta) * std::sin(theta)));

    for (int ip = 0; ip < nPhi; ++ip) {
      double const phi = 2.0 * std::numbers::pi * static_cast<double>(ip) / nPhi;
      int const vi = (it * nPhi) + ip;
      if (outPos != nullptr) {
        double const x = rEmbed * std::sin(theta) * std::cos(phi);
        double const y = rEmbed * std::sin(theta) * std::sin(phi);
        double const z = rPlus * std::cos(theta);
        outPos[(vi * 3) + 0] = static_cast<float>(x);
        outPos[(vi * 3) + 1] = static_cast<float>(y);
        outPos[(vi * 3) + 2] = static_cast<float>(z);
      }
    }
  }

  /* Triangulate */
  if (outIndices != nullptr) {
    int idx = 0;
    for (int it = 0; it < nTheta - 1; ++it) {
      for (int ip = 0; ip < nPhi; ++ip) {
        int const ipN = (ip + 1) % nPhi;
        int const v00 = (it * nPhi) + ip;
        int const v01 = (it * nPhi) + ipN;
        int const v10 = ((it + 1) * nPhi) + ip;
        int const v11 = ((it + 1) * nPhi) + ipN;
        outIndices[idx++] = v00;
        outIndices[idx++] = v10;
        outIndices[idx++] = v11;
        outIndices[idx++] = v00;
        outIndices[idx++] = v11;
        outIndices[idx++] = v01;
      }
    }
  }

  if (outVertexCount != nullptr) {
    *outVertexCount = nVerts;
  }
  if (outIndexCount != nullptr) {
    *outIndexCount = 2 * (nTheta - 1) * nPhi * 3;
  }

  return 0;
}

int bhbGenerateErgosphereMesh(double aStar, int nTheta, int nPhi, float *outPos, int *outIndices,
                              int *outVertexCount, int *outIndexCount) {
  if (nTheta < 2 || nPhi < 3) {
    return -1;
  }

  int const nVerts = nTheta * nPhi;
  for (int it = 0; it < nTheta; ++it) {
    double const theta = std::numbers::pi * static_cast<double>(it) / (nTheta - 1);
    double const rErgo = bhbKerrErgosphere(aStar, theta);

    for (int ip = 0; ip < nPhi; ++ip) {
      double const phi = 2.0 * std::numbers::pi * static_cast<double>(ip) / nPhi;
      int const vi = (it * nPhi) + ip;
      if (outPos != nullptr) {
        double const x = rErgo * std::sin(theta) * std::cos(phi);
        double const y = rErgo * std::sin(theta) * std::sin(phi);
        double const z = rErgo * std::cos(theta);
        outPos[(vi * 3) + 0] = static_cast<float>(x);
        outPos[(vi * 3) + 1] = static_cast<float>(y);
        outPos[(vi * 3) + 2] = static_cast<float>(z);
      }
    }
  }

  if (outIndices != nullptr) {
    int idx = 0;
    for (int it = 0; it < nTheta - 1; ++it) {
      for (int ip = 0; ip < nPhi; ++ip) {
        int const ipN = (ip + 1) % nPhi;
        int const v00 = (it * nPhi) + ip;
        int const v01 = (it * nPhi) + ipN;
        int const v10 = ((it + 1) * nPhi) + ip;
        int const v11 = ((it + 1) * nPhi) + ipN;
        outIndices[idx++] = v00;
        outIndices[idx++] = v10;
        outIndices[idx++] = v11;
        outIndices[idx++] = v00;
        outIndices[idx++] = v11;
        outIndices[idx++] = v01;
      }
    }
  }

  if (outVertexCount != nullptr) {
    *outVertexCount = nVerts;
  }
  if (outIndexCount != nullptr) {
    *outIndexCount = 2 * (nTheta - 1) * nPhi * 3;
  }

  return 0;
}

/* ========================================================================
 * Gravitational wave inspiral waveform
 * ======================================================================== */

int bhbGWInspiral(double m1Msun, double m2Msun, double a1Star, double a2Star, double distMpc,
                  double incRad, double fLowHz, double fHighHz, double dtSec, double *outBuf,
                  int maxPoints) {
  if ((outBuf == nullptr) || maxPoints <= 0 || m1Msun <= 0.0 || m2Msun <= 0.0 ||
      distMpc <= 0.0 || fLowHz <= 0.0 || fHighHz <= fLowHz || dtSec <= 0.0) {
    return -1;
  }

  /* bbhSystem handles all CGS conversions (masses, spins, distance). */
  physics::BinarySystem binary = physics::bbhSystem(m1Msun, m2Msun, a1Star, a2Star, distMpc);
  binary.inclination = incRad;

  auto waveform = physics::generateInspiralWaveform(binary, fLowHz, fHighHz, dtSec);

  int const nPoints =
      static_cast<int>(std::min(waveform.size(), static_cast<size_t>(maxPoints)));

  for (int i = 0; i < nPoints; ++i) {
    double *p = outBuf + (static_cast<ptrdiff_t>(i) * 5);
    p[0] = waveform[i].t;
    p[1] = waveform[i].f;
    p[2] = waveform[i].hPlus;
    p[3] = waveform[i].hCross;
    p[4] = waveform[i].phase;
  }

  return nPoints;
}

/* ========================================================================
 * Underscore aliases for Python ctypes (bridge.py uses bhb_snake_case names)
 *
 * WHY: Blender Python bridge.py accesses symbols as lib.bhb_foo_bar but the
 *      primary C ABI exports camelCase names (bhbFooBar).  These thin wrappers
 *      forward every call so both naming conventions resolve to the same code.
 * ======================================================================== */

extern "C" {

int bhb_version_major(void) { return bhbVersionMajor(); }
int bhb_version_minor(void) { return bhbVersionMinor(); }
int bhb_has_cuda(void)      { return bhbHasCuda(); }
int bhb_has_boost(void)     { return bhbHasBoost(); }
int bhb_sizeof_source_params(void) { return bhbSizeofSourceParams(); }
int bhb_sizeof_disk_params(void)   { return bhbSizeofDiskParams(); }
int bhb_cuda_reset_device(void)    { return bhbCudaResetDevice(); }

void bhb_preset_m87(struct BhbSourceParams *out)  { bhbPresetM87(out); }
void bhb_preset_sgra(struct BhbSourceParams *out) { bhbPresetSgra(out); }

double bhb_kerr_outer_horizon(double aStar)  { return bhbKerrOuterHorizon(aStar); }
double bhb_kerr_inner_horizon(double aStar)  { return bhbKerrInnerHorizon(aStar); }

double bhb_kerr_ergosphere(double aStar, double thetaRad) {
  return bhbKerrErgosphere(aStar, thetaRad);
}
double bhb_kerr_isco(double aStar, int prograde) { return bhbKerrIsco(aStar, prograde); }
double bhb_kerr_photon_orbit_prograde(double aStar)   { return bhbKerrPhotonOrbitPrograde(aStar); }
double bhb_kerr_photon_orbit_retrograde(double aStar) { return bhbKerrPhotonOrbitRetrograde(aStar); }
double bhb_kerr_sigma(double rRg, double aStar, double thetaRad) {
  return bhbKerrSigma(rRg, aStar, thetaRad);
}
double bhb_kerr_delta(double rRg, double aStar) { return bhbKerrDelta(rRg, aStar); }

int bhb_trace_geodesics_equatorial(double aStar, double observerRRg, double bMin, double bMax,
                                    int nRays, int maxSteps, double stepSize,
                                    float *outXyz, int *outCounts) {
  return bhbTraceGeodesicsEquatorial(aStar, observerRRg, bMin, bMax, nRays, maxSteps, stepSize,
                                     outXyz, outCounts);
}

int bhb_trace_geodesics_image_plane(double aStar, double observerRRg, double inclinationRad,
                                     double alphaMin, double alphaMax, int nAlpha,
                                     double betaMin, double betaMax, int nBeta,
                                     int maxSteps, double stepSize,
                                     float *outXyz, int *outCounts) {
  return bhbTraceGeodesicsImagePlane(aStar, observerRRg, inclinationRad, alphaMin, alphaMax,
                                     nAlpha, betaMin, betaMax, nBeta, maxSteps, stepSize,
                                     outXyz, outCounts);
}

int bhb_generate_disk_mesh(const struct BhbDiskParams *params, int nRadial, int nAzimuthal,
                            float *outPos, float *outNormals, float *outTemp, float *outUvs,
                            int *outIndices, int *outVertexCount, int *outIndexCount) {
  return bhbGenerateDiskMesh(params, nRadial, nAzimuthal, outPos, outNormals, outTemp, outUvs,
                              outIndices, outVertexCount, outIndexCount);
}

double bhb_nt_radiative_efficiency(double aStar)  { return bhbNtRadiativeEfficiency(aStar); }
double bhb_nt_isco_radius(double aStar)           { return bhbNtIscoRadius(aStar); }

int bhb_nt_temperature_profile(double aStar, double massMsun, double mdotEdd,
                                const double *rValues, int n,
                                double *outTemp, double *outFlux) {
  return bhbNtTemperatureProfile(aStar, massMsun, mdotEdd, rValues, n, outTemp, outFlux);
}

double bhb_lorentz_factor(double beta)                      { return bhbLorentzFactor(beta); }
double bhb_doppler_factor(double beta, double cosTheta)     { return bhbDopplerFactor(beta, cosTheta); }
double bhb_beaming_flux(double delta, double alphaSpectral) { return bhbBeamingFlux(delta, alphaSpectral); }

/* bhb_synchrotron_gyrofreq: bridge.py assigns argtypes=[c_double, c_double] in the loop
 * that covers all four synchrotron functions; accept two args to match that prototype. */
double bhb_synchrotron_gyrofreq(double bGauss, double /*unused*/) {
  return bhbSynchrotronGyrofreq(bGauss);
}
double bhb_synchrotron_critical_freq(double bGauss, double gamma) {
  return bhbSynchrotronCriticalFreq(bGauss, gamma);
}
double bhb_synchrotron_power(double bGauss, double gamma) {
  return bhbSynchrotronPower(bGauss, gamma);
}
double bhb_synchrotron_cooling_time(double bGauss, double gamma) {
  return bhbSynchrotronCoolingTime(bGauss, gamma);
}

int bhb_render_lensing_map(double aStar, double observerRRg, double inclinationRad,
                            int width, int height, float *outRgba) {
  return bhbRenderLensingMap(aStar, observerRRg, inclinationRad, width, height, outRgba);
}

int bhb_render_disk_texture(const struct BhbDiskParams *params, int width, int height,
                             float *outRgba) {
  return bhbRenderDiskTexture(params, width, height, outRgba);
}

int bhb_generate_horizon_mesh(double aStar, int nTheta, int nPhi,
                               float *outPos, int *outIndices,
                               int *outVertexCount, int *outIndexCount) {
  return bhbGenerateHorizonMesh(aStar, nTheta, nPhi, outPos, outIndices, outVertexCount,
                                outIndexCount);
}

int bhb_generate_ergosphere_mesh(double aStar, int nTheta, int nPhi,
                                  float *outPos, int *outIndices,
                                  int *outVertexCount, int *outIndexCount) {
  return bhbGenerateErgosphereMesh(aStar, nTheta, nPhi, outPos, outIndices, outVertexCount,
                                   outIndexCount);
}

int bhb_cuda_trace_geodesics(double aStar, double observerRRg, double inclinationRad,
                              double alphaMin, double alphaMax, int nAlpha,
                              double betaMin, double betaMax, int nBeta,
                              int maxSteps, double stepSize, float *outXyz, int *outCounts) {
  return bhbCudaTraceGeodesics(aStar, observerRRg, inclinationRad, alphaMin, alphaMax, nAlpha,
                                betaMin, betaMax, nBeta, maxSteps, stepSize, outXyz, outCounts);
}

int bhb_gw_inspiral(double m1Msun, double m2Msun, double a1Star, double a2Star, double distMpc,
                    double incRad, double fLowHz, double fHighHz, double dtSec,
                    double *outBuf, int maxPoints) {
  return bhbGWInspiral(m1Msun, m2Msun, a1Star, a2Star, distMpc, incRad, fLowHz, fHighHz, dtSec,
                       outBuf, maxPoints);
}

/* When built without CUDA, provide underscore-named stubs so the .so always
 * exports these symbols and bridge.py can probe them without OSError. */
#ifndef BLACKHOLE_HAS_CUDA
int bhb_cuda_render_lensing_map(float /*a_star*/, float /*obs_r*/, float /*inc_rad*/,
                                 int /*width*/, int /*height*/, float * /*out_rgba*/) {
  return -1;
}
int bhb_cuda_render_disk_texture(float /*a_star*/, float /*r_out_rg*/, float /*inc_rad*/,
                                  int /*width*/, int /*height*/, float * /*out_rgba*/) {
  return -1;
}
int bhb_cuda_render_raytraced(float /*spin*/, float /*observer_r*/, float /*inc_rad*/,
                               int /*width*/, int /*height*/, float * /*out_rgba*/) {
  return -1;
}
int bhb_cuda_render_raytraced_camera(float /*spin*/, float /*observer_r*/, float /*inc_rad*/,
                                      float /*fov_scale*/, int /*width*/, int /*height*/,
                                      float * /*out_rgba*/) {
  return -1;
}
int bhb_cuda_render_raytraced_view(float /*spin*/, const float * /*cam_pos*/,
                                    const float * /*cam_basis*/, float /*fov_scale*/,
                                    int /*width*/, int /*height*/, float * /*out_rgba*/) {
  return -1;
}
#endif /* !BLACKHOLE_HAS_CUDA */

} /* extern "C" */
