/**
 * @file blender_bridge.h
 * @brief C-linkage API for driving Blackhole physics from Blender Python (ctypes).
 *
 * WHY: Expose Kerr geodesics, accretion disk geometry, synchrotron textures,
 *      and CUDA-accelerated rendering to Blender via a flat C ABI.
 * WHAT: Shared library (libblackhole_bridge.so) with POD structs and functions.
 * HOW: ctypes.CDLL("libblackhole_bridge.so") from Blender's Python.
 *
 * All coordinates use geometric units (r_g = GM/c^2 = 1) unless noted.
 * Angles in radians. Outputs in caller-allocated buffers.
 */

#ifndef BLACKHOLE_BLENDER_BRIDGE_H
#define BLACKHOLE_BLENDER_BRIDGE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/** @brief Return the major version number of the bridge library. */
int bhbVersionMajor(void);
/** @brief Return the minor version number of the bridge library. */
int bhbVersionMinor(void);
/** @brief Return 1 if the library was compiled with CUDA support, 0 otherwise. */
int bhbHasCuda(void);
/** @brief Return 1 if the library was compiled with Boost math support, 0 otherwise. */
int bhbHasBoost(void);

/* ========================================================================
 * Source presets
 * ======================================================================== */

/**
 * @brief Physical parameters for a black hole source preset (M87* or Sgr A*).
 *
 * Input fields are set by the preset functions. rGCm and shadowUas are
 * computed outputs derived from the other fields.
 */
struct BhbSourceParams {
  char name[64];
  double massMsun;       /* solar masses */
  double spin;           /* dimensionless a* in [0,1) */
  double distanceCm;     /* observer distance [cm] */
  double inclinationDeg; /* from spin axis [deg] */
  double freqHz;         /* observing frequency [Hz] */
  double rGCm;           /* gravitational radius [cm] (output) */
  double shadowUas;      /* shadow diameter [uas] (output) */
};

/**
 * @brief Populate @p out with canonical M87* parameters (mass, spin, distance, inclination).
 * @param out Caller-allocated struct to fill.
 */
void bhbPresetM87(struct BhbSourceParams *out);
/**
 * @brief Populate @p out with canonical Sgr A* parameters (mass, spin, distance, inclination).
 * @param out Caller-allocated struct to fill.
 */
void bhbPresetSgra(struct BhbSourceParams *out);

/* ========================================================================
 * Kerr metric
 * ======================================================================== */

/* All functions take dimensionless spin a_star and radii in units of r_g. */

/** @brief Return the outer (event) horizon radius r_+ in units of r_g.
 *  @param aStar Dimensionless spin parameter a* in [0, 1). */
double bhbKerrOuterHorizon(double aStar);

/** @brief Return the inner (Cauchy) horizon radius r_- in units of r_g.
 *  @param aStar Dimensionless spin parameter a* in [0, 1). */
double bhbKerrInnerHorizon(double aStar);

/** @brief Return the ergosphere radius at polar angle @p thetaRad in units of r_g.
 *  @param aStar     Dimensionless spin.
 *  @param thetaRad  Polar angle from the spin axis [rad]. */
double bhbKerrErgosphere(double aStar, double thetaRad);

/** @brief Return the ISCO radius in units of r_g.
 *  @param aStar     Dimensionless spin.
 *  @param prograde  Non-zero for prograde orbit, zero for retrograde. */
double bhbKerrIsco(double aStar, int prograde);

/** @brief Return the prograde circular photon orbit radius in units of r_g.
 *  @param aStar Dimensionless spin. */
double bhbKerrPhotonOrbitPrograde(double aStar);

/** @brief Return the retrograde circular photon orbit radius in units of r_g.
 *  @param aStar Dimensionless spin. */
double bhbKerrPhotonOrbitRetrograde(double aStar);

/** @brief Compute the Kerr Sigma function Sigma = r^2 + a^2 cos^2(theta) (in units of r_g^2).
 *  @param rRg       Radial coordinate [r_g].
 *  @param aStar     Dimensionless spin.
 *  @param thetaRad  Polar angle [rad].
 *  @return Sigma / M^2 (dimensionless). */
double bhbKerrSigma(double rRg, double aStar, double thetaRad);

/** @brief Compute the Kerr Delta function Delta = r^2 - 2r + a^2 (in units of r_g^2).
 *  @param rRg   Radial coordinate [r_g].
 *  @param aStar Dimensionless spin.
 *  @return Delta / M^2 (dimensionless). */
double bhbKerrDelta(double rRg, double aStar);

/* ========================================================================
 * Geodesic curves
 * ======================================================================== */

/**
 * @brief Trace @p nRays photon geodesics in the equatorial plane around a Kerr BH (CPU RK4).
 *
 * Impact parameters are distributed linearly over [bMin, bMax].
 * For GPU-accelerated tracing use bhbCudaTraceGeodesics().
 *
 * @param aStar       Dimensionless spin.
 * @param observerRRg Observer radial coordinate [r_g].
 * @param bMin        Minimum impact parameter [r_g].
 * @param bMax        Maximum impact parameter [r_g].
 * @param nRays       Number of rays to trace.
 * @param maxSteps    Maximum integration steps per ray.
 * @param stepSize    Affine parameter step size [r_g].
 * @param outXyz      Caller-allocated output: nRays * maxSteps * 3 floats (interleaved x,y,z).
 * @param outCounts   Caller-allocated output: nRays ints giving actual points written per ray.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbTraceGeodesicsEquatorial(double aStar, double observerRRg, /* observer distance in r_g */
                                double bMin, double bMax,         /* impact parameter range [r_g] */
                                int nRays, int maxSteps,
                                double stepSize, /* affine parameter step [r_g] */
                                float *outXyz,   /* caller-allocated: n_rays * max_steps * 3 */
                                int *outCounts   /* caller-allocated: n_rays */
);

/**
 * @brief Trace geodesics for a full 2-D image plane (CPU RK4).
 *
 * @p alphaMin / @p alphaMax and @p betaMin / @p betaMax define the image-plane
 * coordinate extents in units of r_g.
 *
 * @param aStar          Dimensionless spin.
 * @param observerRRg    Observer radial coordinate [r_g].
 * @param inclinationRad Observer inclination from the spin axis [rad].
 * @param alphaMin       Left edge of the image plane [r_g].
 * @param alphaMax       Right edge of the image plane [r_g].
 * @param nAlpha         Horizontal pixel count.
 * @param betaMin        Bottom edge of the image plane [r_g].
 * @param betaMax        Top edge of the image plane [r_g].
 * @param nBeta          Vertical pixel count.
 * @param maxSteps       Maximum integration steps per ray.
 * @param stepSize       Affine parameter step size [r_g].
 * @param outXyz         Caller-allocated: nAlpha * nBeta * maxSteps * 3 floats.
 * @param outCounts      Caller-allocated: nAlpha * nBeta ints.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbTraceGeodesicsImagePlane(double aStar, double observerRRg, double inclinationRad,
                                double alphaMin, double alphaMax, int nAlpha, double betaMin,
                                double betaMax, int nBeta, int maxSteps, double stepSize,
                                float *outXyz, int *outCounts);

/* ========================================================================
 * Accretion disk geometry
 * ======================================================================== */

/**
 * @brief Parameters describing a geometrically thin accretion disk around a Kerr BH.
 *
 * Used by bhbGenerateDiskMesh(), bhbNtTemperatureProfile(), and the disk texture functions.
 * The inner edge is automatically set to the prograde ISCO.
 */
struct BhbDiskParams {
  double aStar;
  double massMsun;
  double mdotEdd; /* accretion rate in Eddington units */
  double rOutRg;  /* outer radius [r_g] */
  double inclinationRad;
};

/**
 * @brief Generate an annular triangle mesh for the thin accretion disk.
 *
 * Vertex positions are in Boyer-Lindquist r/phi mapped to Cartesian (x, y, z)
 * with disk inclination applied. Per-vertex temperatures use the
 * Novikov-Thorne profile.
 *
 * @param params         Disk configuration (spin, mass, mdot, outer radius, inclination).
 * @param nRadial        Number of radial rings (>= 2).
 * @param nAzimuthal     Number of azimuthal segments (>= 3).
 * @param outPositions   Caller-allocated: nRadial * nAzimuthal * 3 floats (xyz).
 * @param outNormals     Caller-allocated: nRadial * nAzimuthal * 3 floats.
 * @param outTemperatures Caller-allocated: nRadial * nAzimuthal floats [K].
 * @param outUvs         Caller-allocated: nRadial * nAzimuthal * 2 floats.
 * @param outIndices     Caller-allocated: 2 * (nRadial-1) * nAzimuthal * 3 ints.
 * @param outVertexCount Receives total vertex count.
 * @param outIndexCount  Receives total index count.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbGenerateDiskMesh(const struct BhbDiskParams *params, int nRadial, int nAzimuthal,
                        float *outPositions,    /* n_radial * n_azimuthal * 3 floats */
                        float *outNormals,      /* n_radial * n_azimuthal * 3 floats */
                        float *outTemperatures, /* n_radial * n_azimuthal floats */
                        float *outUvs,          /* n_radial * n_azimuthal * 2 floats */
                        int *outIndices,        /* 2 * (n_radial-1) * n_azimuthal * 3 ints */
                        int *outVertexCount, int *outIndexCount);

/* ========================================================================
 * Novikov-Thorne disk physics
 * ======================================================================== */

/**
 * @brief Return the Novikov-Thorne radiative efficiency eta(a*).
 * @param aStar Dimensionless spin.
 * @return Efficiency in [0, 1].
 */
double bhbNtRadiativeEfficiency(double aStar);

/**
 * @brief Return the ISCO radius from the Novikov-Thorne model in units of r_g.
 * @param aStar Dimensionless spin.
 */
double bhbNtIscoRadius(double aStar);

/**
 * @brief Compute the Novikov-Thorne temperature and flux profile at an array of radii.
 *
 * Radii below the ISCO receive zero temperature and flux.
 *
 * @param aStar           Dimensionless spin.
 * @param massMsun        Black hole mass [solar masses].
 * @param mdotEdd         Accretion rate in Eddington units.
 * @param rValues         Input radii [r_g], length @p n.
 * @param n               Number of radii.
 * @param outTemperatures Output temperatures [K], length @p n. May be NULL.
 * @param outFluxes       Output radiative fluxes [erg/cm^2/s], length @p n. May be NULL.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbNtTemperatureProfile(double aStar, double massMsun, double mdotEdd, const double *rValues,
                            int n, double *outTemperatures, double *outFluxes);

/* ========================================================================
 * Doppler beaming
 * ======================================================================== */

/**
 * @brief Return the Lorentz factor gamma = 1 / sqrt(1 - beta^2).
 * @param beta Velocity as a fraction of c.
 */
double bhbLorentzFactor(double beta);

/**
 * @brief Return the relativistic Doppler factor delta = 1 / (gamma * (1 - beta * cos(theta))).
 * @param beta     Velocity as a fraction of c.
 * @param cosTheta Cosine of the angle between velocity and line-of-sight.
 */
double bhbDopplerFactor(double beta, double cosTheta);

/**
 * @brief Return the Doppler-boosted flux factor delta^(3 + alpha).
 * @param delta          Doppler factor from bhbDopplerFactor().
 * @param alphaSpectral  Spectral index of the emission.
 */
double bhbBeamingFlux(double delta, double alphaSpectral);

/* ========================================================================
 * Synchrotron emission
 * ======================================================================== */

/**
 * @brief Return the non-relativistic electron gyrofrequency [Hz].
 * @param bGauss Magnetic field strength [Gauss].
 */
double bhbSynchrotronGyrofreq(double bGauss);

/**
 * @brief Return the synchrotron critical frequency for a single electron [Hz].
 * @param bGauss Magnetic field strength [Gauss].
 * @param gamma  Electron Lorentz factor.
 */
double bhbSynchrotronCriticalFreq(double bGauss, double gamma);

/**
 * @brief Return the synchrotron radiated power for a single electron [erg/s].
 * @param bGauss Magnetic field strength [Gauss].
 * @param gamma  Electron Lorentz factor.
 */
double bhbSynchrotronPower(double bGauss, double gamma);

/**
 * @brief Return the synchrotron cooling time for a single electron [s].
 * @param bGauss Magnetic field strength [Gauss].
 * @param gamma  Electron Lorentz factor.
 */
double bhbSynchrotronCoolingTime(double bGauss, double gamma);

/* ========================================================================
 * Texture generation (CPU fallback)
 * ======================================================================== */

/**
 * @brief Render a gravitational lensing map to a CPU RGBA float buffer.
 *
 * Each pixel encodes: R = gravitational redshift factor, G = Doppler factor,
 * B = 1 if the ray hit the disk else 0, A = 1.
 *
 * @param aStar          Dimensionless spin.
 * @param observerRRg    Observer radial coordinate [r_g].
 * @param inclinationRad Observer inclination [rad].
 * @param width          Image width in pixels.
 * @param height         Image height in pixels.
 * @param outRgba        Caller-allocated: width * height * 4 floats.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbRenderLensingMap(double aStar, double observerRRg, double inclinationRad, int width,
                        int height, float *outRgba);

/**
 * @brief Render an accretion disk emission texture to a CPU RGBA float buffer.
 *
 * Each pixel encodes: R,G,B = blackbody color modulated by Doppler, A = normalised intensity.
 *
 * @param params  Disk configuration.
 * @param width   Image width in pixels.
 * @param height  Image height in pixels.
 * @param outRgba Caller-allocated: width * height * 4 floats.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbRenderDiskTexture(const struct BhbDiskParams *params, int width, int height, float *outRgba);

/* ========================================================================
 * CUDA-accelerated paths (no-op stubs if built without CUDA)
 * ======================================================================== */

/**
 * @brief GPU-accelerated geodesic tracing over a 2-D image plane.
 *
 * Same interface as bhbTraceGeodesicsImagePlane() but dispatched to CUDA.
 * Returns -1 if CUDA is unavailable (library built without CUDA or no device found).
 */
int bhbCudaTraceGeodesics(double aStar, double observerRRg, double inclinationRad, double alphaMin,
                          double alphaMax, int nAlpha, double betaMin, double betaMax, int nBeta,
                          int maxSteps, double stepSize, float *outXyz, int *outCounts);

/**
 * @brief GPU-accelerated lensing map generation. Writes to caller-supplied host buffer.
 *
 * Returns -1 if CUDA is unavailable.
 */
int bhbCudaRenderLensingMap(double aStar, double observerRRg, double inclinationRad, int width,
                            int height, float *outRgba);

/**
 * @brief GPU-accelerated accretion disk emission texture generation.
 *
 * Returns -1 if CUDA is unavailable.
 */
int bhbCudaRenderDiskTexture(const struct BhbDiskParams *params, int width, int height,
                             float *outRgba);

/**
 * @brief Render a physically correct ray-traced black hole image on the GPU.
 *
 * Runs the full CUDA geodesic kernel including Kerr metric, accretion disk,
 * Doppler beaming, photon ring, and horizon shadow, followed by the
 * post-processing pipeline (bloom, ACES tonemap, chromatic aberration, vignette,
 * film grain). Output is a host RGBA float buffer.
 *
 * @param spin           Dimensionless spin a*.
 * @param observerR      Observer radial coordinate [r_s units].
 * @param inclinationRad Observer inclination from spin axis [rad].
 * @param width          Image width in pixels.
 * @param height         Image height in pixels.
 * @param outRgba        Caller-allocated: width * height * 4 floats.
 * @return 0 on success, -1 if CUDA is unavailable or a device error occurred.
 */
int bhbCudaRenderRaytraced(float spin, float observerR, float inclinationRad, int width, int height,
                           float *outRgba);

/* ========================================================================
 * Ergosphere / horizon surface meshes
 * ======================================================================== */

/**
 * @brief Generate a triangulated 3-D mesh of the Kerr event horizon.
 *
 * The horizon is an oblate spheroid embedded in Boyer-Lindquist coordinates.
 * Positions are in units of r_g.
 *
 * @param aStar          Dimensionless spin.
 * @param nTheta         Polar subdivisions (>= 2).
 * @param nPhi           Azimuthal subdivisions (>= 3).
 * @param outPositions   Caller-allocated: nTheta * nPhi * 3 floats.
 * @param outIndices     Caller-allocated triangle index buffer.
 * @param outVertexCount Receives total vertex count.
 * @param outIndexCount  Receives total index count.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbGenerateHorizonMesh(double aStar, int nTheta, int nPhi,
                           float *outPositions, /* n_theta * n_phi * 3 */
                           int *outIndices,     /* triangles */
                           int *outVertexCount, int *outIndexCount);

/**
 * @brief Generate a triangulated 3-D mesh of the Kerr ergosphere boundary.
 *
 * The ergosphere surface r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2(theta))
 * varies with polar angle. Positions are in units of r_g.
 *
 * @param aStar          Dimensionless spin.
 * @param nTheta         Polar subdivisions (>= 2).
 * @param nPhi           Azimuthal subdivisions (>= 3).
 * @param outPositions   Caller-allocated: nTheta * nPhi * 3 floats.
 * @param outIndices     Caller-allocated triangle index buffer.
 * @param outVertexCount Receives total vertex count.
 * @param outIndexCount  Receives total index count.
 * @return 0 on success, -1 on invalid arguments.
 */
int bhbGenerateErgosphereMesh(double aStar, int nTheta, int nPhi, float *outPositions,
                              int *outIndices, int *outVertexCount, int *outIndexCount);

#ifdef __cplusplus
}
#endif

#endif /* BLACKHOLE_BLENDER_BRIDGE_H */
