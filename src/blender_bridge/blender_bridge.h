/*
 * blender_bridge.h
 * C-linkage API for driving Blackhole physics from Blender Python (ctypes).
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

/* Version / capability query */
int bhbVersionMajor(void);
int bhbVersionMinor(void);
int bhbHasCuda(void);
int bhbHasBoost(void);

/* ========================================================================
 * Source presets
 * ======================================================================== */

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

/* Fill a BHB_SourceParams with M87* or Sgr A* values. */
void bhbPresetM87(struct BhbSourceParams *out);
void bhbPresetSgra(struct BhbSourceParams *out);

/* ========================================================================
 * Kerr metric
 * ======================================================================== */

/* All functions take dimensionless spin a_star and radii in units of r_g. */
double bhbKerrOuterHorizon(double aStar);
double bhbKerrInnerHorizon(double aStar);
double bhbKerrErgosphere(double aStar, double thetaRad);
double bhbKerrIsco(double aStar, int prograde);
double bhbKerrPhotonOrbitPrograde(double aStar);
double bhbKerrPhotonOrbitRetrograde(double aStar);
double bhbKerrSigma(double rRg, double aStar, double thetaRad);
double bhbKerrDelta(double rRg, double aStar);

/* ========================================================================
 * Geodesic curves
 * ======================================================================== */

/*
 * Trace N photon geodesics in the equatorial plane around a Kerr BH.
 * Impact parameters span [b_min, b_max] linearly.
 *
 * Output: positions written to out_xyz as interleaved (x,y,z) floats.
 * Each ray gets max_steps points. Total floats: n_rays * max_steps * 3.
 * Returns actual points written per ray in out_counts[n_rays].
 *
 * This is CPU-side (RK4). For GPU, use bhb_cuda_trace_geodesics.
 */
int bhbTraceGeodesicsEquatorial(double aStar, double observerRRg, /* observer distance in r_g */
                                double bMin, double bMax,         /* impact parameter range [r_g] */
                                int nRays, int maxSteps,
                                double stepSize, /* affine parameter step [r_g] */
                                float *outXyz,   /* caller-allocated: n_rays * max_steps * 3 */
                                int *outCounts   /* caller-allocated: n_rays */
);

/*
 * Trace geodesics for a full image plane (2D grid).
 * alpha, beta are image-plane coordinates in units of r_g.
 * Output: out_xyz[n_alpha * n_beta * max_steps * 3], out_counts[n_alpha * n_beta].
 */
int bhbTraceGeodesicsImagePlane(double aStar, double observerRRg, double inclinationRad,
                                double alphaMin, double alphaMax, int nAlpha, double betaMin,
                                double betaMax, int nBeta, int maxSteps, double stepSize,
                                float *outXyz, int *outCounts);

/* ========================================================================
 * Accretion disk geometry
 * ======================================================================== */

struct BhbDiskParams {
  double aStar;
  double massMsun;
  double mdotEdd; /* accretion rate in Eddington units */
  double rOutRg;  /* outer radius [r_g] */
  double inclinationRad;
};

/*
 * Generate an annular mesh for the thin accretion disk.
 * Outputs vertex positions (r, theta -> x, y, z in Cartesian)
 * and per-vertex temperature [K] for coloring / emission.
 *
 * n_radial: radial subdivisions, n_azimuthal: azimuthal subdivisions.
 * Total vertices: n_radial * n_azimuthal.
 * Total triangles: 2 * (n_radial - 1) * n_azimuthal.
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

double bhbNtRadiativeEfficiency(double aStar);
double bhbNtIscoRadius(double aStar);

/*
 * Compute temperature profile T(r) for the thin disk.
 * r_values: input radii [r_g], n: count.
 * out_temperatures: output [K], out_fluxes: output [erg/cm^2/s].
 */
int bhbNtTemperatureProfile(double aStar, double massMsun, double mdotEdd, const double *rValues,
                            int n, double *outTemperatures, double *outFluxes);

/* ========================================================================
 * Doppler beaming
 * ======================================================================== */

double bhbLorentzFactor(double beta);
double bhbDopplerFactor(double beta, double cosTheta);
double bhbBeamingFlux(double delta, double alphaSpectral);

/* ========================================================================
 * Synchrotron emission
 * ======================================================================== */

double bhbSynchrotronGyrofreq(double bGauss);
double bhbSynchrotronCriticalFreq(double bGauss, double gamma);
double bhbSynchrotronPower(double bGauss, double gamma);
double bhbSynchrotronCoolingTime(double bGauss, double gamma);

/* ========================================================================
 * Texture generation (CPU fallback)
 * ======================================================================== */

/*
 * Render a gravitational lensing map for the given observer config.
 * Output: RGBA float image (4 channels) of size width x height.
 * R = redshift factor, G = Doppler factor, B = disk flag, A = 1.
 */
int bhbRenderLensingMap(double aStar, double observerRRg, double inclinationRad, int width,
                        int height, float *outRgba);

/*
 * Render accretion disk emission texture.
 * Output: RGBA float image. R,G,B = blackbody color, A = intensity.
 */
int bhbRenderDiskTexture(const struct BhbDiskParams *params, int width, int height, float *outRgba);

/* ========================================================================
 * CUDA-accelerated paths (no-op stubs if built without CUDA)
 * ======================================================================== */

/*
 * GPU-accelerated geodesic tracing. Same interface as CPU version
 * but runs on the CUDA device. Returns -1 if CUDA unavailable.
 */
int bhbCudaTraceGeodesics(double aStar, double observerRRg, double inclinationRad, double alphaMin,
                          double alphaMax, int nAlpha, double betaMin, double betaMax, int nBeta,
                          int maxSteps, double stepSize, float *outXyz, int *outCounts);

/*
 * GPU-accelerated lensing/emission texture generation.
 * Writes directly to caller buffer (pinned or pageable host memory).
 */
int bhbCudaRenderLensingMap(double aStar, double observerRRg, double inclinationRad, int width,
                            int height, float *outRgba);

int bhbCudaRenderDiskTexture(const struct BhbDiskParams *params, int width, int height,
                             float *outRgba);

/*
 * Full ray-traced black hole image via CUDA geodesic kernel.
 * Renders Kerr geodesics with accretion disk, Doppler beaming,
 * photon ring, horizon shadow -- the real thing.
 * Output: RGBA float image (4 channels) of size width x height.
 * Returns -1 if CUDA unavailable.
 */
int bhbCudaRenderRaytraced(float spin, float observerR, float inclinationRad, int width, int height,
                           float *outRgba);

/* ========================================================================
 * Ergosphere / horizon surface meshes
 * ======================================================================== */

/*
 * Generate a 3D mesh of the event horizon (oblate sphere for Kerr).
 * n_theta: polar subdivisions, n_phi: azimuthal subdivisions.
 */
int bhbGenerateHorizonMesh(double aStar, int nTheta, int nPhi,
                           float *outPositions, /* n_theta * n_phi * 3 */
                           int *outIndices,     /* triangles */
                           int *outVertexCount, int *outIndexCount);

/*
 * Generate a 3D mesh of the ergosphere boundary.
 */
int bhbGenerateErgosphereMesh(double aStar, int nTheta, int nPhi, float *outPositions,
                              int *outIndices, int *outVertexCount, int *outIndexCount);

#ifdef __cplusplus
}
#endif

#endif /* BLACKHOLE_BLENDER_BRIDGE_H */
