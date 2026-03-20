/**
 * @file lut_manager.cu
 * @brief Implementation of GL-to-CUDA LUT texture object management.
 *
 * WHY: GL textures used as physics LUTs (emissivity, redshift, spectral, GRB,
 *      galaxy cubemap) must be accessible from CUDA kernels without duplicating
 *      data.  CUDA-GL interop lets us register the GL texture as a read-only
 *      CUDA resource and create a texture object pointing at the same memory.
 *
 * HOW (2D slots 0-3):
 *   - cudaGraphicsGLRegisterImage + map + GetMappedArray(face=0, mip=0)
 *   - Create 2D texture object; unmap (object stays valid while GL resource
 *     is registered).
 *
 * HOW (cubemap slot 4 = BhLutGalaxy):
 *   - Register with GL_TEXTURE_CUBE_MAP target.
 *   - Map and retrieve all 6 face arrays via GetMappedArray(face=0..5, mip=0).
 *   - Allocate an owned 6-layer 2D cudaArray (cudaArrayLayered) with the same
 *     channel format and copy each face into the matching layer.
 *   - Create a tex2DLayered texture object from the owned array.
 *   - Unmap the GL resource (owned array lives until lutUnregister).
 *   - Device code selects face+UV from ray direction, then calls tex2DLayered.
 *
 * CUBEMAP FACE ORDER (matching GL_TEXTURE_CUBE_MAP_POSITIVE_X ordering):
 *   layer 0 = +X, 1 = -X, 2 = +Y, 3 = -Y, 4 = +Z, 5 = -Z
 */

#include <cstdio>

#include <cuda_gl_interop.h>
#include <cuda_runtime_api.h>
#include <driver_types.h>
#include <texture_types.h>

#include "lut_manager.h"

/* GL cubemap target constant (0x8513) -- avoids including GL headers here */
static constexpr unsigned int kGLTextureCubeMap = 0x8513U;

/* Number of faces in a cubemap */
static constexpr int kCubeFaces = 6;

/**
 * @brief Register a 2D GL texture (emissivity / redshift / spectral / GRB).
 *
 * Maps the GL resource to obtain the underlying CUDA array and creates a 2D
 * normalised-float texture object suitable for tex2D<float4> sampling.
 *
 * @param mgr   LUT manager to update.
 * @param slot  BhLutSlot index (0-3).
 * @param glTex GL texture name.
 * @return 0 on success, -1 on any CUDA error.
 */
static int lutRegister2D(LutManager &mgr, int slot, unsigned int glTex,
                         unsigned int glTarget) {
  cudaError_t err =
      cudaGraphicsGLRegisterImage(&mgr.resources[slot], glTex, glTarget,
                                  cudaGraphicsRegisterFlagsReadOnly);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister2D slot %d: cudaGraphicsGLRegisterImage failed: %s\n",
                  slot, cudaGetErrorString(err));
    return -1;
  }

  err = cudaGraphicsMapResources(1, &mgr.resources[slot], nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister2D slot %d: MapResources failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  cudaArray_t array = nullptr;
  err = cudaGraphicsSubResourceGetMappedArray(&array, mgr.resources[slot], 0, 0);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister2D slot %d: GetMappedArray failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  cudaResourceDesc resDesc = {};
  resDesc.resType         = cudaResourceTypeArray;
  resDesc.res.array.array = array;

  cudaTextureDesc texDesc = {};
  texDesc.addressMode[0]  = cudaAddressModeClamp;
  texDesc.addressMode[1]  = cudaAddressModeClamp;
  texDesc.filterMode      = cudaFilterModeLinear;
  texDesc.readMode        = cudaReadModeElementType;
  texDesc.normalizedCoords = 1;

  err = cudaCreateTextureObject(&mgr.texObjects[slot], &resDesc, &texDesc, nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister2D slot %d: CreateTextureObject failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Unmap: texture object remains valid while resource is registered */
  cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
  mgr.registered[slot] = true;
  return 0;
}

/**
 * @brief Register a GL_TEXTURE_CUBE_MAP texture (galaxy background, slot 4).
 *
 * Allocates an owned 6-layer 2D cudaArray matching the cubemap face size and
 * channel format, copies all six GL faces into it (device-to-device), and
 * creates a tex2DLayered texture object.  The owned array is stored in
 * mgr.layeredArrays[slot] and freed by lutUnregister().
 *
 * Face ordering: layer 0=+X, 1=-X, 2=+Y, 3=-Y, 4=+Z, 5=-Z.
 *
 * @param mgr   LUT manager to update.
 * @param slot  BhLutSlot index (should be BhLutGalaxy = 4).
 * @param glTex GL cubemap texture name.
 * @return 0 on success, -1 on any CUDA error.
 */
static int lutRegisterCubemap(LutManager &mgr, int slot, unsigned int glTex) {
  /* Register the GL cubemap resource */
  cudaError_t err =
      cudaGraphicsGLRegisterImage(&mgr.resources[slot], glTex, kGLTextureCubeMap,
                                  cudaGraphicsRegisterFlagsReadOnly);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegisterCubemap slot %d: RegisterImage failed: %s\n", slot,
                  cudaGetErrorString(err));
    return -1;
  }

  err = cudaGraphicsMapResources(1, &mgr.resources[slot], nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegisterCubemap slot %d: MapResources failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Query face 0 for channel format and dimensions */
  cudaArray_t face0 = nullptr;
  err = cudaGraphicsSubResourceGetMappedArray(&face0, mgr.resources[slot], 0, 0);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegisterCubemap slot %d: GetMappedArray face 0 failed: %s\n",
                  slot, cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  cudaChannelFormatDesc channelDesc = {};
  cudaExtent extent                 = {};
  unsigned int arrayFlags           = 0U;
  err = cudaArrayGetInfo(&channelDesc, &extent, &arrayFlags, face0);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegisterCubemap slot %d: cudaArrayGetInfo failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Allocate owned 6-layer 2D array */
  cudaArray_t layered = nullptr;
  cudaExtent layeredExtent = make_cudaExtent(extent.width, extent.height,
                                             static_cast<size_t>(kCubeFaces));
  err = cudaMalloc3DArray(&layered, &channelDesc, layeredExtent, cudaArrayLayered);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegisterCubemap slot %d: cudaMalloc3DArray failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Copy each GL cubemap face into the corresponding layer */
  for (int face = 0; face < kCubeFaces; ++face) {
    cudaArray_t faceArray = nullptr;
    err = cudaGraphicsSubResourceGetMappedArray(&faceArray, mgr.resources[slot],
                                                static_cast<unsigned int>(face), 0);
    if (err != cudaSuccess) {
      (void)fprintf(stderr,
                    "lutRegisterCubemap slot %d: GetMappedArray face %d failed: %s\n",
                    slot, face, cudaGetErrorString(err));
      /* Non-fatal per face: leave remaining faces at zero */
      continue;
    }

    cudaMemcpy3DParms parms = {};
    parms.srcArray          = faceArray;
    parms.dstArray          = layered;
    parms.dstPos            = make_cudaPos(0, 0, static_cast<size_t>(face));
    parms.extent            = make_cudaExtent(extent.width, extent.height, 1);
    parms.kind              = cudaMemcpyDeviceToDevice;

    err = cudaMemcpy3D(&parms);
    if (err != cudaSuccess) {
      (void)fprintf(stderr,
                    "lutRegisterCubemap slot %d: cudaMemcpy3D face %d failed: %s\n",
                    slot, face, cudaGetErrorString(err));
    }
  }

  /* Unmap GL resource -- owned layered array persists */
  cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);

  /* Create tex2DLayered texture object from the owned array.
   * readMode=ElementType for float textures; normalizedCoords for [0,1] UV. */
  cudaResourceDesc resDesc = {};
  resDesc.resType          = cudaResourceTypeArray;
  resDesc.res.array.array  = layered;

  cudaTextureDesc texDesc  = {};
  texDesc.addressMode[0]   = cudaAddressModeWrap;
  texDesc.addressMode[1]   = cudaAddressModeClamp;
  texDesc.filterMode       = cudaFilterModeLinear;
  texDesc.readMode         = (channelDesc.f == cudaChannelFormatKindFloat)
                               ? cudaReadModeElementType
                               : cudaReadModeNormalizedFloat;
  texDesc.normalizedCoords = 1;

  err = cudaCreateTextureObject(&mgr.texObjects[slot], &resDesc, &texDesc, nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr,
                  "lutRegisterCubemap slot %d: CreateTextureObject failed: %s\n",
                  slot, cudaGetErrorString(err));
    cudaFreeArray(layered);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  mgr.layeredArrays[slot] = layered;
  mgr.registered[slot]    = true;
  return 0;
}

int lutRegister(LutManager &mgr, int slot, unsigned int glTex, unsigned int glTarget) {
  if (slot < 0 || slot >= BhLutCount) {
    return -1;
  }

  /* Unregister previous if re-registering */
  if (mgr.registered[slot]) {
    lutUnregister(mgr, slot);
  }

  if (glTarget == kGLTextureCubeMap) {
    return lutRegisterCubemap(mgr, slot, glTex);
  }
  return lutRegister2D(mgr, slot, glTex, glTarget);
}

void lutUnregister(LutManager &mgr, int slot) {
  if (slot < 0 || slot >= BhLutCount) {
    return;
  }
  if (!mgr.registered[slot]) {
    return;
  }

  if (mgr.texObjects[slot] != 0u) {
    cudaDestroyTextureObject(mgr.texObjects[slot]);
    mgr.texObjects[slot] = 0;
  }
  /* Free owned layered array allocated for cubemap slots */
  if (mgr.layeredArrays[slot] != nullptr) {
    cudaFreeArray(mgr.layeredArrays[slot]);
    mgr.layeredArrays[slot] = nullptr;
  }
  if (mgr.resources[slot] != nullptr) {
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
  }
  mgr.registered[slot] = false;
}

cudaTextureObject_t lutGetTex(const LutManager &mgr, int slot) {
  if (slot < 0 || slot >= BhLutCount) {
    return 0;
  }
  return mgr.texObjects[slot];
}

void lutShutdown(LutManager &mgr) {
  for (int i = 0; i < BhLutCount; ++i) {
    lutUnregister(mgr, i);
  }
}
