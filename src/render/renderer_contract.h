#ifndef BLACKHOLE_RENDERER_CONTRACT_H
#define BLACKHOLE_RENDERER_CONTRACT_H

#include <algorithm>
#include <array>
#include <optional>
#include <string_view>

namespace blackhole {

enum class RenderBackend { Fragment, Compute, Cuda };
enum class GeodesicModel { LegacyBeauty, SchwarzschildReference, KerrReference };
enum class RadiativeModel { BackgroundOnly, ThinSurface, VolumetricRte, Stokes };
enum class QualityTier { Interactive, Balanced, Reference };

struct RendererContract {
  RenderBackend backend = RenderBackend::Fragment;
  GeodesicModel geodesic = GeodesicModel::KerrReference;
  // The volumetric disk (interop_trace.glsl bhTraceGeodesicRTE): density
  // absorption, flared height, and a soft outer taper over the thin-surface
  // disk's emission.
  RadiativeModel radiative = RadiativeModel::VolumetricRte;
  QualityTier quality = QualityTier::Balanced;
};

constexpr std::string_view rendererName(RenderBackend value) {
  switch (value) {
  case RenderBackend::Fragment: return "fragment";
  case RenderBackend::Compute: return "compute";
  case RenderBackend::Cuda: return "cuda";
  }
  return "unknown";
}

constexpr std::string_view rendererName(GeodesicModel value) {
  switch (value) {
  case GeodesicModel::LegacyBeauty: return "legacy-beauty";
  case GeodesicModel::SchwarzschildReference: return "schwarzschild-reference";
  case GeodesicModel::KerrReference: return "kerr-reference";
  }
  return "unknown";
}

constexpr std::string_view rendererName(RadiativeModel value) {
  switch (value) {
  case RadiativeModel::BackgroundOnly: return "background-only";
  case RadiativeModel::ThinSurface: return "thin-surface";
  case RadiativeModel::VolumetricRte: return "volumetric-rte";
  case RadiativeModel::Stokes: return "stokes";
  }
  return "unknown";
}

constexpr std::string_view rendererName(QualityTier value) {
  switch (value) {
  case QualityTier::Interactive: return "interactive";
  case QualityTier::Balanced: return "balanced";
  case QualityTier::Reference: return "reference";
  }
  return "unknown";
}

/// Reference-tier step size and the affine range it must at least cover.
inline constexpr float K_REFERENCE_STEP_SIZE = 0.02f;
inline constexpr float K_REFERENCE_MIN_AFFINE_RANGE = 40.0f;
inline constexpr int K_REFERENCE_MAX_STEPS = 20000;

/// Accretion-disk outer edge in units of r_s. BH_DISK_OUTER_RADIUS_RS
/// (shader/include/interop_trace.glsl) and D_DISK_OUTER_RADIUS_RS
/// (src/cuda/device_physics.cuh) carry the same value, and
/// settings_persistence_test reads both sources to hold them equal.
inline constexpr float K_DISK_OUTER_RADIUS_RS = 20.0f;

// Near-critical rays exhaust a budget by running out of affine range, not by
// step error, so the reference tier covers twice the selected range (and at
// least K_REFERENCE_MIN_AFFINE_RANGE) at the finer K_REFERENCE_STEP_SIZE. A
// budget that only halves the step over the same range exhausts the same rays.
constexpr int rendererStepBudget(QualityTier value, int selectedSteps, float selectedSize) {
  if (value == QualityTier::Reference) {
    const float selectedRange = static_cast<float>(selectedSteps) * selectedSize;
    const float range = std::max(K_REFERENCE_MIN_AFFINE_RANGE, 2.0f * selectedRange);
    const auto steps = static_cast<int>(range / K_REFERENCE_STEP_SIZE) + 1;
    return std::min(steps, K_REFERENCE_MAX_STEPS);
  }
  return value == QualityTier::Interactive ? std::min(selectedSteps, 300) : selectedSteps;
}

constexpr float rendererStepSize(QualityTier value, float selectedSize) {
  if (value == QualityTier::Reference) {
    return K_REFERENCE_STEP_SIZE;
  }
  return value == QualityTier::Interactive ? std::max(selectedSize, 0.1f) : selectedSize;
}

constexpr int rendererStepBudget(const RendererContract &contract, int selectedSteps,
                                 float selectedSize) {
  return contract.geodesic == GeodesicModel::LegacyBeauty
             ? 300 : rendererStepBudget(contract.quality, selectedSteps, selectedSize);
}

constexpr float rendererStepSize(const RendererContract &contract, float selectedSize) {
  return contract.geodesic == GeodesicModel::LegacyBeauty
             ? 0.1f : rendererStepSize(contract.quality, selectedSize);
}

/// Backend or geodesic model whose rendererName is @p name, if any.
constexpr std::optional<RenderBackend> rendererBackendFromName(std::string_view name) {
  for (const RenderBackend value :
       std::array{RenderBackend::Fragment, RenderBackend::Compute, RenderBackend::Cuda}) {
    if (rendererName(value) == name) {
      return value;
    }
  }
  return std::nullopt;
}

constexpr std::optional<GeodesicModel> geodesicModelFromName(std::string_view name) {
  for (const GeodesicModel value :
       std::array{GeodesicModel::LegacyBeauty, GeodesicModel::SchwarzschildReference,
                  GeodesicModel::KerrReference}) {
    if (rendererName(value) == name) {
      return value;
    }
  }
  return std::nullopt;
}

constexpr std::optional<RadiativeModel> radiativeModelFromName(std::string_view name) {
  for (const RadiativeModel value :
       std::array{RadiativeModel::BackgroundOnly, RadiativeModel::ThinSurface,
                  RadiativeModel::VolumetricRte, RadiativeModel::Stokes}) {
    if (rendererName(value) == name) {
      return value;
    }
  }
  return std::nullopt;
}

constexpr void normalizeRendererContract(RendererContract &contract) {
  if (contract.backend != RenderBackend::Fragment &&
      contract.geodesic == GeodesicModel::LegacyBeauty) {
    contract.geodesic = GeodesicModel::KerrReference;
  }
  if (contract.geodesic == GeodesicModel::LegacyBeauty) {
    contract.radiative = RadiativeModel::ThinSurface;
  }
}

} // namespace blackhole

#endif
