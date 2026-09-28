#ifndef BLACKHOLE_RENDERER_CONTRACT_H
#define BLACKHOLE_RENDERER_CONTRACT_H

#include <algorithm>
#include <string_view>

namespace blackhole {

enum class RenderBackend { Fragment, Compute, Cuda };
enum class GeodesicModel { LegacyBeauty, SchwarzschildReference, KerrReference };
enum class RadiativeModel { BackgroundOnly, ThinSurface, VolumetricRte, Stokes };
enum class QualityTier { Interactive, Balanced, Reference };

struct RendererContract {
  RenderBackend backend = RenderBackend::Fragment;
  GeodesicModel geodesic = GeodesicModel::KerrReference;
  RadiativeModel radiative = RadiativeModel::ThinSurface;
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

constexpr int rendererStepBudget(QualityTier value, int selectedSteps) {
  if (value == QualityTier::Reference) {
    return 1000;
  }
  return value == QualityTier::Interactive ? std::min(selectedSteps, 300) : selectedSteps;
}

constexpr float rendererStepSize(QualityTier value, float selectedSize) {
  if (value == QualityTier::Reference) {
    return 0.02f;
  }
  return value == QualityTier::Interactive ? std::max(selectedSize, 0.1f) : selectedSize;
}

constexpr int rendererStepBudget(const RendererContract &contract, int selectedSteps) {
  return contract.geodesic == GeodesicModel::LegacyBeauty
             ? 300 : rendererStepBudget(contract.quality, selectedSteps);
}

constexpr float rendererStepSize(const RendererContract &contract, float selectedSize) {
  return contract.geodesic == GeodesicModel::LegacyBeauty
             ? 0.1f : rendererStepSize(contract.quality, selectedSize);
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
