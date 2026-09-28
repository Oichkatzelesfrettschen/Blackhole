#ifndef BLACKHOLE_UI_PRESENTATION_METADATA_H
#define BLACKHOLE_UI_PRESENTATION_METADATA_H

#include <array>
#include <string_view>

namespace ui {

enum class ControlVisibility { Basic, Advanced };

struct ControlPresentation {
  // Empty units mean dimensionless; an empty persistence key means runtime-only.
  std::string_view key;
  const char *label;
  const char *help;
  const char *units = "";
  float minimum = 0.0f;
  float maximum = 1.0f;
  float step = 1.0f;
  const char *format = "";
  ControlVisibility visibility = ControlVisibility::Basic;
  std::string_view persistenceKey;
};

inline constexpr std::array<ControlPresentation, 11> K_DISK_PRESENTATION{{
    {.key = "gravitationalLensing",
     .label = "Gravitational lensing",
     .help = "Bends the rendered background around the black hole.",
     .persistenceKey = "gravitationalLensing"},
    {.key = "renderBlackHole",
     .label = "Render event-horizon silhouette",
     .help = "Shows the central dark silhouette.",
     .persistenceKey = "renderBlackHole"},
    {.key = "adiskEnabled",
     .label = "Accretion disk",
     .help = "Shows the legacy tracer's disk.",
     .persistenceKey = "adiskEnabled"},
    {.key = "adiskParticle",
     .label = "Particle detail",
     .help = "Enables the legacy disk's particle detail.",
     .persistenceKey = "adiskParticle"},
    {.key = "adiskDensityV",
     .label = "Vertical density",
     .help = "Adjusts the legacy disk density profile vertically.",
     .maximum = 10.0f,
     .step = 0.1f,
     .format = "%.2f",
     .persistenceKey = "adiskDensityV"},
    {.key = "adiskDensityH",
     .label = "Radial density",
     .help = "Adjusts the legacy disk density profile radially.",
     .maximum = 10.0f,
     .step = 0.1f,
     .format = "%.2f",
     .persistenceKey = "adiskDensityH"},
    {.key = "adiskHeight",
     .label = "Disk thickness",
     .help = "Adjusts the legacy disk's thickness control.",
     .step = 0.01f,
     .format = "%.2f",
     .persistenceKey = "adiskHeight"},
    {.key = "adiskLit",
     .label = "Emission intensity",
     .help = "Scales the legacy disk's light control.",
     .maximum = 4.0f,
     .step = 0.05f,
     .format = "%.2f",
     .persistenceKey = "adiskLit"},
    {.key = "adiskNoiseLOD",
     .label = "Turbulence detail",
     .help = "Adjusts the legacy disk noise detail.",
     .minimum = 1.0f,
     .maximum = 12.0f,
     .step = 0.1f,
     .format = "%.2f",
     .persistenceKey = "adiskNoiseLOD"},
    {.key = "adiskNoiseScale",
     .label = "Turbulence scale",
     .help = "Adjusts the legacy disk noise scale.",
     .maximum = 10.0f,
     .step = 0.1f,
     .format = "%.2f",
     .persistenceKey = "adiskNoiseScale"},
    {.key = "adiskSpeed",
     .label = "Disk rotation speed",
     .help = "Adjusts the legacy disk animation speed.",
     .step = 0.01f,
     .format = "%.2f",
     .persistenceKey = "adiskSpeed"},
}};

inline constexpr ControlPresentation K_DOPPLER_PRESENTATION{
    .key = "dopplerStrength",
    .label = "Doppler beaming",
    .help = "Adjusts the legacy disk brightness contrast around its rotation.",
    .maximum = 5.0f,
    .step = 0.05f,
    .format = "%.2f",
    .persistenceKey = {}};

} // namespace ui

#endif
