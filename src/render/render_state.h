/**
 * @file render_state.h
 * @brief Reified render/application state: every value that was a
 *        function-local static in main() lives here, grouped by subsystem.
 *
 * One instance is constructed in main() after window and ImGui
 * initialization; the grouped substructs let UI panels and dispatch paths
 * take exactly the state they touch (debt-ledger.md tranche
 * render-state-reification).
 */

#ifndef BLACKHOLE_RENDER_RENDER_STATE_H
#define BLACKHOLE_RENDER_RENDER_STATE_H

#include <array>
#include <memory>
#include <string>
#include <vector>

#include <glbinding/gl/types.h>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/vector_float2.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <imgui.h>
#include <ImGuizmo.h>

#include "cinematic.h"
#include "grmhd_packed_loader.h"
#include "grmhd_pbo_uploader.h"
#include "grmhd_streaming.h"
#include "hud_overlay.h"
#include "input.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "physics/lut.h"
#include "render/gpu_timing.h"
#include "render/noise_texture_cache.h"
#include "render/tesseract/tesseract_renderer.h"
#include "rmlui_overlay.h"
#include "tools/compare_harness.h"

#ifndef BLACKHOLE_HAS_CUDA
// The build variant selects CUDA declarations through preprocessor guards.
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
#define BLACKHOLE_HAS_CUDA 0
#endif

#if BLACKHOLE_HAS_CUDA
#include "cuda/cuda_render_manager.h"
#endif

namespace blackhole {

/** @brief Number of parallax background layers rendered behind the scene. */
constexpr int K_BACKGROUND_LAYERS = 3;

/** @brief Upper bound on bloom downsample/upsample chain length and texture arrays. */
constexpr int K_MAX_BLOOM_ITERATIONS = 8;

/** @brief Metadata for a single background skybox asset loaded from manifest.json. */
struct BackgroundAsset {
  std::string id;        ///< Unique asset identifier matching the manifest "id" field.
  std::string title;     ///< Human-readable display name shown in the UI.
  std::string path;      ///< Relative file path to the 2D background image on disk.
  std::string skyboxDir; ///< Directory containing 6 cubemap face PNGs (empty = use default).
};

/**
 * @brief Parameters for the Boyer-Lindquist coordinate wiregrid overlay.
 *
 * Controls the fragment-shader wiregridOverlay() call (wiregrid.glsl) and the
 * matching CUDA kernel path.  The overlay replaces the former Euclidean
 * Flamm's-paraboloid mesh, which was geometrically inconsistent with the
 * ray-traced geodesic view.
 */
struct WiregridParams {
  enum class Mode { Beauty = 0, Diagnostic = 1 };

  Mode  mode            = Mode::Beauty; ///< Intended use: beauty scene vs diagnostic teaching.
  bool  showErgosphere = true; ///< Render ergosphere boundary and interior glow.
  float gridScale      = 1.0f; ///< Grid density: 1.0 = pi/6 angular spacing; >1 = denser.
  float motionScale    = 1.0f; ///< Frame-dragging azimuth advection strength.
  float infallScale    = 0.6f; ///< Inward radial-shell advection strength.
  float strength       = 1.0f; ///< Overall overlay alpha multiplier after scene attenuation.
  float scenePreserve  = 1.0f; ///< 1 = fully defer to scene luminance, 0 = diagnostic override.
};


struct RenderState {
  /**
   * @brief Scene the frame renders. Blackhole runs the geodesic integrator;
   *        Tesseract runs the speculative, render-only tesseract pass.
   */
  enum class SceneMode { Blackhole = 0, Tesseract = 1 };

  struct SceneGroup {
    SceneMode mode = SceneMode::Blackhole;
    bool envApplied = false;
  } scene;

  /**
   * @brief Speculative tesseract scene (Thorne, The Science of Interstellar
   *        ch. 29-31): SO(4) rotation, projection, and library-of-time
   *        parameters. Render-only; none of it feeds the physics.
   */
  struct TesseractGroup {
    enum class Projection { Perspective = 0, Stereographic = 1 };
    Projection projection = Projection::Perspective;
    /// Angular rates of qL and qR as pure quaternions: qL = exp(s leftRate).
    /// Opposite equal rates give a simple rotation; equal rates give SO(3).
    std::array<float, 3> leftRate = {0.35f, 0.0f, 0.15f};
    std::array<float, 3> rightRate = {-0.35f, 0.12f, 0.0f};
    bool animate = true;
    float rotationPhase = 2.5f; ///< Rotation parameter s at wall time 0.
    float rotationSpeed = 1.0f; ///< ds per wall second while animating.
    float perspectiveDistance = 3.0f;
    float sceneScale = 1.3f;
    float viewDistance = 8.0f;
    float fovDeg = 50.0f;
    float timeSpan = 10.0f; ///< Library time extent T of every world-tube.
    float litMoment = 6.0f; ///< Library time the lit moment is centered on.
    float litWidth = 0.5f;
    bool pulseEnabled = true;
    int pulseStrand = 2;     ///< Middle shelf book.
    float pulseSpeed = 1.5f; ///< Library time per wall second.
    float pulseNow = 10.0f;  ///< Library time the pulse leaves (t_now).
    float pulsePast = 6.0f;  ///< Library time the pulse reaches (t_past).
    float pulseWidth = 0.35f;
    float lineWidthPx = 2.5f;
    float edgeIntensity = 0.9f;
    float strandIntensity = 1.0f;
    float sliceIntensity = 1.6f;
    TesseractRenderer renderer;
    HudOverlay speculativeLabel;
    bool speculativeLabelReady = false;
  } tesseract;

  struct CameraGroup {
    int cameraModeIndex = static_cast<int>(CameraMode::Input);
    float orbitTime = 0.0f;
    float orbitRadius = 15.0f;
    float orbitSpeed = 6.0f;
    bool gizmoEnabled = false;
    ImGuizmo::OPERATION gizmoOperation = ImGuizmo::TRANSLATE;
    ImGuizmo::MODE gizmoMode = ImGuizmo::WORLD;
    glm::mat4 gizmoTransform = glm::mat4(1.0f);
    bool cameraSettingsLoaded = false;
  } camera;

  struct DisplayGroup {
    float depthFar = 100.0f;
    bool displaySettingsLoaded = false;
    int swapInterval = 1;
    float renderScale = 1.0f;
  } display;

  struct OverlaysGroup {
    OverlayCurve2D curveOverlay;
    bool curveOverlayLoaded = false;
    HudOverlay controlsOverlay;
    bool controlsOverlayReady = false;
    bool controlsOverlayConfigInit = false;
    bool controlsOverlayEnabled = true;
    float controlsOverlayScale = 1.1f;
    HudOverlay perfOverlay;
    bool perfOverlayReady = false;
    bool perfOverlayConfigInit = false;
    [[maybe_unused]] bool perfOverlayEnabled = true;
    [[maybe_unused]] float perfOverlayScale = 1.0f;
    ui::RmlUiOverlay rmluiOverlay;
    bool rmluiEnabled = false;
    bool rmluiReady = false;
    int rmluiWidth = 0;
    int rmluiHeight = 0;
      // curveOverlay and curveOverlayLoaded are declared earlier near curve TSV loading
    bool curveOverlayEnabled = true;
    bool curveOverlayWindowOpen = true;
    bool firstLayout = true;
  } overlays;

  struct PostGroup {
    bool bloomSettingsLoaded = false;
    int bloomIterations = K_MAX_BLOOM_ITERATIONS;
    bool postProcessingSettingsLoaded = false;
    float bloomStrength = 0.1f;
    float bloomThreshold = 0.4f;  // A2: was hardcoded 1.0 in shader (killed disk bloom)
    float bloomKnee = 0.15f;      // A3: soft knee half-width (was binary sign())
    float bloomTone = 1.0f;       // A6: scene weight in bloom composite (was never dispatched)
    bool tonemappingEnabled = true;
    float toneExposure = 1.0f;
    float gamma = 2.5f;
    float tonemapChromaticAberrationStrength = 0.002f;
    float tonemapVignetteStrength = 1.0f;
    float tonemapFilmGrainStrength = 0.005f;
  } post;

  struct DiskGroup {
    bool gravitationalLensing = true;
    bool renderBlackHole = true;
    bool adiskEnabled = true;
    bool adiskParticle = true;
    float adiskDensityV = 2.0f;
    float adiskDensityH = 4.0f;
    float adiskHeight = 0.55f;
    float adiskLit = 0.25f;
    float adiskNoiseLOD = 5.0f;
    float adiskNoiseScale = 0.8f;
    bool useNoiseTexture = true;
    float noiseTextureScale = 0.25f;
    [[maybe_unused]] int noiseTextureSize = 32;
    float adiskSpeed = 0.5f;
    float dopplerStrength = 1.0f;
    float photonSphereGlowStrength = 1.0f;
    gl::GLuint texNoiseVolume = 0;
    bool noiseTextureReady = false;
    blackhole::NoiseTextureCache noiseCache;
  } disk;

  struct RteGroup {
      // D2: volumetric RTE
    bool  rteVolumetricEnabled = false;
    float rteOpacityScale      = 0.5f;
  } rte;

  struct StokesGroup {
      // D4: polarized Stokes IQUV
    bool  stokesEnabled        = false;
    float stokesBFieldAngle    = 0.0f;   // EVPA of projected B field [rad]
    float stokesNeScale        = 0.0f;   // Faraday rotation strength (0 = off)
  } stokes;

  struct PhysicsCoreGroup {
    float blackHoleMass = 1.0f;
    float kerrSpin = 0.0f;
    bool enablePhotonSphere = false;
    bool enableRedshift = false;
  } physicsCore;

  struct HawkingGroup {
    bool hawkingGlowEnabled = false;
    float hawkingTempScale = 1.0f;
    float hawkingGlowIntensity = 1.0f;
    bool hawkingUseLUTs = true;
    int hawkingPreset = 0; // 0=Physical, 1=Primordial, 2=Extreme
    physics::HawkingRenderer hawkingRenderer;
    bool hawkingLutsLoaded = false;
  } hawking;

  struct GrmhdGroup {
    bool useGrmhd = false;
    bool grmhdLoaded = false;
    GrmhdPackedTexture grmhdTexture;
    std::string grmhdLoadError;
    std::array<char, 256> grmhdPathBuffer{};
    bool grmhdPathInit = false;
    glm::vec3 grmhdBoundsMin = glm::vec3(-10.0f, -2.0f, -10.0f);
    glm::vec3 grmhdBoundsMax = glm::vec3(10.0f, 2.0f, 10.0f);
    bool grmhdSliceEnabled = false;
    int grmhdSliceAxis = 2;
    int grmhdSliceChannel = 0;
    float grmhdSliceCoord = 0.5f;
    bool grmhdSliceUseColorMap = true;
    bool grmhdSliceAutoRange = true;
    float grmhdSliceMin = 0.0f;
    float grmhdSliceMax = 1.0f;
    int grmhdSliceSize = 256;
    int grmhdSliceSizeCached = 0;
      // GRMHD Time-Series Playback (Phase 4.3 - streaming infrastructure)
    bool grmhdTimeSeriesEnabled = false;
    std::array<char, 256> grmhdTimeSeriesJsonBuffer{};
    std::array<char, 256> grmhdTimeSeriesBinBuffer{};
    bool grmhdTimeSeriesLoaded = false;
    int grmhdCurrentFrame = 0;
    int grmhdMaxFrame = 0;
    bool grmhdPlaying = false;
    float grmhdPlaybackSpeed = 1.0f;
    double grmhdCacheHitRate = 0.0;
    int grmhdQueueDepth = 0;
    std::unique_ptr<blackhole::GRMHDStreamer> grmhdStreamer;
      /* PBO uploader for streaming time-series tiles.  Initialized once when the
       * streamer loads a dataset and shut down when the dataset is unloaded.
       * Its texture() replaces grmhdTexture.texture for the time-series path. */
    blackhole::GrmhdPBOUploader grmhdPboUploader;
      /* C1d: second PBO uploader for the adjacent (next) GRMHD frame.
       * Holds frame N+1; blended with grmhdPboUploader (frame N) using grmhdFrameAlpha. */
    blackhole::GrmhdPBOUploader grmhdPboUploaderRight;
      /* Sub-frame blend factor [0,1): fraction of current inter-frame interval elapsed. */
    float grmhdFrameAlpha = 0.0f;
    gl::GLuint texGrmhdSlice = 0;
    gl::GLuint registeredRightTex = 0;
  } grmhd;

  struct LutsGroup {
    bool lutAssetsTried = false;
    bool lutAssetsLoaded = false;
    bool lutFromAssets = false;
    bool lutAssetOnly = false;
    bool lutAssetOnlyWarned = false;
    bool lutAssetConfigInit = false;
    float lutAssetSpin = 0.0f;
    physics::Lut1D lutAssetEmissivity;
    physics::Lut1D lutAssetRedshift;
    bool spectralLutTried = false;
    bool spectralLutLoaded = false;
    bool synchGLutCreated = false;
    bool useSpectralLut = false;
    float spectralWavelengthMin = 0.0f;
    float spectralWavelengthMax = 0.0f;
    float spectralRadiusMin = 0.0f;
    float spectralRadiusMax = 0.0f;
    bool grbModulationTried = false;
    bool grbModulationLoaded = false;
    bool useGrbModulation = false;
    bool grbTimeManual = false;
    float grbTimeManualValue = 0.0f;
    float grbTimeMin = 0.0f;
    float grbTimeMax = 1.0f;
    std::vector<float> grbModulationValues;
    gl::GLuint texGrbModulationLUT = 0;
    std::vector<float> spectralLutValues;
    bool lutInitialized = false;
    float lutSpin = 0.0f;
    float lutRadiusMin = 0.0f;
    float lutRadiusMax = 0.0f;
    float redshiftRadiusMin = 0.0f;
    float redshiftRadiusMax = 0.0f;
    gl::GLuint texEmissivityLUT = 0;
    gl::GLuint texRedshiftLUT = 0;
    gl::GLuint texPhotonGlowLUT = 0;  // Phase 8.2: Photon sphere glow effect LUT
    gl::GLuint texDiskDensityLUT = 0; // Phase 8.2: Accretion disk density profile LUT
    gl::GLuint texSpectralLUT = 0;
    gl::GLuint texSynchGLut = 0;   /**< @brief Synchrotron G(x) LUT (GL_TEXTURE_2D, height=1). */
    float lutAdiskDensityV = 0.0f;
  } luts;

  struct TargetsGroup {
    gl::GLuint texBlackhole = 0;
    gl::GLuint texBlackholeCompare = 0;
    gl::GLuint texBrightness = 0;
    gl::GLuint texBloomFinal = 0;
    gl::GLuint texTonemapped = 0;
    gl::GLuint texDepthEffects = 0;
    std::array<gl::GLuint, K_MAX_BLOOM_ITERATIONS> texDownsampled = {};
    std::array<gl::GLuint, K_MAX_BLOOM_ITERATIONS> texUpsampled = {};
    int renderWidth = 0;
    int renderHeight = 0;
    gl::GLuint sceneFbo = 0;
  } targets;

  struct RecordingGroup {
      // --record-frames: cinematic recording state
    bool         recordInitDone    = false;
    int          recordFrameIndex  = 0; // assigned from recordStartFrame after construction
    int          recordWarmup      = 0;
    float recordCinematic = 0.0f; // assigned from recordStartFrame after construction
    CamKeyframe  recordCurrentKf   = K_CINEMATIC_KEYFRAMES[0];
    float        recordCurRs       = 2.0f;
    float        recordCurIsco     = 1.0f;
  } recording;

  struct DispatchGroup {
    bool useComputeRaytracer = false;
#if BLACKHOLE_HAS_CUDA
    CudaRenderManager cudaManager;
    bool cudaVariantEnvApplied = false;
#endif
    int computeMaxSteps = 300;
    float computeStepSize = 0.1f;
    bool computeTiled = false;
    int computeTileSize = 256;
  } dispatch;

  struct CompareGroup {
    bool compareComputeFragment = false;
    int compareSampleSize = 16;
    int compareFrameStride = 1;
    DiffStats compareStats;
    DiffStats compareFullStats;
    bool compareWriteOutputs = false;
    bool compareWriteDiff = true;
    bool compareWriteSummary = true;
    float compareDiffScale = 8.0f;
    float compareThreshold = 0.02f;
    int compareMaxOutliers = 10000;       // Enable outlier gating by default
    float compareMaxOutlierFrac = 0.006f; // 0.6% tolerance for Kerr divergence
    bool compareOverridesEnabled = false;
    int compareMaxStepsOverride = 0;
    float compareStepSizeOverride = 0.0f;
    bool compareBaselineEnabled = false;
    // Bit meanings for integratorDebugFlags (bhDebugFlags shader uniform).
    static constexpr int K_INTEGRATOR_DEBUG_NAN_FLAG = 1;
    static constexpr int K_INTEGRATOR_DEBUG_RANGE_FLAG = 2;
    static constexpr int K_INTEGRATOR_DEBUG_MAXSTEPS_FLAG = 4;
    int integratorDebugFlags = 0;
    bool integratorDebugConfigInit = false;
    int compareFailureCount = 0;
    bool compareLastExceeded = false;
    int compareLastOutliers = 0;
    int compareLastOutlierLimit = 0;
    int compareSnapshotIndex = 0;
    bool compareAutoCapture = false;
    int compareAutoCount = static_cast<int>(K_COMPARE_PRESETS.size());
    int compareAutoStride = 30;
    int compareAutoRemaining = 0;
    int compareAutoStrideCounter = 0;
    bool comparePresetSweep = false;
    bool comparePresetSaved = false;
    bool compareRestorePending = false;
    int comparePresetIndex = 0;
    int comparePresetFrameCounter = 0;
    int comparePresetSettleFrames = 2;
    CameraState comparePresetSavedCamera{};
    int comparePresetSavedMode = 0;
    float comparePresetSavedOrbitRadius = 0.0f;
    float comparePresetSavedOrbitSpeed = 0.0f;
    float comparePresetSavedOrbitTime = 0.0f;
    float comparePresetSavedKerrSpin = 0.0f;
    bool captureCompareSnapshot = false;
    int compareFrameCounter = 0;
    bool compareAutoInit = false;
    bool forceInteropFragmentEnvApplied = false;
  } compare;

  struct ProbesGroup {
    bool drawIdProbeEnabled = false;
    bool drawIdProbeConfigInit = false;
    bool drawIdProbeSupported = false;
    bool multiDrawMainEnabled = false;
    bool multiDrawMainConfigInit = false;
    bool multiDrawIndirectCount = false;
    bool multiDrawSupported = false;
    bool multiDrawCountSupported = false;
    [[maybe_unused]] bool multiDrawOverlayEnabled = true;
    [[maybe_unused]] int multiDrawInstanceCount = 2;
    [[maybe_unused]] gl::GLuint multiDrawProgram = 0;
    [[maybe_unused]] gl::GLuint multiDrawInstanceBuffer = 0;
    [[maybe_unused]] gl::GLuint multiDrawCommandBuffer = 0;
    [[maybe_unused]] gl::GLuint multiDrawCountBuffer = 0;
    [[maybe_unused]] gl::GLuint multiDrawComputeProgram = 0;
    [[maybe_unused]] bool depthPrepassEnabled =
        false; // For future mesh-based disk rendering
  } probes;

  struct TimingGroup {
    bool gpuTimingEnabled = false;
    bool gpuTimingLogInit = false;
    bool gpuTimingLogEnabled = false;
    int gpuTimingLogStride = 60;
    int gpuTimingLogCounter = 0;
    int gpuTimingLogIndex = 0;
    GpuTimerSet gpuTimers;
    TimingHistory timingHistory;
  } timing;

  struct BackgroundGroup {
    gl::GLuint galaxy = 0;
    gl::GLuint colorMap = 0;
    bool baseTexturesLoaded = false;
    std::vector<BackgroundAsset> backgroundAssets;
    int backgroundIndex = 0;
    std::string backgroundLoadedId;
    std::string skyboxLoadedDir;
    gl::GLuint backgroundBase = 0;
    std::array<gl::GLuint, K_BACKGROUND_LAYERS> backgroundTextures = {};
    std::array<glm::vec4, K_BACKGROUND_LAYERS> backgroundLayerParams = {};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerDepth = {0.2f, 0.5f, 0.9f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerScale = {1.0f, 1.08f, 1.16f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
    glm::vec2 backgroundLayerGlobalOffset = glm::vec2(0.0f);
    float backgroundYawRad = 0.0f;
    float backgroundPitchRad = 0.0f;
    gl::GLuint fallback2D = 0;
    gl::GLuint fallback3D = 0;
    gl::GLuint fallbackCubemap = 0;
  } background;

  struct WiregridGroup {
    bool wiregridEnabled = false;
    WiregridParams wiregridParams;
    glm::vec4 wiregridColor = glm::vec4(0.21f, 0.62f, 0.92f, 0.16f);
    bool wiregridEnvApplied = false;
  } wiregrid;

  struct DebugGroup {
    bool debugPreRedshiftBackground = false;
    bool debugPreShapingBackground = false;
    bool debugPostShapingBackground = false;
    bool debugShaperInputs = false;
    bool debugClosestApproachState = false;
    bool debugClosestApproachTimeline = false;
    bool debugClosestApproachDirection = false;
    bool debugEscapedDirection = false;
    bool debugPreShapingBackgroundEnvApplied = false;
  } debug;

  struct ExportingGroup {
    int exportWarmup = 0;
    bool exportPerformed = false;
    int exportDone = 0;
  } exporting;

  struct DepthFxGroup {
    bool depthEffectsEnabled = true;
    bool fogEnabled = true;
    float fogDensity = 0.08f;
    float fogStart = 0.6f;
    float fogEnd = 0.98f;
    float fogColor[3] = {0.06f, 0.06f, 0.10f};
    bool edgeOutlinesEnabled = false;
    float edgeThreshold = 0.5f;
    float edgeWidth = 1.0f;
    float edgeColor[3] = {1.0f, 1.0f, 1.0f};
    bool depthDesatEnabled = true;
    float desatStrength = 0.10f;
    bool chromaDepthEnabled = false;
    bool motionParallaxHint = false;
    bool dofEnabled = false;
    float dofFocusNear = 0.3f;
    float dofFocusFar = 0.9f;
    float dofMaxRadius = 2.0f;
    float depthCurve = 1.0f;
  } depthFx;

};

} // namespace blackhole

#endif // BLACKHOLE_RENDER_RENDER_STATE_H
