/**
 * @file async_compute_pipeline.h
 * @brief Asynchronous GPU compute pipeline with command recording and submission.
 *
 * WHY: Overlapping compute dispatches with raster rendering requires a
 *      command-recording model so that dispatch parameters can be batched
 *      and submitted without stalling the main render loop on GL fence waits.
 *
 * WHAT: Three cooperating classes:
 *   - AsyncComputePipeline: double-buffered command buffer + PBO readback.
 *   - TileDispatcher: generates per-tile dispatch commands for a given frame.
 *   - FramePipeline: 3-stage (compute -> readback -> CPU post-process) frame queue.
 *
 * HOW:
 *   pipeline.beginRecording();
 *   pipeline.recordDispatch(cmd);
 *   pipeline.endRecording();
 *   pipeline.submitToGPU();
 *   pipeline.swapBuffers();
 *   // next frame: read results while GPU works on new frame
 *   if (pipeline.isReadyForReadback()) { ... }
 *
 * Note: this module is a scaffolded implementation (Phase 6.1c stub).
 *       GL calls in submitToGPU() and beginAsyncReadback() are marked
 *       as placeholders pending full integration with the render path.
 */

#pragma once

#include <atomic>
#include <cstdint>
#include <memory>
#include <queue>
#include <vector>

#include <glm/glm.hpp>

namespace gpu {

// ============================================================================
// Compute Command Structure
// ============================================================================

/**
 * @brief A single recorded compute dispatch command with shader and binding info.
 *
 * Passed to AsyncComputePipeline::recordDispatch() during command recording.
 * The pipeline stores these in a double-buffered CommandBuffer and replays
 * them on submitToGPU().
 */
struct ComputeCommand {
  /** @brief Workgroup grid and block dimensions for glDispatchCompute(). */
  struct Dispatch {
    uint32_t gridX, gridY, gridZ;    /**< @brief Workgroup counts in each dimension. */
    uint32_t blockX, blockY, blockZ; /**< @brief Threads per workgroup in each dimension. */
  } dispatch;

  /** @brief Shader resource binding indices for SSBOs, UBOs, and textures. */
  struct Bindings {
    uint32_t ssboCount;              /**< @brief Number of active SSBO bindings. */
    uint32_t uboCount;               /**< @brief Number of active UBO bindings. */
    uint32_t textureCount;           /**< @brief Number of active texture bindings. */
    uint32_t bindingIndices[16];     /**< @brief GL binding point indices. */
  } bindings;

  uint32_t computeShaderId; /**< @brief GL program object ID for the compute shader. */
  uint32_t timestamp;       /**< @brief Monotonic counter used for GPU fence tracking. */
};

// ============================================================================
// Async Pipeline State Machine
// ============================================================================

/**
 * @brief State machine states for the async compute pipeline.
 *
 * Transitions: IDLE -> RECORDING -> SUBMITTED -> EXECUTING -> FencePending -> COMPLETE -> IDLE.
 */
enum class PipelineState : uint32_t {
  IDLE         = 0, /**< @brief No commands recorded; ready to begin a new recording pass. */
  RECORDING    = 1, /**< @brief Command buffer is open; recordDispatch() calls are accepted. */
  SUBMITTED    = 2, /**< @brief Recording ended; commands are queued for GPU submission. */
  EXECUTING    = 3, /**< @brief Commands have been dispatched to the GPU. */
  FencePending = 4, /**< @brief Waiting for the GPU sync fence to signal. */
  COMPLETE     = 5  /**< @brief GPU work is done; results are ready for readback. */
};

// ============================================================================
// Double-Buffered GPU Pipeline
// ============================================================================

/**
 * @brief Double-buffered async compute pipeline with PBO readback.
 *
 * The pipeline alternates between two internal CommandBuffers so that the
 * CPU can record commands for frame N+1 while the GPU executes frame N.
 * A PBO-based readback path allows asynchronous transfer of compute results
 * back to the CPU without a glFinish() stall.
 *
 * Typical per-frame usage:
 *   1. beginRecording()
 *   2. recordDispatch() / recordBarrier() (repeat as needed)
 *   3. endRecording()
 *   4. submitToGPU()
 *   5. swapBuffers()
 *   6. (next frame) if isReadyForReadback(): beginAsyncReadback()
 */
class AsyncComputePipeline {
public:
  /**
   * @brief Construct the pipeline and pre-allocate command buffer storage.
   * @param maxCommands Initial capacity for the per-buffer command vector.
   */
  explicit AsyncComputePipeline(uint32_t maxCommands = 256);
  ~AsyncComputePipeline();

  /** @brief Open the current command buffer for recording; clears prior commands. */
  void beginRecording();

  /**
   * @brief Append a compute dispatch to the current command buffer.
   *
   * No-op if the pipeline is not in RECORDING state.
   * @param cmd Dispatch parameters, shader ID, and binding indices.
   */
  void recordDispatch(const ComputeCommand &cmd);

  /**
   * @brief Insert a pipeline barrier into the current command buffer.
   *
   * No-op if the pipeline is not in RECORDING state.
   * @param stageMask GL memory barrier bits (e.g., GL_SHADER_STORAGE_BARRIER_BIT).
   */
  void recordBarrier(uint32_t stageMask);

  /**
   * @brief Record a buffer-to-buffer memory copy (stub -- not yet implemented).
   * @param srcSsbo Source SSBO binding index.
   * @param dstSsbo Destination SSBO binding index.
   * @param size    Number of bytes to copy.
   */
  static void recordMemoryCopy(uint32_t srcSsbo, uint32_t dstSsbo, uint32_t size);

  /** @brief Close the command buffer and transition state to SUBMITTED. */
  void endRecording();

  /**
   * @brief Dispatch all recorded commands to the GPU.
   *
   * Transitions state from SUBMITTED to EXECUTING.  A real implementation
   * calls glDispatchCompute() for each recorded ComputeCommand.
   */
  void submitToGPU();

  /** @brief Spin-wait until the pipeline reaches COMPLETE state. */
  void waitForCompletion();

  /** @brief Rotate the double buffer: submitted buffer becomes the read buffer. */
  void swapBuffers();

  /** @brief True when state is COMPLETE and results may be read back. */
  [[nodiscard]] bool isReadyForReadback() const;

  /**
   * @brief Initiate an asynchronous PBO readback of an SSBO region.
   *
   * Sets readback state to in-progress.  A real implementation binds a PBO
   * and issues glGetBufferSubData with an async fence.
   *
   * @param ssboId  GL SSBO binding index to read (currently unused in stub).
   * @param offset  Byte offset within the SSBO.
   * @param size    Number of bytes to read.
   */
  void beginAsyncReadback(uint32_t ssboId, uint32_t offset,
                          uint32_t size); // NOLINT(readability-inconsistent-declaration-parameter-name)
                                          // -- ssboId unused in stub impl

  /** @brief True once the async readback has completed and data is available. */
  [[nodiscard]] bool readbackComplete() const;

  /**
   * @brief Pointer to the CPU-side readback buffer, or nullptr if not ready.
   * @return Pointer to the mapped PBO memory containing the readback data.
   */
  [[nodiscard]] const uint8_t *getReadbackData() const;

  /** @brief Current pipeline state (thread-safe atomic read). */
  [[nodiscard]] PipelineState getState() const { return state_; }

  /** @brief Number of commands currently queued for submission. */
  [[nodiscard]] uint32_t getPendingCommandCount() const { return pending_commands_.size(); }

  /** @brief Monotonic GPU dispatch counter used for fence tracking. */
  [[nodiscard]] uint32_t getGPUTimestampNS() const { return gpu_timestamp_; }

private:
  // Command buffer management
  struct CommandBuffer {
    std::vector<ComputeCommand> commands;
    std::vector<uint32_t> barriers;
    uint32_t gpuFence{};
    uint32_t timestamp{};
    PipelineState state{};
  };

  // Double-buffered command buffers
  CommandBuffer buffers_[2];
  uint32_t current_buffer_{0};
  uint32_t submitted_buffer_{1};

  // State tracking
  std::atomic<PipelineState> state_;
  uint32_t gpu_timestamp_{0};

  // Command queues
  std::queue<ComputeCommand> pending_commands_;
  std::queue<uint32_t> barrier_queue_;

  // Async readback PBO
  struct AsyncReadback {
    uint32_t pboId;
    uint32_t size;
    void *mappedPtr;
    uint32_t gpuFence;
    bool complete;
  } readback_{};

  // GPU resource IDs (from OpenGL context)
  uint32_t command_buffer_id_{};
  uint32_t compute_queue_id_{};

  // Helper methods
  void recordCommandToBuffer(const ComputeCommand &cmd, CommandBuffer &buf);
  void flushBarriers(CommandBuffer &buf);
};

// ============================================================================
// Tile-Based Dispatch Helper
// ============================================================================

/**
 * @brief Generates per-tile compute dispatch commands for a full render frame.
 *
 * Divides a frame into fixed-size tiles and assigns each tile a center-weighted
 * priority (higher priority near the image center for foveated rendering).
 * Use generateTileDispatches() to produce the full command list, or
 * getPriorityTiles() for progressive rendering ordered by priority.
 */
class TileDispatcher {
public:
  /** @brief Configuration for the tile grid covering one render frame. */
  struct TileConfig {
    uint32_t tileSizeX;   /**< @brief Tile width in pixels (e.g., 32). */
    uint32_t tileSizeY;   /**< @brief Tile height in pixels (e.g., 32). */
    uint32_t frameWidth;  /**< @brief Total frame width in pixels. */
    uint32_t frameHeight; /**< @brief Total frame height in pixels. */
  };

  /**
   * @brief Build the tile grid and compute initial center-weighted priorities.
   * @param config Tile and frame dimensions.
   */
  explicit TileDispatcher(const TileConfig &config);

  /**
   * @brief Generate one ComputeCommand per tile covering the full frame.
   * @param computeShaderId GL program ID for the compute shader.
   * @return Vector of dispatch commands, one per tile, in raster order.
   */
  std::vector<ComputeCommand> generateTileDispatches(uint32_t computeShaderId);

  /**
   * @brief Adjust tile size to hit a target SM occupancy.
   * @param targetOccupancy Desired occupancy fraction in [0, 1].
   */
  void optimizeForOccupancy(float targetOccupancy);

  /**
   * @brief Return dispatch commands for tiles above a priority threshold.
   *
   * Intended for progressive rendering: high-priority (center) tiles are
   * returned first so the viewer sees a sharp center before the periphery.
   *
   * @param computeShaderId GL program ID for the compute shader.
   * @param priority        Minimum tile priority score to include.
   * @return Filtered and sorted dispatch commands.
   */
  static std::vector<ComputeCommand> getPriorityTiles(uint32_t computeShaderId, float priority);

private:
  TileConfig config_;
  float current_occupancy_{0.5f};

  struct Tile {
    uint32_t x, y;
    float priority;
    bool rendered;
  };
  std::vector<Tile> tiles_;

  void computeTilePriorities();
};

// ============================================================================
// Frame Pipelining: 3-Stage Pipeline
// ============================================================================

/**
 * @brief 3-stage frame pipeline: GPU compute -> readback wait -> CPU post-process.
 *
 * Frames are submitted with submitFrame() and advanced through stages with
 * advance().  Each advance() call moves the front-of-queue frame one stage
 * forward; when it completes CpuPostprocess it is retired and removed.
 *
 * Designed to overlap GPU execution of frame N with CPU post-processing of
 * frame N-1, targeting the 16.67 ms budget for 60 fps.
 */
class FramePipeline {
public:
  /** @brief The three serial stages a frame passes through. */
  enum class FrameStage {
    ComputeDispatch = 0, /**< @brief GPU compute shaders are dispatched. */
    ReadbackWait    = 1, /**< @brief Waiting for async PBO readback to complete. */
    CpuPostprocess  = 2  /**< @brief CPU tonemap / compositing pass. */
  };

  /** @brief Per-frame tracking state for the pipeline. */
  struct FrameState {
    uint32_t frameNumber;    /**< @brief Monotonic frame counter. */
    uint32_t computeFence;   /**< @brief GL sync object for compute completion. */
    uint32_t readbackFence;  /**< @brief GL sync object for PBO readback completion. */
    FrameStage stage;        /**< @brief Current pipeline stage. */
    uint64_t timestampNs;    /**< @brief Wall-clock nanoseconds at submitFrame(). */
  };

  FramePipeline();

  /**
   * @brief Enqueue a new frame at the ComputeDispatch stage.
   * @param frameNumber Monotonic frame index for tracking.
   */
  void submitFrame(uint32_t frameNumber);

  /** @brief Advance the front-of-queue frame by one stage; retire it when done. */
  void advance();

  /**
   * @brief Return the frame currently at the front of the pipeline.
   * @return Pointer to the current FrameState, or nullptr if the pipeline is empty.
   */
  [[nodiscard]] const FrameState *getCurrentFrame() const;

  /**
   * @brief Target frame time in milliseconds (hardcoded 16.67 ms for 60 fps).
   * @return Frame time in milliseconds.
   */
  static [[nodiscard]] double getFrameTimeMS();

  /**
   * @brief Target GPU utilization percentage (hardcoded 75%).
   * @return GPU utilization as a percentage.
   */
  static [[nodiscard]] double getGPUUtilizationPercent();

private:
  std::vector<FrameState> frames_;
  uint32_t current_idx_{0};
  uint64_t frame_submit_time_{0};
};

} // namespace gpu
