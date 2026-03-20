/**
 * @file async_compute_pipeline.h
 * @brief Asynchronous GPU compute pipeline with command recording and submission
 *
 * Phase 6.1c: Overlaps compute work with raster rendering
 * - Command recording: build compute dispatch queue
 * - GPU submission: execute on separate command queue
 * - Double buffering: async fence tracking
 * - PBO streaming: pixel buffer object for async readback
 */

#pragma once

#include <vector>
#include <queue>
#include <memory>
#include <cstdint>
#include <atomic>
#include <glm/glm.hpp>

namespace gpu {

// ============================================================================
// Compute Command Structure
// ============================================================================

struct ComputeCommand {
    struct Dispatch {
      uint32_t gridX, gridY, gridZ;    // Workgroup counts
      uint32_t blockX, blockY, blockZ; // Workgroup sizes
    } dispatch;

    struct Bindings {
      uint32_t ssboCount;
      uint32_t uboCount;
      uint32_t textureCount;
      uint32_t bindingIndices[16];
    } bindings;

    uint32_t computeShaderId;
    uint32_t timestamp;  // Fence tracking
};

// ============================================================================
// Async Pipeline State Machine
// ============================================================================

enum class PipelineState : uint32_t {
  IDLE = 0,         // Ready for commands
  RECORDING = 1,    // Recording command buffer
  SUBMITTED = 2,    // On GPU queue
  EXECUTING = 3,    // GPU actively processing
  FencePending = 4, // Waiting for GPU sync
  COMPLETE = 5      // Results ready for readback
};

// ============================================================================
// Double-Buffered GPU Pipeline
// ============================================================================

class AsyncComputePipeline {
public:
  explicit AsyncComputePipeline(uint32_t maxCommands = 256);
  ~AsyncComputePipeline();

  // Command recording API
  void beginRecording();
  void recordDispatch(const ComputeCommand &cmd);
  void recordBarrier(uint32_t stageMask);
  void recordMemoryCopy(uint32_t srcSsbo, uint32_t dstSsbo, uint32_t size);
  void endRecording();

  // GPU submission
  void submitToGPU();
  void waitForCompletion();

  // Double buffer management
  void swapBuffers();
  [[nodiscard]] bool isReadyForReadback() const;

  // Async readback with PBO
  void beginAsyncReadback(uint32_t ssboId, uint32_t offset, uint32_t size); // NOLINT(readability-inconsistent-declaration-parameter-name) -- ssboId unused in stub impl
  [[nodiscard]] bool readbackComplete() const;
  [[nodiscard]] const uint8_t *getReadbackData() const;

  // State inspection
  [[nodiscard]] PipelineState getState() const { return state_; }
  [[nodiscard]] uint32_t getPendingCommandCount() const { return pending_commands_.size(); }
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
    void recordCommandToBuffer(const ComputeCommand& cmd, CommandBuffer& buf);
    void flushBarriers(CommandBuffer& buf);
};

// ============================================================================
// Tile-Based Dispatch Helper
// ============================================================================

class TileDispatcher {
public:
    struct TileConfig {
      uint32_t tileSizeX; // e.g., 32x32 pixels
      uint32_t tileSizeY;
      uint32_t frameWidth;
      uint32_t frameHeight;
    };

    explicit TileDispatcher(const TileConfig& config);

    // Generate tile dispatch commands
    std::vector<ComputeCommand> generateTileDispatches(uint32_t computeShaderId);

    // Adaptive tiling based on occupancy
    void optimizeForOccupancy(float targetOccupancy);

    // Progressive rendering: return commands for priority tiles first
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

class FramePipeline {
public:
    // Frame stages: GPU compute -> readback -> CPU processing
  enum class FrameStage { ComputeDispatch = 0, ReadbackWait = 1, CpuPostprocess = 2 };

  struct FrameState {
    uint32_t frameNumber;
    uint32_t computeFence;
    uint32_t readbackFence;
    FrameStage stage;
    uint64_t timestampNs;
  };

    FramePipeline();

    // Submit frame for processing
    void submitFrame(uint32_t frameNumber);

    // Advance pipeline stages
    void advance();

    // Get current frame being processed
    [[nodiscard]] const FrameState *getCurrentFrame() const;

    // Statistics
    static [[nodiscard]] double getFrameTimeMS();
    static [[nodiscard]] double getGPUUtilizationPercent();

  private:
    std::vector<FrameState> frames_;
    uint32_t current_idx_{0};
    uint64_t frame_submit_time_{0};
};

} // namespace gpu
