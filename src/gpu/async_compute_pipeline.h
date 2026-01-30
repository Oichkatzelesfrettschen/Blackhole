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
        uint32_t grid_x, grid_y, grid_z;  // Workgroup counts
        uint32_t block_x, block_y, block_z; // Workgroup sizes
    } dispatch;

    struct Bindings {
        uint32_t ssbo_count;
        uint32_t ubo_count;
        uint32_t texture_count;
        uint32_t binding_indices[16];
    } bindings;

    uint32_t compute_shader_id;
    uint32_t timestamp;  // Fence tracking
};

// ============================================================================
// Async Pipeline State Machine
// ============================================================================

enum class PipelineState : uint32_t {
    IDLE = 0,           // Ready for commands
    RECORDING = 1,      // Recording command buffer
    SUBMITTED = 2,      // On GPU queue
    EXECUTING = 3,      // GPU actively processing
    FENCE_PENDING = 4,  // Waiting for GPU sync
    COMPLETE = 5        // Results ready for readback
};

// ============================================================================
// Double-Buffered GPU Pipeline
// ============================================================================

class AsyncComputePipeline {
public:
    explicit AsyncComputePipeline(uint32_t max_commands = 256);
    ~AsyncComputePipeline();

    // Command recording API
    void beginRecording();
    void recordDispatch(const ComputeCommand& cmd);
    void recordBarrier(uint32_t stage_mask);
    void recordMemoryCopy(uint32_t src_ssbo, uint32_t dst_ssbo, uint32_t size);
    void endRecording();

    // GPU submission
    void submitToGPU();
    void waitForCompletion();

    // Double buffer management
    void swapBuffers();
    bool isReadyForReadback() const;

    // Async readback with PBO
    void beginAsyncReadback(uint32_t ssbo_id, uint32_t offset, uint32_t size);
    bool readbackComplete() const;
    const uint8_t* getReadbackData() const;

    // State inspection
    PipelineState getState() const { return state_; }
    uint32_t getPendingCommandCount() const { return pending_commands_.size(); }
    uint32_t getGPUTimestampNS() const { return gpu_timestamp_; }

private:
    // Command buffer management
    struct CommandBuffer {
        std::vector<ComputeCommand> commands;
        std::vector<uint32_t> barriers;
        uint32_t gpu_fence;
        uint32_t timestamp;
        PipelineState state;
    };

    // Double-buffered command buffers
    CommandBuffer buffers_[2];
    uint32_t current_buffer_;
    uint32_t submitted_buffer_;

    // State tracking
    std::atomic<PipelineState> state_;
    uint32_t gpu_timestamp_;

    // Command queues
    std::queue<ComputeCommand> pending_commands_;
    std::queue<uint32_t> barrier_queue_;

    // Async readback PBO
    struct AsyncReadback {
        uint32_t pbo_id;
        uint32_t size;
        void* mapped_ptr;
        uint32_t gpu_fence;
        bool complete;
    } readback_;

    // GPU resource IDs (from OpenGL context)
    uint32_t command_buffer_id_;
    uint32_t compute_queue_id_;

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
        uint32_t tile_size_x;   // e.g., 32x32 pixels
        uint32_t tile_size_y;
        uint32_t frame_width;
        uint32_t frame_height;
    };

    explicit TileDispatcher(const TileConfig& config);

    // Generate tile dispatch commands
    std::vector<ComputeCommand> generateTileDispatches(uint32_t compute_shader_id);

    // Adaptive tiling based on occupancy
    void optimizeForOccupancy(float target_occupancy);

    // Progressive rendering: return commands for priority tiles first
    std::vector<ComputeCommand> getPriorityTiles(uint32_t compute_shader_id, float priority);

private:
    TileConfig config_;
    float current_occupancy_;

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
    enum class FrameStage {
        COMPUTE_DISPATCH = 0,
        READBACK_WAIT = 1,
        CPU_POSTPROCESS = 2
    };

    struct FrameState {
        uint32_t frame_number;
        uint32_t compute_fence;
        uint32_t readback_fence;
        FrameStage stage;
        uint64_t timestamp_ns;
    };

    FramePipeline();

    // Submit frame for processing
    void submitFrame(uint32_t frame_number);

    // Advance pipeline stages
    void advance();

    // Get current frame being processed
    const FrameState* getCurrentFrame() const;

    // Statistics
    double getFrameTimeMS() const;
    double getGPUUtilizationPercent() const;

private:
    std::vector<FrameState> frames_;
    uint32_t current_idx_;
    uint64_t frame_submit_time_;
};

} // namespace gpu
