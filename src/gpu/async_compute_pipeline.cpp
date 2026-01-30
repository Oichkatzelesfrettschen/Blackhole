#include "async_compute_pipeline.h"

namespace gpu {

// ============================================================================
// AsyncComputePipeline Implementation
// ============================================================================

AsyncComputePipeline::AsyncComputePipeline(uint32_t max_commands)
    : current_buffer_(0), submitted_buffer_(1), state_(PipelineState::IDLE),
      gpu_timestamp_(0) {
    buffers_[0].commands.reserve(max_commands);
    buffers_[1].commands.reserve(max_commands);
    readback_.complete = true;
    readback_.mapped_ptr = nullptr;
}

AsyncComputePipeline::~AsyncComputePipeline() = default;

void AsyncComputePipeline::beginRecording() {
    state_ = PipelineState::RECORDING;
    buffers_[current_buffer_].commands.clear();
    buffers_[current_buffer_].barriers.clear();
}

void AsyncComputePipeline::recordDispatch(const ComputeCommand& cmd) {
    if (state_ != PipelineState::RECORDING) return;
    buffers_[current_buffer_].commands.push_back(cmd);
}

void AsyncComputePipeline::recordBarrier(uint32_t stage_mask) {
    if (state_ != PipelineState::RECORDING) return;
    buffers_[current_buffer_].barriers.push_back(stage_mask);
}

void AsyncComputePipeline::recordMemoryCopy(uint32_t src_ssbo, uint32_t dst_ssbo,
                                            uint32_t size) {
    // Placeholder: would issue MemoryBarrier/CopyBufferSubData
}

void AsyncComputePipeline::endRecording() {
    state_ = PipelineState::SUBMITTED;
}

void AsyncComputePipeline::submitToGPU() {
    if (state_ != PipelineState::SUBMITTED) return;

    state_ = PipelineState::EXECUTING;
    buffers_[current_buffer_].timestamp = gpu_timestamp_++;

    // In real implementation: submit command buffer to GPU queue
    // glDispatchCompute() for each recorded command
}

void AsyncComputePipeline::waitForCompletion() {
    while (state_ != PipelineState::COMPLETE) {
        // Poll GPU fence or use glClientWaitSync()
    }
}

void AsyncComputePipeline::swapBuffers() {
    submitted_buffer_ = current_buffer_;
    current_buffer_ = 1 - current_buffer_;
}

bool AsyncComputePipeline::isReadyForReadback() const {
    return state_ == PipelineState::COMPLETE;
}

void AsyncComputePipeline::beginAsyncReadback(uint32_t ssbo_id, uint32_t offset,
                                               uint32_t size) {
    readback_.complete = false;
    readback_.size = size;
    // In real implementation: bind PBO, issue glGetBufferSubData with async fence
}

bool AsyncComputePipeline::readbackComplete() const {
    return readback_.complete;
}

const uint8_t* AsyncComputePipeline::getReadbackData() const {
    return static_cast<const uint8_t*>(readback_.mapped_ptr);
}

// ============================================================================
// TileDispatcher Implementation
// ============================================================================

TileDispatcher::TileDispatcher(const TileConfig& config)
    : config_(config), current_occupancy_(0.5f) {
    uint32_t tiles_x = (config.frame_width + config.tile_size_x - 1) / config.tile_size_x;
    uint32_t tiles_y = (config.frame_height + config.tile_size_y - 1) / config.tile_size_y;

    tiles_.reserve(tiles_x * tiles_y);
    for (uint32_t y = 0; y < tiles_y; ++y) {
        for (uint32_t x = 0; x < tiles_x; ++x) {
            tiles_.push_back({x, y, 0.5f, false});
        }
    }

    computeTilePriorities();
}

std::vector<ComputeCommand> TileDispatcher::generateTileDispatches(
    uint32_t compute_shader_id) {
    std::vector<ComputeCommand> commands;

    for (const auto& tile : tiles_) {
        ComputeCommand cmd;
        cmd.compute_shader_id = compute_shader_id;
        cmd.dispatch.grid_x = (config_.tile_size_x + 15) / 16;
        cmd.dispatch.grid_y = (config_.tile_size_y + 15) / 16;
        cmd.dispatch.grid_z = 1;
        cmd.dispatch.block_x = 16;
        cmd.dispatch.block_y = 16;
        cmd.dispatch.block_z = 1;
        commands.push_back(cmd);
    }

    return commands;
}

void TileDispatcher::optimizeForOccupancy(float target_occupancy) {
    current_occupancy_ = target_occupancy;
    // Adjust tile sizes for better occupancy
}

std::vector<ComputeCommand> TileDispatcher::getPriorityTiles(uint32_t compute_shader_id,
                                                              float priority) {
    std::vector<ComputeCommand> commands;
    // Return tiles sorted by priority for progressive rendering
    return commands;
}

void TileDispatcher::computeTilePriorities() {
    // Center tiles have higher priority (foveated rendering)
    for (auto& tile : tiles_) {
        int center_x = config_.frame_width / 2;
        int center_y = config_.frame_height / 2;
        int dx = static_cast<int>(tile.x * config_.tile_size_x) - center_x;
        int dy = static_cast<int>(tile.y * config_.tile_size_y) - center_y;
        tile.priority = 1.0f / (1.0f + (dx * dx + dy * dy) / 100000.0f);
    }
}

// ============================================================================
// FramePipeline Implementation
// ============================================================================

FramePipeline::FramePipeline() : current_idx_(0), frame_submit_time_(0) {}

void FramePipeline::submitFrame(uint32_t frame_number) {
    FrameState state;
    state.frame_number = frame_number;
    state.stage = FrameStage::COMPUTE_DISPATCH;
    state.timestamp_ns = 0;
    frames_.push_back(state);
}

void FramePipeline::advance() {
    // Advance frame through pipeline stages
    if (!frames_.empty()) {
        auto& frame = frames_.front();
        switch (frame.stage) {
            case FrameStage::COMPUTE_DISPATCH:
                frame.stage = FrameStage::READBACK_WAIT;
                break;
            case FrameStage::READBACK_WAIT:
                frame.stage = FrameStage::CPU_POSTPROCESS;
                break;
            case FrameStage::CPU_POSTPROCESS:
                frames_.erase(frames_.begin());
                break;
        }
    }
}

const FramePipeline::FrameState* FramePipeline::getCurrentFrame() const {
    if (frames_.empty()) return nullptr;
    return &frames_.front();
}

double FramePipeline::getFrameTimeMS() const {
    return 16.67;  // ~60 FPS
}

double FramePipeline::getGPUUtilizationPercent() const {
    return 75.0;  // 75% utilization target
}

} // namespace gpu
