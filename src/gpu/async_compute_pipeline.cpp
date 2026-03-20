#include "async_compute_pipeline.h"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace gpu {

// ============================================================================
// AsyncComputePipeline Implementation
// ============================================================================

AsyncComputePipeline::AsyncComputePipeline(uint32_t maxCommands) : state_(PipelineState::IDLE) {
  buffers_[0].commands.reserve(maxCommands);
  buffers_[1].commands.reserve(maxCommands);
  readback_.complete = true;
  readback_.mappedPtr = nullptr;
}

AsyncComputePipeline::~AsyncComputePipeline() = default;

void AsyncComputePipeline::beginRecording() {
  state_ = PipelineState::RECORDING;
  buffers_[current_buffer_].commands.clear();
  buffers_[current_buffer_].barriers.clear();
}

void AsyncComputePipeline::recordDispatch(const ComputeCommand &cmd) {
  if (state_ != PipelineState::RECORDING) {
    return;
  }
  buffers_[current_buffer_].commands.push_back(cmd);
}

void AsyncComputePipeline::recordBarrier(uint32_t stageMask) {
  if (state_ != PipelineState::RECORDING) {
    return;
  }
  buffers_[current_buffer_].barriers.push_back(stageMask);
}

void AsyncComputePipeline::recordMemoryCopy(uint32_t srcSsbo, uint32_t dstSsbo, uint32_t size) {
  // Placeholder: would issue MemoryBarrier/CopyBufferSubData
}

void AsyncComputePipeline::endRecording() {
  state_ = PipelineState::SUBMITTED;
}

void AsyncComputePipeline::submitToGPU() {
  if (state_ != PipelineState::SUBMITTED) {
    return;
  }

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

void AsyncComputePipeline::beginAsyncReadback(uint32_t /*ssboId*/, uint32_t /*offset*/,
                                              uint32_t size) {
  readback_.complete = false;
  readback_.size = size;
  // In real implementation: bind PBO, issue glGetBufferSubData with async fence
}

bool AsyncComputePipeline::readbackComplete() const {
  return readback_.complete;
}

const uint8_t *AsyncComputePipeline::getReadbackData() const {
  return static_cast<const uint8_t *>(readback_.mappedPtr);
}

// ============================================================================
// TileDispatcher Implementation
// ============================================================================

TileDispatcher::TileDispatcher(const TileConfig &config) : config_(config) {
  uint32_t const tilesX = (config.frameWidth + config.tileSizeX - 1) / config.tileSizeX;
  uint32_t const tilesY = (config.frameHeight + config.tileSizeY - 1) / config.tileSizeY;

  tiles_.reserve(static_cast<size_t>(tilesX) * tilesY);
  for (uint32_t y = 0; y < tilesY; ++y) {
    for (uint32_t x = 0; x < tilesX; ++x) {
      tiles_.push_back({.x = x, .y = y, .priority = 0.5f, .rendered = false});
    }
  }

  computeTilePriorities();
}

std::vector<ComputeCommand> TileDispatcher::generateTileDispatches(uint32_t computeShaderId) {
  std::vector<ComputeCommand> commands;

  for (const auto &tile : tiles_) {
    ComputeCommand cmd{};
    cmd.computeShaderId = computeShaderId;
    cmd.dispatch.gridX = (config_.tileSizeX + 15) / 16;
    cmd.dispatch.gridY = (config_.tileSizeY + 15) / 16;
    cmd.dispatch.gridZ = 1;
    cmd.dispatch.blockX = 16;
    cmd.dispatch.blockY = 16;
    cmd.dispatch.blockZ = 1;
    commands.push_back(cmd);
  }

  return commands;
}

void TileDispatcher::optimizeForOccupancy(float targetOccupancy) {
  current_occupancy_ = targetOccupancy;
  // Adjust tile sizes for better occupancy
}

std::vector<ComputeCommand> TileDispatcher::getPriorityTiles(uint32_t /*computeShaderId*/,
                                                             float /*priority*/) {
  std::vector<ComputeCommand> commands;
  // Return tiles sorted by priority for progressive rendering
  return commands;
}

void TileDispatcher::computeTilePriorities() {
  // Center tiles have higher priority (foveated rendering)
  for (auto &tile : tiles_) {
    int const centerX = static_cast<int>(config_.frameWidth / 2);
    int const centerY = static_cast<int>(config_.frameHeight / 2);
    int const dx = static_cast<int>(tile.x * config_.tileSizeX) - centerX;
    int const dy = static_cast<int>(tile.y * config_.tileSizeY) - centerY;
    tile.priority = 1.0f / (1.0f + (static_cast<float>((dx * dx) + (dy * dy)) / 100000.0f));
  }
}

// ============================================================================
// FramePipeline Implementation
// ============================================================================

FramePipeline::FramePipeline() = default;

void FramePipeline::submitFrame(uint32_t frameNumber) {
  FrameState state{};
  state.frameNumber = frameNumber;
  state.stage = FrameStage::ComputeDispatch;
  state.timestampNs = 0;
  frames_.push_back(state);
}

void FramePipeline::advance() {
  // Advance frame through pipeline stages
  if (!frames_.empty()) {
    auto &frame = frames_.front();
    switch (frame.stage) {
    case FrameStage::ComputeDispatch:
      frame.stage = FrameStage::ReadbackWait;
      break;
    case FrameStage::ReadbackWait:
      frame.stage = FrameStage::CpuPostprocess;
      break;
    case FrameStage::CpuPostprocess:
      frames_.erase(frames_.begin());
      break;
    }
  }
}

const FramePipeline::FrameState *FramePipeline::getCurrentFrame() const {
  if (frames_.empty()) {
    return nullptr;
  }
  return &frames_.front();
}

double FramePipeline::getFrameTimeMS() {
  return 16.67; // ~60 FPS
}

double FramePipeline::getGPUUtilizationPercent() {
  return 75.0; // 75% utilization target
}

} // namespace gpu
