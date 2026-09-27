/**
 * @file task_graph.cpp
 * @brief Task graph implementation.
 */

#include "game/task_graph.h"

#include <cassert>
#include <cstddef>
#include <cmath> // IWYU pragma: keep -- std::isfinite inside assert, compiled out under NDEBUG
#include <utility>
#include <vector>

#include "game/fleet.h"

namespace game {

TaskId TaskGraph::addTask(FleetId assignedFleet, double properTimeCostSec,
                          std::vector<TaskId> prerequisites) {
  assert(std::isfinite(properTimeCostSec) && properTimeCostSec > 0.0);
  TaskContract contract;
  contract.id = nextTaskId_++;
  contract.prerequisites = std::move(prerequisites);
  contract.assignedFleet = assignedFleet;
  contract.properTimeCostSec = properTimeCostSec;
  std::size_t remaining = 0;
  for (const TaskId prerequisiteId : contract.prerequisites) {
    const TaskContract *prerequisite = find(prerequisiteId);
    if (prerequisite == nullptr || prerequisite->state != TaskState::Complete) {
      ++remaining;
      dependents_[prerequisiteId].push_back(contract.id);
    }
  }
  remainingPrerequisites_.push_back(remaining);
  if (remaining == 0) {
    readyTasks_.insert(contract.id);
  }
  tasks_.push_back(std::move(contract));
  return tasks_.back().id;
}

const TaskContract *TaskGraph::find(TaskId taskId) const {
  if (taskId == K_INVALID_TASK_ID || taskId >= nextTaskId_) {
    return nullptr;
  }
  return &tasks_[static_cast<std::size_t>(taskId - 1)];
}

void TaskGraph::activateEligible() {
  lastTurnVisits_ = 0;
  for (const TaskId taskId : readyTasks_) {
    ++lastTurnVisits_;
    TaskContract &contract = tasks_[static_cast<std::size_t>(taskId - 1)];
    contract.state = TaskState::Active;
    activeTasks_[contract.assignedFleet].insert(taskId);
  }
  readyTasks_.clear();
}

TaskGraph::FleetAdvanceResult TaskGraph::advanceFleetTasks(FleetId fleet, double properDeltaSec) {
  assert(std::isfinite(properDeltaSec) && properDeltaSec >= 0.0);
  FleetAdvanceResult result;
  // The fleet spends one local-time budget per turn, worked task by task in
  // insertion order; leftover budget rolls into the next Active task.
  double remainingBudgetSec = properDeltaSec;
  auto &fleetTasks = activeTasks_[fleet];
  for (auto task = fleetTasks.begin(); task != fleetTasks.end();) {
    if (remainingBudgetSec <= 0.0) {
      break;
    }
    ++lastTurnVisits_;
    TaskContract &contract = tasks_[static_cast<std::size_t>(*task - 1)];
    const double neededSec = contract.properTimeCostSec - contract.progressSec;
    if (remainingBudgetSec >= neededSec) {
      contract.progressSec = contract.properTimeCostSec;
      contract.state = TaskState::Complete;
      result.completed.push_back(contract.id);
      result.properTimeSpentSec += neededSec;
      remainingBudgetSec -= neededSec;
      const auto dependents = dependents_.find(contract.id);
      if (dependents != dependents_.end()) {
        for (const TaskId dependentId : dependents->second) {
          std::size_t &remaining = remainingPrerequisites_[static_cast<std::size_t>(dependentId - 1)];
          if (--remaining == 0) {
            readyTasks_.insert(dependentId);
          }
        }
        dependents_.erase(dependents);
      }
      task = fleetTasks.erase(task);
    } else {
      contract.progressSec += remainingBudgetSec;
      result.properTimeSpentSec += remainingBudgetSec;
      remainingBudgetSec = 0.0;
      ++task;
    }
  }
  return result;
}

} // namespace game
