/**
 * @file task_graph.cpp
 * @brief Task graph implementation.
 */

#include "game/task_graph.h"

#include <cassert>
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
  tasks_.push_back(std::move(contract));
  return tasks_.back().id;
}

const TaskContract *TaskGraph::find(TaskId taskId) const {
  for (const TaskContract &contract : tasks_) {
    if (contract.id == taskId) {
      return &contract;
    }
  }
  return nullptr;
}

void TaskGraph::activateEligible() {
  for (TaskContract &contract : tasks_) {
    if (contract.state != TaskState::Pending) {
      continue;
    }
    bool prerequisitesComplete = true;
    for (const TaskId prerequisiteId : contract.prerequisites) {
      const TaskContract *prerequisite = find(prerequisiteId);
      if (prerequisite == nullptr || prerequisite->state != TaskState::Complete) {
        prerequisitesComplete = false;
        break;
      }
    }
    if (prerequisitesComplete) {
      contract.state = TaskState::Active;
    }
  }
}

TaskGraph::FleetAdvanceResult TaskGraph::advanceFleetTasks(FleetId fleet, double properDeltaSec) {
  assert(std::isfinite(properDeltaSec) && properDeltaSec >= 0.0);
  FleetAdvanceResult result;
  // The fleet spends one local-time budget per turn, worked task by task in
  // insertion order; leftover budget rolls into the next Active task.
  double remainingBudgetSec = properDeltaSec;
  for (TaskContract &contract : tasks_) {
    if (remainingBudgetSec <= 0.0) {
      break;
    }
    if (contract.assignedFleet != fleet || contract.state != TaskState::Active) {
      continue;
    }
    const double neededSec = contract.properTimeCostSec - contract.progressSec;
    if (remainingBudgetSec >= neededSec) {
      contract.progressSec = contract.properTimeCostSec;
      contract.state = TaskState::Complete;
      result.completed.push_back(contract.id);
      result.properTimeSpentSec += neededSec;
      remainingBudgetSec -= neededSec;
    } else {
      contract.progressSec += remainingBudgetSec;
      result.properTimeSpentSec += remainingBudgetSec;
      remainingBudgetSec = 0.0;
    }
  }
  return result;
}

} // namespace game
