/**
 * @file task_graph.h
 * @brief Task contracts, prerequisites, and proper-time-driven advancement.
 *
 * Tasks live in insertion order inside the graph and are advanced in that
 * order, so identical command histories replay to identical task states.
 * Progress is paid in the assigned fleet's LOCAL proper time: a near-horizon
 * fleet with dtau/dt = 0.1 needs ten coordinate turns to do one turn's worth
 * of far-orbit work.
 */

#ifndef BLACKHOLE_GAME_TASK_GRAPH_H
#define BLACKHOLE_GAME_TASK_GRAPH_H

#include <vector>

#include "game/fleet.h"

namespace game {

enum class TaskState : std::uint8_t {
  Pending = 0,  ///< Waiting on prerequisites.
  Active = 1,   ///< Consuming the assigned fleet's proper time.
  Complete = 2, ///< Finished; completion report may still be in flight.
};

struct TaskContract {
  TaskId id = K_INVALID_TASK_ID;
  std::vector<TaskId> prerequisites;
  FleetId assignedFleet = K_INVALID_FLEET_ID;
  double properTimeCostSec = 0.0; ///< Local proper time the task consumes.
  double progressSec = 0.0;       ///< Local proper time consumed so far.
  TaskState state = TaskState::Pending;
};

class TaskGraph {
public:
  /** @brief Adds a task; returns its stable id (monotone from 1). */
  TaskId addTask(FleetId assignedFleet, double properTimeCostSec,
                 std::vector<TaskId> prerequisites = {});

  [[nodiscard]] const TaskContract *find(TaskId taskId) const;

  /** @brief Promotes every Pending task whose prerequisites are all Complete
   *         to Active, in insertion order. */
  void activateEligible();

  struct FleetAdvanceResult {
    std::vector<TaskId> completed;    ///< Ids completed this call, insertion order.
    double properTimeSpentSec = 0.0;  ///< Local proper time actually consumed (wear input).
  };

  /** @brief Spends properDeltaSec of the fleet's local proper time across its
   *         Active tasks in insertion order. */
  FleetAdvanceResult advanceFleetTasks(FleetId fleet, double properDeltaSec);

  [[nodiscard]] const std::vector<TaskContract> &tasks() const { return tasks_; }

private:
  std::vector<TaskContract> tasks_;
  TaskId nextTaskId_ = 1;
};

} // namespace game

#endif // BLACKHOLE_GAME_TASK_GRAPH_H
