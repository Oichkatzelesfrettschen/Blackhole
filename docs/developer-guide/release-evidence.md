# Release Evidence

The [machine-readable summary](release-evidence.json) lists separate release
obligations for Blackhole Simulator / Workbench and Singularity: Proper Time.
Each entry uses one of four classifications:

- **Measured fact:** a value read directly from current source or a recorded run.
- **Local inference:** a source or test relationship that still needs a product
  execution witness.
- **Approximation:** a deliberate physical model limit.
- **Unvalidated roadmap item:** a release obligation without qualifying evidence.

The [generated repo truth report](repo-truth.md) records current build options,
source sizes, registered tests, and the latest recorded test execution. The
[physics claims report](../physics/claims-evidence.md) records evidence classes
and conditional registration. A green headless campaign test is a core rule
witness; a Simulator screenshot or a Proper Time desktop release requires a live
rendering and UI witness.
