# Repo Truth

The repository now exposes a generated, measured build inventory so the docs do
not need to guess what a configured tree contains.

## Generate the report

```bash
cmake --build --preset release --target repo-truth
```

The target writes:

- `build/<preset>/reports/repo_truth.json`
- `build/<preset>/reports/repo_truth.md`

## What it records

- configured build options from `CMakeCache.txt`
- `ctest -N` inventory for the configured build tree
- visible configure presets from `CMakePresets.json`
- detected local tools such as `blender`, `OctaneBlender`, `blender-mcp`,
  `nvcc`, `nvidia-smi`, shader tools, and profiling tools
- selected system packages queried through `pacman -Q` when available
- generated Blender/Octane evidence when present:
  - addon manifest and package verification
  - addon staging report
  - Blender smoke and Octane smoke reports
  - Blender interactive and harsh-lighting benchmark reports
  - Dream Textures runtime and direct-pipeline verification reports
  - Dream Textures four-mode conditioning sweep reports and artifact summaries
  - baseline and harsh-lighting Blender-vs-Octane conditioning parity reports
  - per-host Dream Textures conditioning policy reports
  - aggregate Dream Textures conditioning trend summary
  - per-host Dream Textures policy-preparation warm-cache reports
  - background and production prepare-only Dream Textures policy reports
  - per-host Dream Textures policy stale-refresh reports after scene mutation
  - stable Blender and Octane showcase gallery reports and copied stills
  - verified smoke-report summaries

## Usage

Use the generated report when updating status, requirements, and module docs.
If a narrative document disagrees with the report, the report is the preferred
starting point for reconciliation.

## Current scope

This target is still intentionally narrower than the full project scope. It now
captures build, package, and integration evidence for the Blender/Octane lane,
the first Blender interactive benchmark report, and the physics claims report,
including conditioned Dream Textures quality floors and scene-policy outputs,
but it does not by itself complete the full scientific-audit workflow.
