# Blackhole Documentation Index

**WHY:** Centralized navigation for all project documentation
**WHAT:** Index of design docs, guides, roadmaps, and API references
**HOW:** Start here, follow links to specific topics

---

## Quick Links

**Getting Started:**
- [BUILDING.md](BUILDING.md) - Build instructions for all platforms
- [TROUBLESHOOTING.md](TROUBLESHOOTING.md) - Common issues and solutions
- [SIMD_GUIDE.md](SIMD_GUIDE.md) - SIMD tier selection and performance

**Project Management:**
- [MASTER_ROADMAP.md](MASTER_ROADMAP.md) - Canonical roadmap (Phases 0-5)
- [STATUS.md](STATUS.md) - Current project status
- [AGENTS.md](../AGENTS.md) - Agent coordination and contribution guide

**Physics & Accuracy:**
- [CLEANROOM_DECISIONS.md](CLEANROOM_DECISIONS.md) - Physics validation strategy
- [COMPARE_SWEEP.md](COMPARE_SWEEP.md) - Compute/fragment parity analysis
- [../rocq/README.md](../rocq/README.md) - Formal verification (Rocq proofs)

**Performance:**
- [../bench/README.md](../bench/README.md) - Benchmark suite
- [SIMD_GUIDE.md](SIMD_GUIDE.md) - SIMD optimization guide
- [HALIDE_FEASIBILITY.md](HALIDE_FEASIBILITY.md) - Halide integration analysis

**Data Pipelines:**
- [GRMHD_INGESTION_PLAN.md](GRMHD_INGESTION_PLAN.md) - GRMHD data streaming
- [BACKGROUND_ASSET_PIPELINE.md](BACKGROUND_ASSET_PIPELINE.md) - Background assets
- [IMAGE_SOURCES.md](IMAGE_SOURCES.md) - Image attribution

**Development:**
- [GLSL_BUILD_GUIDE.md](GLSL_BUILD_GUIDE.md) - Shader development
- [INTEROP_BEST_PRACTICES.md](INTEROP_BEST_PRACTICES.md) - Cross-language interop
- [../tools/README.md](../tools/README.md) - Utility tools

---

## Documentation Structure

```
docs/
├── README.md                    # This file - documentation index
├── BUILDING.md                  # Build instructions
├── TROUBLESHOOTING.md           # Common issues
├── SIMD_GUIDE.md               # SIMD performance guide
├── MASTER_ROADMAP.md           # Canonical roadmap
├── STATUS.md                   # Project status
│
├── Physics & Validation/
│   ├── CLEANROOM_DECISIONS.md
│   ├── COMPARE_SWEEP.md
│   └── DEPENDENCY_MATRIX.md
│
├── Planning & Execution/
│   ├── EXECUTION_PLAN_2026Q1.md
│   ├── EIGEN_REFACTOR_PLAN.md
│   ├── GRB_MODULATION_PLAN.md
│   └── GRMHD_INGESTION_PLAN.md
│
├── Development Guides/
│   ├── GLSL_BUILD_GUIDE.md
│   ├── INTEROP_BEST_PRACTICES.md
│   └── HUD.md
│
├── Assets & Data/
│   ├── BACKGROUND_ASSET_PIPELINE.md
│   ├── IMAGE_SOURCES.md
│   └── IMAGE_CANDIDATES.md
│
└── archive/
    └── 2026Q1/                 # Quarterly snapshots
```

---

## Topic Categories

### 1. Getting Started

New to the project? Start here:
1. Read [../README.md](../README.md) - Project overview
2. Read [BUILDING.md](BUILDING.md) - Build the project
3. Read [MASTER_ROADMAP.md](MASTER_ROADMAP.md) - Understand project phases
4. Read [../AGENTS.md](../AGENTS.md) - Contribution workflow

### 2. Physics Implementation

Understanding the black hole physics:
- [CLEANROOM_DECISIONS.md](CLEANROOM_DECISIONS.md) - Validation methodology
- [COMPARE_SWEEP.md](COMPARE_SWEEP.md) - Accuracy analysis
- [../rocq/README.md](../rocq/README.md) - Formal proofs
- [../rocq/docs/PHASE2_VALIDATION.md](../rocq/docs/PHASE2_VALIDATION.md) - OCaml extraction

### 3. Performance Optimization

Making it fast:
- [SIMD_GUIDE.md](SIMD_GUIDE.md) - CPU vectorization
- [../bench/README.md](../bench/README.md) - Benchmarking
- [HALIDE_FEASIBILITY.md](HALIDE_FEASIBILITY.md) - Auto-scheduling

### 4. Data Pipelines

Working with GRMHD and image data:
- [GRMHD_INGESTION_PLAN.md](GRMHD_INGESTION_PLAN.md) - GRMHD streaming
- [BACKGROUND_ASSET_PIPELINE.md](BACKGROUND_ASSET_PIPELINE.md) - Background images
- [IMAGE_SOURCES.md](IMAGE_SOURCES.md) - Attribution

### 5. Build System

CMake, dependencies, presets:
- [BUILDING.md](BUILDING.md) - Build instructions
- [DEPENDENCY_MATRIX.md](DEPENDENCY_MATRIX.md) - Dependency graph
- [TROUBLESHOOTING.md](TROUBLESHOOTING.md) - Common build issues

### 6. Shader Development

Writing and debugging GLSL:
- [GLSL_BUILD_GUIDE.md](GLSL_BUILD_GUIDE.md) - Shader workflow
- [HUD.md](HUD.md) - ImGui interface
- [../shader/README.md](../shader/README.md) - Shader organization

---

## Archive Policy

**Quarterly Snapshots:**
- End-of-quarter docs archived to `archive/YYYYQ#/`
- Preserves historical design decisions
- Current docs remain in `docs/` root

**Archive Structure:**
```
archive/
└── 2026Q1/
    ├── README.md               # Quarter summary
    ├── ROADMAP.md             # Roadmap snapshot
    ├── STATUS.md              # Status snapshot
    └── EXECUTION_PLAN.md      # Execution snapshot
```

---

## Document Conventions

**Frontmatter (WHY/WHAT/HOW):**
All new documents should start with:
```markdown
**WHY:** Goal or rationale
**WHAT:** Scope and artifacts
**HOW:** Repeatable steps
```

**Linking:**
- Use relative paths: `[BUILDING.md](BUILDING.md)`
- Link to source files: `[kerr.h](../src/physics/kerr.h)`
- Link to tools: `[physics_bench](../bench/physics_bench.cpp)`

**Updates:**
- Add "Last Updated: YYYY-MM-DD" at document end
- Update MASTER_ROADMAP.md when completing phases
- Archive outdated docs to `archive/`

---

## Contributing to Documentation

**When to Update:**
- After completing a roadmap phase
- After major refactors or rewrites
- When fixing bugs mentioned in TROUBLESHOOTING.md
- When adding new features or tools

**Documentation Standards:**
- Keep docs under 500 lines (split if larger)
- Use code blocks with language hints
- Include command examples with expected output
- Link to related docs and source files

---

**Last Updated:** 2026-01-29
**Maintainer:** See ../AGENTS.md for contributors
