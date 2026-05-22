# Repository hygiene sweep remaining blockers

Date: 2026-05-21

## Completed in this pass

- `discobsd`: replayed local analysis/POSIX work onto `origin/master`, created and squash-merged PR #1, synced local `main`, deleted replay and backup branches.
- `v7x86-32`: deleted stale local branches that were superseded by squash-merged PR #2, archived ignored vendor subproject state to `Blackhole/v7x86-32-vendor-subprojects-20260521`, removed ignored nested vendor Git repos, and moved obsolete unrelated `/home/eirikr/Github/OS-Projects/v7x86` checkout to trash.
- `hwauditnet`: reviewed PR #1, removed tracked local session/build-log debris from the PR branch, pushed the hygiene commit, and reset local `main` to `origin/main`. Not merged because it fails the solution build with 317 Core errors plus Avalonia task loading failure.
- `openmach`: archived the uncommitted Lites header-stub experiment to `Blackhole/openmach-lites-header-stubs-20260521`, cleaned the worktree, published local committed history as PR #1, squash-merged it, deleted the PR branch, and synced local `master` to `origin/master`.
- `minix318`: archived the active merge state to `Blackhole/minix318-active-merge-state-20260521`, archived the nested `collaborativeHaskell` checkout, aborted the raw merge, pruned the stale closed-PR tracking branch, fast-forwarded to `origin/master`, and left the checkout clean.

## Blocker: hwauditnet PR #1

Command:

```sh
dotnet build HardwareAnalyzer.sln -p:EnableWindowsTargeting=true --no-restore
```

Observed result:

- CS0246 x416
- CS0051 x112
- CS0050 x64
- CS7025 x16
- CS0053 x12
- CS0535 x8
- CS0234 x4
- MSB4022 x2

Mechanism:

- `HardwareAnalyzer.Core.csproj` disables default compile items and uses a hand-maintained compile list.
- The PR adds dependencies on omitted namespaces and model files.
- Several public interfaces expose internal model types.
- TensorFlow namespace references do not resolve under the restored package graph.
- Desktop build fails on the Avalonia task path in this Linux-hosted validation.

Falsifier:

- The same command completes without those error classes.

## Resolved: openmach local header stubs

Command:

```sh
./scripts/build.sh
```

Observed result:

- Configure fails because `ccache gcc-15 -m32 -std=gnu11` cannot link a 32-bit test executable; linker cannot find compatible `libgcc`.

Mechanism:

- Host GCC is built without usable multilib runtime for `-m32` in this environment.
- Dirty tree replaces `include/mach/cthreads.h` with a minimal Lites stub before any build proof exists.
- The repository already has generated or architecture-specific header surfaces under `i386/include`.

Falsifier:

- Install/provide a working i686 compiler runtime, run `./scripts/build.sh`, and prove the header changes improve the Lites/Mach build without reducing public cthreads ABI surface.

Resolution:

- The uncommitted header-stub experiment was archived, not committed, because the build precondition failed and the stubs reduced the public cthreads surface.
- The committed local history was published separately through PR #1 and squash-merged into `master`.

## Resolved: minix318 active merge

State:

- Branch: `master...origin/master [ahead 32, behind 221]`
- Active merge head: `c9a4d1a581ea3d18f42860e7a4b102a3275ec6de`
- Index entries: 59,443
- Conflict-class entries: 55
- Nested Git repo: `collaborativeHaskell` on `main...origin/main`

Conflict classes:

```text
A 56974
AA 12
AU 17
D 878
DD 3
DU 1
M 3
R 1529
UA 3
UD 17
UU 5
?? 1
```

Mechanism:

- A massive local MINIX4-style rewrite is being merged with a much newer remote master.
- The merge contains duplicate filenames, staged generated reports, large standards-document imports, and conflicts across kernel, release tooling, docs, and setup scripts.
- This should be recovered as its own branch-level archival/replay operation, not committed as a raw merge.

Falsifier:

- A dedicated recovery branch reduces the index to resolved, reviewable commits with no `AA/AU/DD/DU/UA/UD/UU` entries, no nested Git repo, and a clean `git diff --check`.

Resolution:

- The raw merge state and nested checkout were archived rather than committed.
- Remote `master` subsequently gained the mathematical-kernel branch content as a regular merge.
- Local `master` was fast-forwarded to `origin/master` and the checkout is clean.
