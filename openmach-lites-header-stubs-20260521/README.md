# openmach Lites header stub experiment

This archive preserves uncommitted local header-stub work removed during repository hygiene.

The experiment added top-level Mach/MIG/Lites compatibility headers and replaced `include/mach/cthreads.h` with a minimal stub. It was not committed because the replacement drops the full CMU cthreads public API and the repository build did not reach a proof point: `./scripts/build.sh` failed earlier because the host `gcc-15 -m32` toolchain could not link a 32-bit test executable due missing compatible libgcc runtime.

Falsifier for future recovery: provide a working i686 compiler runtime, run `./scripts/build.sh`, and prove any header change preserves required cthreads ABI while fixing a concrete Lites/Mach include failure.
