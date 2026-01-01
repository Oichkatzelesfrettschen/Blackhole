# Sanitizer Workflows

## AddressSanitizer (ASan)

Build and test:
```bash
cmake --build --preset riced-asan
ctest --test-dir build/RicedAsan/Debug --output-on-failure
```

## ThreadSanitizer (TSan)

Build and test:
```bash
cmake --build --preset riced-tsan
ctest --test-dir build/RicedTsan/Debug --output-on-failure
```

## Notes and caveats

- If the system has a stale `LD_PRELOAD` (e.g., `mklfakeintel.so`), prefer:
  `env -u LD_PRELOAD <command>` for clean logs.
- These presets are configured for `-Werror` and use repo-local Conan state.
