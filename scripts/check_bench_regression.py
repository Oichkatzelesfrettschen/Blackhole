#!/usr/bin/env python3
"""Compare physics_bench JSON results against a recorded baseline.

physics_bench --json emits {"config": {...}, "results": [{"name",
"avg_ms", ...}]}. This tool compares each named result's avg_ms against
the baseline and fails when any ratio exceeds the threshold. A missing
baseline is an explicit condition, never a silent pass: either record
one with --record or acknowledge the bootstrap with --allow-missing.
Every current result is validated first (finite, positive avg_ms and a
positive iteration count), so neither --record nor --allow-missing
accepts a run that produced no measurement. A current file whose workload
("config": rays, steps, iterations, and the other physics_bench inputs)
differs from the baseline's is a CONFIG failure and is not timed against
it. A recorded baseline carries a "provenance" object (host CPU, logical
CPU count, platform, UTC date, and each --provenance note), which never
affects a verdict.
"""

import argparse
import json
import math
import os
import pathlib
import platform
import sys
import time

# physics_bench's "config" fields that define the measured workload; a
# timing is comparable only with a baseline recorded for the same values.
WORKLOAD_KEYS = (
    "rays",
    "steps",
    "iterations",
    "warmup",
    "lut_size",
    "spin",
    "mass_solar",
    "mdot",
    "gpu_enabled",
    "gpu_width",
    "gpu_height",
    "gpu_iterations",
    "gpu_step",
    "gpu_max_distance",
)


def load_run(path: str | pathlib.Path) -> tuple[object, dict[str, dict]]:
    """Return the file's "config" object (None when absent) and its results by name."""
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    results = {entry["name"]: entry for entry in payload.get("results", [])}
    return payload.get("config"), results


def config_mismatch(baseline: object, current: object) -> list[str]:
    """Workload fields that differ between two config objects."""
    if not isinstance(baseline, dict) or not isinstance(current, dict):
        return ["a config object is missing"]
    return [
        f"{key} {baseline.get(key)!r} != {current.get(key)!r}"
        for key in WORKLOAD_KEYS
        if baseline.get(key) != current.get(key)
    ]


def threshold_arg(text: str) -> float:
    try:
        value = float(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not a number: {text!r}") from error
    if not math.isfinite(value) or value < 0:
        raise argparse.ArgumentTypeError(f"must be a finite, non-negative fraction: {text!r}")
    return value


def invalid_reason(entry: dict) -> str | None:
    """Why an entry is not a measurement, or None when it is one.

    A measurement has a finite, positive avg_ms and a positive iteration
    count. json.load yields NaN and Infinity as floats, physics_bench writes
    null for a non-finite timing, and a benchmark that never ran reports zero
    iterations and a zero time; none of these is a timing to compare.
    """
    avg = entry.get("avg_ms")
    if not isinstance(avg, (int, float)) or isinstance(avg, bool) or not math.isfinite(avg):
        return "no finite avg_ms"
    if avg <= 0:
        return f"avg_ms {avg} is not positive"
    iterations = entry.get("iterations")
    if not isinstance(iterations, int) or isinstance(iterations, bool) or iterations <= 0:
        return f"iterations {iterations!r} is not a positive count"
    return None


def host_cpu_model() -> str:
    try:
        with open("/proc/cpuinfo", encoding="utf-8") as handle:
            for line in handle:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.processor() or "unknown"


def record(current_path: str, baseline_path: pathlib.Path, notes: list[str]) -> None:
    with open(current_path, encoding="utf-8") as handle:
        payload = json.load(handle)
    payload["provenance"] = {
        "cpu": host_cpu_model(),
        "logical_cpus": os.cpu_count(),
        "platform": platform.platform(),
        # time.gmtime works on every Python 3 release; datetime.UTC is 3.11+.
        "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "notes": notes,
    }
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    with open(baseline_path, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2)
        handle.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("current", nargs="+", help="JSON files produced by physics_bench --json")
    parser.add_argument(
        "--baseline",
        default="bench/baseline-riced.json",
        help="recorded baseline JSON (default: %(default)s)",
    )
    parser.add_argument(
        "--threshold",
        type=threshold_arg,
        default=0.05,
        help="fractional slowdown that fails, finite and >= 0 (default 5%%)",
    )
    parser.add_argument(
        "--record",
        action="store_true",
        help="write the first current file, plus provenance, to the baseline path",
    )
    parser.add_argument(
        "--provenance",
        action="append",
        default=[],
        metavar="NOTE",
        help="with --record: a provenance note such as the compiler and preset (repeatable)",
    )
    parser.add_argument(
        "--allow-missing", action="store_true", help="exit 0 with a notice when no baseline exists"
    )
    args = parser.parse_args()

    baseline_path = pathlib.Path(args.baseline)
    runs = [(path, *load_run(path)) for path in args.current]
    failures = 0
    for path, _config, results in runs:
        for name, entry in sorted(results.items()):
            reason = invalid_reason(entry)
            if reason is not None:
                print(f"INVALID: {name} in {path}: {reason}")
                failures += 1

    if args.record:
        if failures:
            print(f"not recording {baseline_path}: the run has {failures} invalid result(s)")
            return 1
        record(args.current[0], baseline_path, args.provenance)
        print(f"recorded baseline {baseline_path} from {args.current[0]}")
        return 0

    if not baseline_path.exists():
        print(
            f"NOTICE: no baseline at {baseline_path}; "
            f"record one with: {sys.argv[0]} --baseline {baseline_path} --record {args.current[0]}"
        )
        if failures:
            return 1
        return 0 if args.allow_missing else 2

    baseline_config, baseline = load_run(baseline_path)
    for path, config, current in runs:
        mismatch = config_mismatch(baseline_config, config)
        if mismatch:
            print(
                f"CONFIG: {path} measured a different workload than {baseline_path}: "
                + "; ".join(mismatch)
            )
            failures += 1
            continue
        for name, entry in sorted(current.items()):
            if invalid_reason(entry) is not None:
                continue
            base = baseline.get(name)
            if base is None:
                print(f"NEW: {name} has no baseline entry ({entry['avg_ms']:.3f} ms)")
                continue
            reason = invalid_reason(base)
            if reason is not None:
                print(f"INVALID: {name} in {baseline_path}: {reason}")
                failures += 1
                continue
            ratio = entry["avg_ms"] / base["avg_ms"]
            if ratio > 1.0 + args.threshold:
                print(
                    f"REGRESSION: {name} {base['avg_ms']:.3f} -> "
                    f"{entry['avg_ms']:.3f} ms ({(ratio - 1) * 100:+.1f}%)"
                )
                failures += 1
            else:
                print(f"ok: {name} {(ratio - 1) * 100:+.1f}%")
        # Each file is one run compared with the whole baseline, so a baseline
        # entry absent from this file is a lost measurement even when another
        # file reports it.
        for name in sorted(set(baseline) - set(current)):
            print(f"MISSING: {name} is in {baseline_path} but absent from {path}")
            failures += 1
    if failures:
        print(
            f"{failures} failure(s): regressions beyond {args.threshold * 100:.0f}%, "
            "invalid timings, workload mismatches, or missing benchmarks"
        )
        return 1
    print("all benchmarks within threshold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
