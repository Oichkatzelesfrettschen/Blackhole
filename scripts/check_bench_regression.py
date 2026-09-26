#!/usr/bin/env python3
"""Compare physics_bench JSON results against a recorded baseline.

physics_bench --json emits {"config": {...}, "results": [{"name",
"avg_ms", ...}]}. This tool compares each named result's avg_ms against
the baseline and fails when any ratio exceeds the threshold. A missing
baseline is an explicit condition, never a silent pass: either record
one with --record or acknowledge the bootstrap with --allow-missing.
A recorded baseline carries a "provenance" object (host CPU, logical CPU
count, platform, UTC date, and each --provenance note); comparisons read
only "results", so the provenance never affects a verdict.
"""

import argparse
import json
import math
import os
import pathlib
import platform
import sys
import time


def load_results(path: str | pathlib.Path) -> dict[str, dict]:
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    return {entry["name"]: entry for entry in payload.get("results", [])}


def finite_ms(value: object) -> bool:
    """True for a finite, non-negative number; json.load yields NaN and
    Infinity as floats and physics_bench writes null for a non-finite timing."""
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(value)
        and value >= 0
    )


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
        "--threshold", type=float, default=0.05, help="fractional slowdown that fails (default 5%%)"
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
    if args.record:
        record(args.current[0], baseline_path, args.provenance)
        print(f"recorded baseline {baseline_path} from {args.current[0]}")
        return 0

    if not baseline_path.exists():
        print(
            f"NOTICE: no baseline at {baseline_path}; "
            f"record one with: {sys.argv[0]} --baseline {baseline_path} --record {args.current[0]}"
        )
        return 0 if args.allow_missing else 2

    baseline = load_results(baseline_path)
    failures = 0
    seen = set()
    for current_file in args.current:
        current = load_results(current_file)
        seen.update(current)
        for name, entry in sorted(current.items()):
            base = baseline.get(name)
            if not finite_ms(entry.get("avg_ms")):
                print(f"INVALID: {name} has no finite avg_ms in {current_file}")
                failures += 1
                continue
            if base is None:
                print(f"NEW: {name} has no baseline entry ({entry['avg_ms']:.3f} ms)")
                continue
            if not finite_ms(base.get("avg_ms")) or base["avg_ms"] == 0:
                print(f"INVALID: {name} has no finite, positive avg_ms in {baseline_path}")
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
    # A benchmark that stops reporting is a lost measurement, not a pass.
    for name in sorted(set(baseline) - seen):
        print(f"MISSING: {name} is in {baseline_path} but absent from this run")
        failures += 1
    if failures:
        print(
            f"{failures} failure(s): regressions beyond {args.threshold * 100:.0f}%, "
            "invalid timings, or missing benchmarks"
        )
        return 1
    print("all benchmarks within threshold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
