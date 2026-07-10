#!/usr/bin/env python3
"""Compare physics_bench JSON results against a recorded baseline.

physics_bench --json emits {"config": {...}, "results": [{"name",
"avg_ms", ...}]}. This tool compares each named result's avg_ms against
the baseline and fails when any ratio exceeds the threshold. A missing
baseline is an explicit condition, never a silent pass: either record
one with --record or acknowledge the bootstrap with --allow-missing.
"""

import argparse
import json
import pathlib
import shutil
import sys


def load_results(path):
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    return {entry["name"]: entry for entry in payload.get("results", [])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("current", nargs="+",
                        help="JSON files produced by physics_bench --json")
    parser.add_argument("--baseline", default="bench/baseline-riced.json",
                        help="recorded baseline JSON (default: %(default)s)")
    parser.add_argument("--threshold", type=float, default=0.05,
                        help="fractional slowdown that fails (default 5%%)")
    parser.add_argument("--record", action="store_true",
                        help="copy the first current file to the baseline path")
    parser.add_argument("--allow-missing", action="store_true",
                        help="exit 0 with a notice when no baseline exists")
    args = parser.parse_args()

    baseline_path = pathlib.Path(args.baseline)
    if args.record:
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.current[0], baseline_path)
        print(f"recorded baseline {baseline_path} from {args.current[0]}")
        return 0

    if not baseline_path.exists():
        print(f"NOTICE: no baseline at {baseline_path}; "
              f"record one with: {sys.argv[0]} --record " + args.current[0])
        return 0 if args.allow_missing else 2

    baseline = load_results(baseline_path)
    failures = 0
    for current_file in args.current:
        current = load_results(current_file)
        for name, entry in sorted(current.items()):
            base = baseline.get(name)
            if base is None:
                print(f"NEW: {name} has no baseline entry "
                      f"({entry['avg_ms']:.3f} ms)")
                continue
            ratio = entry["avg_ms"] / base["avg_ms"]
            if ratio > 1.0 + args.threshold:
                print(f"REGRESSION: {name} {base['avg_ms']:.3f} -> "
                      f"{entry['avg_ms']:.3f} ms ({(ratio - 1) * 100:+.1f}%)")
                failures += 1
            else:
                print(f"ok: {name} {(ratio - 1) * 100:+.1f}%")
    if failures:
        print(f"{failures} regression(s) beyond "
              f"{args.threshold * 100:.0f}% threshold")
        return 1
    print("all benchmarks within threshold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
