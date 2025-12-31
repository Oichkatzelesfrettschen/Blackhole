#!/usr/bin/env python3
"""Generate GRB modulation LUTs from analytic pulse envelopes."""

from __future__ import annotations

import argparse
import csv
import json
import math
from datetime import datetime, timezone
from pathlib import Path


def gaussian(t: float, t0: float, sigma: float) -> float:
    if sigma <= 0.0:
        return 0.0
    z = (t - t0) / sigma
    return math.exp(-0.5 * z * z)


def fred(t: float, t0: float, tau_rise: float, tau_decay: float) -> float:
    x = t - t0
    if x <= 0.0 or tau_rise <= 0.0 or tau_decay <= 0.0:
        return 0.0
    return math.exp(-tau_rise / x - x / tau_decay)


def fredx(t: float, t0: float, tau_rise: float, tau_decay: float,
          xi: float, gamma: float) -> float:
    x = t - t0
    if x <= 0.0 or tau_rise <= 0.0 or tau_decay <= 0.0:
        return 0.0
    return math.exp(-tau_rise / x - x / tau_decay) * (1.0 + xi * x) ** gamma


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", choices=["gaussian", "fred", "fredx"], default="gaussian")
    parser.add_argument("--t-min", type=float, default=0.0)
    parser.add_argument("--t-max", type=float, default=100.0)
    parser.add_argument("--size", type=int, default=512)
    parser.add_argument("--t0", type=float, default=10.0)
    parser.add_argument("--sigma", type=float, default=2.0)
    parser.add_argument("--tau-rise", type=float, default=0.5)
    parser.add_argument("--tau-decay", type=float, default=8.0)
    parser.add_argument("--xi", type=float, default=0.0)
    parser.add_argument("--gamma", type=float, default=1.0)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent / "assets" / "luts",
    )
    args = parser.parse_args()

    t_min = args.t_min
    t_max = max(args.t_max, t_min + 1e-6)
    size = max(args.size, 8)
    times = [t_min + (t_max - t_min) * i / (size - 1) for i in range(size)]

    if args.model == "gaussian":
        values = [gaussian(t, args.t0, args.sigma) for t in times]
    elif args.model == "fred":
        values = [fred(t, args.t0, args.tau_rise, args.tau_decay) for t in times]
    else:
        values = [
            fredx(t, args.t0, args.tau_rise, args.tau_decay, args.xi, args.gamma)
            for t in times
        ]

    vmax = max(values) if values else 1.0
    if vmax > 0.0:
        values = [v / vmax for v in values]

    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "grb_modulation_lut.csv"
    meta_path = output_dir / "grb_modulation_meta.json"

    with csv_path.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["time_s", "value"])
        for t, v in zip(times, values):
            writer.writerow([t, v])

    meta = {
        "model": args.model,
        "t_min": t_min,
        "t_max": t_max,
        "size": size,
        "t0": args.t0,
        "sigma": args.sigma,
        "tau_rise": args.tau_rise,
        "tau_decay": args.tau_decay,
        "xi": args.xi,
        "gamma": args.gamma,
        "units": {"time": "s"},
        "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    with meta_path.open("w", encoding="utf-8") as handle:
        json.dump(meta, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print("Wrote GRB modulation LUT:", csv_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
