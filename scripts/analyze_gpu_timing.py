#!/usr/bin/env python3
"""
GPU Timing CSV Analyzer

Parses gpu_timing.csv logs and generates performance reports with outlier detection.

Usage:
    python scripts/analyze_gpu_timing.py [logs/perf/gpu_timing.csv]
    python scripts/analyze_gpu_timing.py --json  # Machine-readable output
    python scripts/analyze_gpu_timing.py --threshold 2.5  # Custom IQR multiplier
"""

import argparse
import csv
import json
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from statistics import mean, median, stdev, quantiles
from typing import Optional


@dataclass
class TimingStats:
    """Statistics for a single timing metric."""

    name: str
    count: int = 0
    mean_ms: float = 0.0
    median_ms: float = 0.0
    std_ms: float = 0.0
    min_ms: float = 0.0
    max_ms: float = 0.0
    p25_ms: float = 0.0
    p75_ms: float = 0.0
    p95_ms: float = 0.0
    p99_ms: float = 0.0
    iqr_ms: float = 0.0
    outlier_count: int = 0
    outlier_indices: list = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "count": self.count,
            "mean_ms": round(self.mean_ms, 4),
            "median_ms": round(self.median_ms, 4),
            "std_ms": round(self.std_ms, 4),
            "min_ms": round(self.min_ms, 4),
            "max_ms": round(self.max_ms, 4),
            "p25_ms": round(self.p25_ms, 4),
            "p75_ms": round(self.p75_ms, 4),
            "p95_ms": round(self.p95_ms, 4),
            "p99_ms": round(self.p99_ms, 4),
            "iqr_ms": round(self.iqr_ms, 4),
            "outlier_count": self.outlier_count,
            "outlier_pct": round(100.0 * self.outlier_count / self.count, 2) if self.count > 0 else 0.0,
        }


@dataclass
class GpuTimingReport:
    """Complete GPU timing analysis report."""

    csv_path: str
    sample_count: int
    duration_sec: float
    resolution: tuple
    compute_active_pct: float
    kerr_spin_range: tuple
    metrics: dict  # name -> TimingStats
    has_outliers: bool = False

    def to_dict(self) -> dict:
        return {
            "csv_path": self.csv_path,
            "sample_count": self.sample_count,
            "duration_sec": round(self.duration_sec, 2),
            "resolution": f"{self.resolution[0]}x{self.resolution[1]}",
            "compute_active_pct": round(self.compute_active_pct, 1),
            "kerr_spin_range": [round(self.kerr_spin_range[0], 4), round(self.kerr_spin_range[1], 4)],
            "has_outliers": self.has_outliers,
            "metrics": {k: v.to_dict() for k, v in self.metrics.items()},
        }


def compute_stats(name: str, values: list, indices: list, iqr_threshold: float = 1.5) -> TimingStats:
    """Compute statistics and detect outliers using IQR method."""
    if not values:
        return TimingStats(name=name)

    stats = TimingStats(name=name)
    stats.count = len(values)
    stats.mean_ms = mean(values)
    stats.median_ms = median(values)
    stats.min_ms = min(values)
    stats.max_ms = max(values)

    if len(values) >= 2:
        stats.std_ms = stdev(values)
        quarts = quantiles(values, n=4)
        stats.p25_ms = quarts[0]
        stats.p75_ms = quarts[2]
        stats.iqr_ms = stats.p75_ms - stats.p25_ms

        # Percentiles
        percentiles = quantiles(values, n=100)
        if len(percentiles) >= 95:
            stats.p95_ms = percentiles[94]
        if len(percentiles) >= 99:
            stats.p99_ms = percentiles[98]

        # IQR outlier detection
        lower_bound = stats.p25_ms - iqr_threshold * stats.iqr_ms
        upper_bound = stats.p75_ms + iqr_threshold * stats.iqr_ms

        for i, v in enumerate(values):
            if v < lower_bound or v > upper_bound:
                stats.outlier_count += 1
                if len(stats.outlier_indices) < 20:  # Limit stored indices
                    stats.outlier_indices.append(indices[i])

    return stats


def parse_gpu_timing_csv(csv_path: str, iqr_threshold: float = 1.5) -> Optional[GpuTimingReport]:
    """Parse gpu_timing.csv and compute statistics."""
    if not os.path.exists(csv_path):
        return None

    # Columns to analyze
    metric_columns = [
        "cpu_ms",
        "gpu_fragment_ms",
        "gpu_compute_ms",
        "gpu_bloom_ms",
        "gpu_tonemap_ms",
        "gpu_depth_ms",
        "gpu_grmhd_slice_ms",
    ]

    # Storage
    indices = []
    times = []
    widths = []
    heights = []
    compute_active = []
    kerr_spins = []
    metric_values = {col: [] for col in metric_columns}

    with open(csv_path, "r", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                idx = int(row["index"])
                indices.append(idx)
                times.append(float(row["time_sec"]))
                widths.append(int(row["width"]))
                heights.append(int(row["height"]))
                compute_active.append(int(row["compute_active"]))
                kerr_spins.append(float(row["kerr_spin"]))

                for col in metric_columns:
                    val = float(row[col])
                    # Filter out zero values for GPU metrics (not active)
                    if col.startswith("gpu_") and val == 0.0:
                        continue
                    metric_values[col].append((idx, val))
            except (KeyError, ValueError) as e:
                print(f"Warning: Skipping malformed row: {e}", file=sys.stderr)
                continue

    if not indices:
        return None

    # Build report
    duration = times[-1] - times[0] if len(times) > 1 else 0.0
    resolution = (widths[0], heights[0]) if widths else (0, 0)
    compute_pct = 100.0 * sum(compute_active) / len(compute_active) if compute_active else 0.0
    spin_range = (min(kerr_spins), max(kerr_spins)) if kerr_spins else (0.0, 0.0)

    metrics = {}
    has_outliers = False
    for col in metric_columns:
        vals = metric_values[col]
        if vals:
            col_indices = [v[0] for v in vals]
            col_values = [v[1] for v in vals]
            stats = compute_stats(col, col_values, col_indices, iqr_threshold)
            metrics[col] = stats
            if stats.outlier_count > 0:
                has_outliers = True

    return GpuTimingReport(
        csv_path=csv_path,
        sample_count=len(indices),
        duration_sec=duration,
        resolution=resolution,
        compute_active_pct=compute_pct,
        kerr_spin_range=spin_range,
        metrics=metrics,
        has_outliers=has_outliers,
    )


def print_text_report(report: GpuTimingReport) -> None:
    """Print human-readable report to stdout."""
    print("=" * 70)
    print("GPU TIMING ANALYSIS REPORT")
    print("=" * 70)
    print(f"CSV Path:        {report.csv_path}")
    print(f"Samples:         {report.sample_count}")
    print(f"Duration:        {report.duration_sec:.1f} sec")
    print(f"Resolution:      {report.resolution[0]}x{report.resolution[1]}")
    print(f"Compute Active:  {report.compute_active_pct:.1f}%")
    print(f"Kerr Spin:       [{report.kerr_spin_range[0]:.4f}, {report.kerr_spin_range[1]:.4f}]")
    print()

    # Summary table
    print(f"{'Metric':<22} {'Mean':>8} {'Median':>8} {'Std':>8} {'P95':>8} {'P99':>8} {'Outliers':>10}")
    print("-" * 70)

    for name, stats in report.metrics.items():
        outlier_str = f"{stats.outlier_count} ({100*stats.outlier_count/stats.count:.1f}%)" if stats.count > 0 else "0"
        print(
            f"{name:<22} {stats.mean_ms:>8.2f} {stats.median_ms:>8.2f} "
            f"{stats.std_ms:>8.2f} {stats.p95_ms:>8.2f} {stats.p99_ms:>8.2f} {outlier_str:>10}"
        )

    print()

    # Outlier details
    if report.has_outliers:
        print("OUTLIERS DETECTED:")
        print("-" * 70)
        for name, stats in report.metrics.items():
            if stats.outlier_count > 0:
                indices_str = ", ".join(str(i) for i in stats.outlier_indices[:10])
                if stats.outlier_count > 10:
                    indices_str += f", ... (+{stats.outlier_count - 10} more)"
                print(f"  {name}: {stats.outlier_count} outliers at indices [{indices_str}]")
        print()
        print("Outlier bounds: Q1 - 1.5*IQR to Q3 + 1.5*IQR")
    else:
        print("No outliers detected.")

    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(description="Analyze GPU timing CSV logs")
    parser.add_argument(
        "csv_path",
        nargs="?",
        default="logs/perf/gpu_timing.csv",
        help="Path to gpu_timing.csv (default: logs/perf/gpu_timing.csv)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output machine-readable JSON",
    )
    parser.add_argument(
        "--threshold",
        type=float,
        default=1.5,
        help="IQR multiplier for outlier detection (default: 1.5)",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        help="Write report to file instead of stdout",
    )

    args = parser.parse_args()

    report = parse_gpu_timing_csv(args.csv_path, args.threshold)

    if report is None:
        print(f"Error: Could not parse {args.csv_path}", file=sys.stderr)
        if not os.path.exists(args.csv_path):
            print(f"File does not exist. Generate with: BLACKHOLE_GPU_TIMING_LOG=1 ./build/Release/Blackhole", file=sys.stderr)
        sys.exit(1)

    if args.json:
        output = json.dumps(report.to_dict(), indent=2)
    else:
        # Capture text output
        import io
        buf = io.StringIO()
        old_stdout = sys.stdout
        sys.stdout = buf
        print_text_report(report)
        sys.stdout = old_stdout
        output = buf.getvalue()

    if args.output:
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Report written to {args.output}")
    else:
        print(output)

    # Exit with status based on outliers
    sys.exit(1 if report.has_outliers else 0)


if __name__ == "__main__":
    main()
