#!/usr/bin/env python3
"""Generate GRB LUT assets from external datasets (cleanroom pipeline).

This script does not copy code. It re-emits public data tables with
metadata so the runtime can consume a consistent HDF5 layout.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path


def require_h5py():
    try:
        import h5py  # type: ignore
    except Exception as exc:  # pragma: no cover - runtime guard
        raise SystemExit(
            "h5py is required to generate GRB LUTs. Install it in your venv."
        ) from exc
    return h5py


def export_jetfit_table(source: Path, output: Path) -> None:
    h5py = require_h5py()
    output.parent.mkdir(parents=True, exist_ok=True)

    with h5py.File(source, "r") as src, h5py.File(output, "w") as dst:
        for name in src.keys():
            src_obj = src[name]
            if hasattr(src_obj, "shape"):
                dst.create_dataset(name, data=src_obj[()])
            else:
                grp = dst.create_group(name)
                for sub_name in src_obj.keys():
                    grp.create_dataset(sub_name, data=src_obj[sub_name][()])

        dst.attrs["source_repo"] = "openuniverse/JetFit"
        dst.attrs["source_path"] = str(source)
        dst.attrs["generated_utc"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        dst.attrs["schema"] = "jetfit_table_v1"
        dst.attrs["units"] = "See JetFit Table.h5 + literature (Wu & MacFadyen 2018)."
        dst.attrs["citation"] = (
            "Wu & MacFadyen 2018 (ApJ 869:55); Duffell & MacFadyen 2013 (ApJL 775:L9)."
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--jetfit-table",
        type=Path,
        default=Path("/home/eirikr/Github/openuniverse/JetFit/Table.h5"),
        help="Path to JetFit Table.h5",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent.parent / "assets" / "luts" / "grb_spectral_table.h5",
        help="Output HDF5 path",
    )
    args = parser.parse_args()

    if not args.jetfit_table.exists():
        raise SystemExit(f"JetFit table not found: {args.jetfit_table}")

    export_jetfit_table(args.jetfit_table, args.output)
    print("Wrote GRB spectral LUT:", args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
