"""Compare dependency identities while allowing local recipe export timestamps."""

import argparse
import difflib
import json
from pathlib import Path


REFERENCE_FIELDS = ("requires", "build_requires", "python_requires", "config_requires")


def normalized_lock(path: Path) -> str:
    lock = json.loads(path.read_text(encoding="utf-8"))
    for field in REFERENCE_FIELDS:
        if field in lock:
            # Conan assigns a fresh timestamp when identical local bytes are
            # exported. The recipe revision before '%' identifies those bytes.
            lock[field] = [reference.split("%", 1)[0] for reference in lock[field]]
    return json.dumps(lock, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("committed", type=Path)
    parser.add_argument("resolved", type=Path)
    arguments = parser.parse_args()
    committed = normalized_lock(arguments.committed)
    resolved = normalized_lock(arguments.resolved)
    if committed == resolved:
        return 0
    print("".join(difflib.unified_diff(
        committed.splitlines(keepends=True), resolved.splitlines(keepends=True),
        fromfile=str(arguments.committed), tofile=str(arguments.resolved),
    )), end="")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
