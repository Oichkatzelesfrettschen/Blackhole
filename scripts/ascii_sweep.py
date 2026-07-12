#!/usr/bin/env python3
"""Convert or reject non-ASCII characters in living documentation.

The repository documentation policy is ASCII-only outside docs/archive/.
Run with --fix to rewrite files through the explicit mapping below; any
character absent from the mapping is an error in both modes, so nothing
is silently mangled. Run without --fix as a verifier (exit 1 on any
non-ASCII), which is how CI holds the line.
"""

import argparse
import pathlib
import re
import sys

MAPPING = {
    # box drawing -> ASCII art
    "─": "-", "━": "=", "│": "|", "┌": "+",
    "┐": "+", "└": "+", "┘": "+", "├": "+",
    "┤": "+", "┬": "+", "┴": "+", "┼": "+",
    "═": "=", "█": "#", "□": "[ ]",
    # arrows
    "→": "->", "←": "<-", "↔": "<->",
    "▶": ">", "▼": "v", "▲": "^",
    # dashes, quotes, ellipsis, bullets
    "—": "--", "–": "-", "‘": "'", "’": "'",
    "“": '"', "”": '"', "…": "...", "·": "*",
    "•": "*",
    # status marks
    "✓": "yes", "✗": "no", "✅": "[done]",
    "❌": "[fail]", "⭐": "*", "✨": "*",
    "⚠": "[warn]", "️": "",
    # math and units
    "×": "x", "≈": "~=", "≤": "<=", "≥": ">=",
    "±": "+/-", "∝": "~", "∂": "d", "°": " deg",
    "☉": "sun",
    # superscripts
    "¹": "^1", "²": "^2", "³": "^3", "⁰": "^0",
    "⁴": "^4", "⁵": "^5", "⁶": "^6", "⁷": "^7",
    "⁸": "^8", "⁹": "^9", "⁻": "^-",
    # math operators and physics symbols
    "√": "sqrt", "ℏ": "hbar", "Ṁ": "Mdot",
    # greek (physics prose)
    "α": "alpha", "β": "beta", "γ": "gamma",
    "δ": "delta", "ε": "eps", "η": "eta",
    "θ": "theta", "κ": "kappa", "λ": "lambda",
    "μ": "mu", "ν": "nu", "ρ": "rho",
    "σ": "sigma", "τ": "tau", "π": "pi",
    "Γ": "Gamma", "Θ": "Theta", "Λ": "Lambda",
    "Σ": "Sigma", "Φ": "Phi", "Ω": "Omega",
}


def sweep(path, fix):
    text = path.read_text(encoding="utf-8")
    unmapped = {}
    out = []
    for lineno, line in enumerate(text.splitlines(keepends=True), 1):
        for ch in line:
            if ord(ch) > 127 and ch not in MAPPING:
                unmapped.setdefault(repr(ch), []).append(lineno)
        if fix:
            for src, dst in MAPPING.items():
                line = line.replace(src, dst)
            # collapse per-digit superscript runs: 10^-^2^7 -> 10^-27
            run = re.compile(r"(\^-?\d*)\^(\d)")
            while run.search(line):
                line = run.sub(r"\1\2", line)
        out.append(line)
    if unmapped:
        for ch, lines in sorted(unmapped.items()):
            print(f"{path}: unmapped {ch} on lines {lines[:5]}")
        return False
    if fix:
        new_text = "".join(out)
        if new_text != text:
            path.write_text(new_text, encoding="utf-8")
            print(f"rewrote {path}")
    elif any(ord(c) > 127 for c in text):
        offending = sorted({repr(c) for c in text if ord(c) > 127})
        print(f"{path}: non-ASCII present {offending[:8]}")
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fix", action="store_true",
                        help="rewrite files through the mapping")
    parser.add_argument("paths", nargs="*",
                        help="files to process (default: living docs)")
    args = parser.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    if args.paths:
        targets = [pathlib.Path(p) for p in args.paths]
    else:
        targets = [p for p in (root / "docs").rglob("*.md")
                   if "archive" not in p.parts]
        targets += [root / n for n in
                    ("AGENTS.md", "README.md", "CHANGELOG.md",
                     "gemini.md", "CLAUDE.md")]

    ok = True
    for path in sorted(targets):
        if path.exists():
            ok = sweep(path, args.fix) and ok
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
