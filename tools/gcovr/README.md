# Vendored gcovr archive

`gcovr-python-8.4-vendored-source.tar.gz` is the archived form of the
previous expanded `tools/gcovr` Python snapshot.

The archive is kept in this repository because it is part of the Python tooling
surface that supports coverage-report generation for Blackhole development.  It
is intentionally archived rather than expanded so the repository keeps the
vendored object as provenance data without treating hundreds of third-party
files as editable project source.

Runtime use should still resolve `gcovr` from the developer environment.  The
CMake coverage target calls `find_program(GCOVR_EXE NAMES "gcovr")`, so this
archive is not placed on `PATH` and does not provide an executable environment.

Contents summarized from the archived tree:

- Source path before archival: `tools/gcovr`
- Archive root: `gcovr-python-8.4-vendored-source/tools/gcovr`
- Files archived: 670
- Uncompressed tracked bytes: 8613855
- Archive bytes: 1880711
- Archive SHA-256:
  `edca5615e829ffd7719df567a5ebd2203b9c88fdf32012ffc19c501098f040ce`
- Entrypoints preserved in the archive: `tools/gcovr/bin/gcovr`,
  `tools/gcovr/bin/pygmentize`

The processed manifest in `analysis.json` records package versions, file-class
counts, and the ownership decision used for future audits.
