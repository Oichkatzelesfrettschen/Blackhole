# Active Debt Ledger

The generated [repo truth report](repo-truth.md) supplies current source and
CTest counts. Run `cmake --build build/Release --target repo-truth` and inspect
`build/Release/reports/repo_truth.json` before interpreting any size claim.

| Finding | Current evidence | Closure condition |
|---------|------------------|-------------------|
| Render output calibration | `docs/physics/claims_evidence.json` contains formula and mock evidence; it declares no shipping-renderer pixel oracle for EHT observations. | Capture shipping renderer pixels and compare scene metrics with independent reference data. |
| Conditional backend coverage | `ENABLE_CUDA` determines CUDA test registration; GL context availability determines whether GPU tests execute. The generated reports distinguish registration, applicability, and recorded execution. | Run CUDA and GL tests on configured hardware, retain execution and parity results. |
| Desktop game release witness | Campaign and constellation headless tests exercise core rules; desktop UI and screenshot status require a live display. | Exercise canonical scenarios through the desktop UI and retain reviewed captures. |

The [dated remediation history](../archive/2026-09-27-debt-remediation-history.md)
retains completed work, prior findings, and the July 2026 source-size capture.
Those historical line numbers and findings do not describe current source.
