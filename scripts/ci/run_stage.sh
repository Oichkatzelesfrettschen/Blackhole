#!/usr/bin/env bash
# Retain command failures and resource costs even when a CI stage fails.
set -euo pipefail
stage_name="${1:?usage: run_stage.sh NAME COMMAND [ARG ...]}"
shift
if [[ ! "$stage_name" =~ ^[a-z][a-z0-9-]*$ || $# -eq 0 ]]; then
  echo "Expected a stage name and command" >&2
  exit 2
fi
mkdir -p build/ci-reports
stage_status=0
/usr/bin/time -v -o "build/ci-reports/${stage_name}.time" \
  "$@" > >(tee "build/ci-reports/${stage_name}.log") 2>&1 || stage_status=$?
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    printf '\n### %s (exit %s)\n\n```text\n' "$stage_name" "$stage_status"
    cat "build/ci-reports/${stage_name}.time"
    printf '```\n'
  } >> "$GITHUB_STEP_SUMMARY"
fi
exit "$stage_status"
