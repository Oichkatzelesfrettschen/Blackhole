#!/usr/bin/env bash
set -euo pipefail

unset OCIO

exec /usr/bin/OctaneServer "$@"
