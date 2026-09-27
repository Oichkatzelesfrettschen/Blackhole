#!/bin/sh
# Run a command with the host header trees the ubuntu-24.04 runner lacks
# hidden behind empty tmpfs mounts.
#
# usage: scripts/ci/without_host_headers.sh COMMAND [ARG...]
#
# A workstation that installs Boost, glm, or cpptrace into /usr/include
# resolves `__has_include(<boost/...>)` and `#include <glm/...>` where the
# runner does not, so a local build or analysis takes branches the hosted
# lanes never compile: synchrotron.h, rte_integrator.h, stokes_transport.h,
# and analytic_kerr_geodesic.h select their non-Boost fallbacks on the runner
# for every target that does not link Conan's Boost. Hiding the trees makes
# the local run see the runner's headers. Needs bwrap when any tree exists;
# with none present the command runs unchanged.
set -eu

[ "$#" -gt 0 ] || { sed -n '5p' "$0" >&2; exit 2; }

# The directory list holds fixed paths without whitespace, so word splitting
# of $mounts is intended; bwrap applies mounts in order, so the tmpfs mounts
# follow the root bind that they cover.
mounts=
for dir in /usr/include/boost /usr/include/glm /usr/include/cpptrace; do
  [ -d "$dir" ] && mounts="$mounts --tmpfs $dir"
done
[ -n "$mounts" ] || exec "$@"
command -v bwrap >/dev/null 2>&1 || {
  echo "without_host_headers: bwrap is required to hide the host header trees" >&2
  exit 2
}
# shellcheck disable=SC2086
exec bwrap --dev-bind / / $mounts -- "$@"
