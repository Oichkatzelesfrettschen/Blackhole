#!/bin/sh
# Run a command with the host header trees the ubuntu-24.04 runner lacks
# hidden behind empty read-only tmpfs mounts.
#
# usage: scripts/ci/without_host_headers.sh COMMAND [ARG...]
#
# A workstation that installs Boost, glm, or cpptrace into /usr/include
# resolves `__has_include(<boost/...>)` and `#include <glm/...>` where the
# runner does not, so a local build or analysis takes branches the hosted
# lanes never compile: synchrotron.h, rte_integrator.h, stokes_transport.h,
# and analytic_kerr_geodesic.h select their non-Boost fallbacks on the runner
# for every target that does not link Conan's Boost. Hiding the trees makes
# the local run see the runner's headers.
#
# An outer user namespace maps the caller to root so that mount(8) accepts
# the tmpfs mounts in a private mount namespace; an inner user namespace maps
# back to the caller's uid and gid, so the command runs, and writes files, as
# the caller. The mount namespace copies the existing mounts as they stand
# instead of re-binding them, so an autofs or network mount that is expired
# or unreachable does not stop the command. Needs util-linux unshare 2.38 or
# newer (--map-user) when any tree exists; with none present the command runs
# unchanged.
set -eu

[ "$#" -gt 0 ] || { sed -n '5p' "$0" >&2; exit 2; }

hide=
for dir in /usr/include/boost /usr/include/glm /usr/include/cpptrace; do
  [ -d "$dir" ] && hide="$hide $dir"
done
[ -n "$hide" ] || exec "$@"

command -v unshare >/dev/null 2>&1 || {
  echo "without_host_headers: util-linux unshare is required to hide$hide" >&2
  exit 2
}
uid=$(id -u)
gid=$(id -g)
# $hide holds fixed paths without whitespace; the command and its arguments
# pass through as "$@" so no argument is re-split or re-quoted.
exec unshare --user --map-root-user --mount -- sh -c '
  hide=$1 uid=$2 gid=$3
  shift 3
  for dir in $hide; do
    mount -t tmpfs -o ro,mode=0755 tmpfs "$dir"
  done
  exec unshare --user --map-user="$uid" --map-group="$gid" -- "$@"
' without_host_headers "$hide" "$uid" "$gid" "$@"
