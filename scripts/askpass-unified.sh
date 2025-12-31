#!/usr/bin/env sh
set -eu

if [ -n "${SUDO_ASKPASS:-}" ] && [ -x "${SUDO_ASKPASS}" ]; then
  exec "${SUDO_ASKPASS}" "$@"
fi

if [ -n "${SSH_ASKPASS:-}" ] && [ -x "${SSH_ASKPASS}" ]; then
  exec "${SSH_ASKPASS}" "$@"
fi

for candidate in \
  /home/eirikr/.local/bin/sudo-askpass-mate \
  /usr/bin/eirikr-askpass \
  /home/eirikr/.codex/bin/askpass.sh \
  ; do
  if [ -x "${candidate}" ]; then
    exec "${candidate}" "$@"
  fi
done

if command -v eirikr-askpass >/dev/null 2>&1; then
  exec eirikr-askpass "$@"
fi

echo "askpass-unified: no askpass helper found" >&2
exit 1
