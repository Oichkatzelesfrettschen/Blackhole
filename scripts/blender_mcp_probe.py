#!/usr/bin/env python3
"""Send a raw JSON command to the installed BlenderMCP addon socket."""

from __future__ import annotations

import argparse
import json
import socket
import sys
import time


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=9876)
    parser.add_argument("--type", required=True, dest="command_type")
    parser.add_argument("--params-json", default="{}")
    parser.add_argument("--timeout-seconds", type=float, default=5.0)
    parser.add_argument("--retry-interval-seconds", type=float, default=0.5)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    payload = {
        "type": args.command_type,
        "params": json.loads(args.params_json),
    }
    deadline = time.monotonic() + max(args.timeout_seconds, 0.1)
    last_error = ""
    while True:
        try:
            with socket.create_connection((args.host, args.port), timeout=2.0) as sock:
                sock.sendall(json.dumps(payload).encode("utf-8"))
                sock.shutdown(socket.SHUT_WR)
                chunks = []
                while True:
                    data = sock.recv(8192)
                    if not data:
                        break
                    chunks.append(data)
            response = json.loads(b"".join(chunks).decode("utf-8"))
            break
        except Exception as exc:
            last_error = str(exc)
            if time.monotonic() >= deadline:
                raise SystemExit(
                    f"Timed out probing BlenderMCP on {args.host}:{args.port}: {last_error}"
                ) from exc
            time.sleep(max(args.retry_interval_seconds, 0.05))
    print(json.dumps(response, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
