#!/usr/bin/env python3
"""Re-emit Lean/Lake build errors as GitHub workflow annotations.

Diagnostic only: this script never changes a step's pass/fail status.
It reads the build logs written by the CI steps (via `tee`) and prints
`::error file=...,line=...,col=...::<message>` commands so that the first
Lean errors are visible through the check-run annotations API, even when the
raw job log cannot be downloaded.
"""
import re
import sys
from pathlib import Path

ERR = re.compile(r"^error: ([^:\s]+\.lean):(\d+):(\d+): ?(.*)$")
MAX_ERRORS = 10
MAX_LINES = 40


def esc_data(s: str) -> str:
    return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def esc_prop(s: str) -> str:
    return esc_data(s).replace(":", "%3A").replace(",", "%2C")


def main(paths):
    emitted = 0
    for p in paths:
        path = Path(p)
        if not path.exists():
            continue
        lines = path.read_text(errors="replace").splitlines()
        i = 0
        while i < len(lines) and emitted < MAX_ERRORS:
            m = ERR.match(lines[i])
            if not m:
                i += 1
                continue
            f, ln, col, first = m.groups()
            body = [first]
            j = i + 1
            while j < len(lines) and len(body) < MAX_LINES:
                nxt = lines[j]
                if ERR.match(nxt) or nxt.startswith(("✔", "✖", "⚠", "info:", "warning:", "Build completed", "error: Lean exited", "Some required targets")):
                    break
                body.append(nxt)
                j += 1
            print(f"::error file={esc_prop(f)},line={ln},col={col},title={esc_prop(path.name)}::{esc_data(chr(10).join(body))}")
            emitted += 1
            i = j
    # Also surface generic failure lines (e.g. missing module) if no Lean error found.
    if emitted == 0:
        for p in paths:
            path = Path(p)
            if not path.exists():
                continue
            tail = [l for l in path.read_text(errors="replace").splitlines() if l.startswith("error")][:MAX_ERRORS]
            for l in tail:
                print(f"::error title={esc_prop(path.name)}::{esc_data(l)}")


if __name__ == "__main__":
    main(sys.argv[1:])
