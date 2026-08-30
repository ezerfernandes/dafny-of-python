#!/usr/bin/env python3
"""Enforce the project's exact Bisect_ppx point-coverage result.

The reporter's human-readable output has changed formatting between releases.
This gate accepts the stable covered/total pair when present and rejects any
summary that cannot prove both numbers, so a missing file cannot pass silently.
"""

from __future__ import annotations

import re
import sys


PAIR = re.compile(r"(?<!\d)(\d+)\s*/\s*(\d+)(?!\d)")
REQUIRED_PERCENT = 100.0


def project_pair(summary: str) -> tuple[int, int] | None:
    """Return the reporter's aggregate pair, never per-file pairs.

    ``summary --per-file`` contains one pair per source file followed by a
    separate ``Project coverage`` line. Summing every pair counts that
    aggregate a second time and can make an accurate report fail the gate.
    """

    matches = []
    for line in summary.splitlines():
        if "Project coverage" in line:
            matches.extend(PAIR.findall(line))
    if len(matches) != 1:
        return None
    covered, total = matches[0]
    return int(covered), int(total)


def main() -> int:
    summary = sys.stdin.read()
    pair = project_pair(summary)
    if pair is None:
        print("coverage gate: no covered/total instrumentation counts found", file=sys.stderr)
        return 2

    covered, total = pair
    if total <= 0:
        print("coverage gate: project contains no instrumentation points", file=sys.stderr)
        return 2
    percentage = 100.0 * covered / total
    if covered != total:
        print(
            f"coverage gate: {covered}/{total} instrumentation points covered ({percentage:.2f}%); "
            f"must be exactly {REQUIRED_PERCENT:.0f}%",
            file=sys.stderr,
        )
        return 1

    print(f"coverage gate: {covered}/{total} instrumentation points covered")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
