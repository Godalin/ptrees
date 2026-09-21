#!/usr/bin/env python3
"""Check extracted constants against the pre-split compiled snapshot.

Includes constructors, induction schemes, class projections and law instances,
not just the 306 paper-facing endpoints audited separately. Read-only.
"""
import json

import audit_capabilities as compiled
from audit_prob_organization import ROOT, SYMBOLS, compare_snapshots


def audit():
    before = json.loads((ROOT / "docs/PROB_CAPABILITY_BEFORE.json").read_text())
    endpoints = [SYMBOLS[e["name"]] for e in before["endpoints"]]
    assert set(e["name"] for e in before["endpoints"]) == SYMBOLS.keys(), "Incomplete extraction capability snapshot"
    groups = {}
    for endpoint in endpoints:
        mod, name = endpoint.rsplit(".", 1)
        groups.setdefault(mod, []).append(name)
    previous = compiled.GROUPS, compiled.ENDPOINTS
    try:
        compiled.GROUPS, compiled.ENDPOINTS = groups, endpoints
        after = {"endpoints": [dict(name=n, type=t, assumptions=a) for n, t, a in compiled.query()]}
    finally:
        compiled.GROUPS, compiled.ENDPOINTS = previous
    return compare_snapshots(before, after)


if __name__ == "__main__":
    print(f"Checked {audit()} extracted constants: compiled types and logical assumptions unchanged modulo explicit relocation.")
