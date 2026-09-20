#!/usr/bin/env python3
"""Check aggregate-import coverage; optionally kernel-check all modules together."""
import argparse
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AGGREGATE = ROOT / "theories/Regression/Infrastructure/AllImports.v"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--kernel", action="store_true",
                    help="after dune build, run one coqchk process over every module")
args = parser.parse_args()


def logical(path):
    return "PTree." + path.relative_to(ROOT / "theories").with_suffix("").as_posix().replace("/", ".")


expected = sorted(logical(p) for p in (ROOT / "theories").rglob("*.v") if p != AGGREGATE)
actual = re.findall(r"^Require (PTree\.[\w.]+)\.$", AGGREGATE.read_text(), re.MULTILINE)
if actual != expected:
    raise SystemExit("AllImports.v inventory is stale. Missing: " + str(sorted(set(expected) - set(actual)))
                     + "; extra: " + str(sorted(set(actual) - set(expected)))
                     + ". Keep every module exactly once in sorted order.")
print(f"Aggregate regression covers all {len(expected)} other Coq modules.", flush=True)
if args.kernel:
    command = ["opam", "exec", "--", "coqchk", "-silent", "-R", "_build/default/theories", "PTree"]
    for module in [*expected, logical(AGGREGATE)]:
        command.extend(["-norec", module])
    result = subprocess.run(command, cwd=ROOT)
    if result.returncode:
        raise SystemExit(f"Single-process kernel check failed (exit {result.returncode}).")
    print(f"Single-process kernel check passed for all {len(expected) + 1} modules "
          "(default conversion, VM disabled).")
