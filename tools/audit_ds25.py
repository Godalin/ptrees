#!/usr/bin/env python3
"""DS2.5 exact source relocation and compiled Upper/native contract conservation.

Read-only: --patch prints the mechanical extraction; --capture-before prints
the compiled baseline (only at the frozen revision). No proof normalization.
"""
import argparse
import difflib
from functools import lru_cache
import json
import re
import subprocess
from pathlib import Path

from audit_migration import frozen

ROOT = Path(__file__).resolve().parents[1]
BASE = "bc8f9d2"
DIR = "theories/Prob/Backend/SubEnum/"
NEW = DIR + "Expectation.v"
UPPER = [DIR + "FreeOmega/Upper" + n + ".v"
         for n in ("Expectation", "Coupling", "Continuity")]
SNAPSHOT = ROOT / "docs/DOMAIN_DS25_BEFORE.json"
EXPORT = "Require Export PTree.Prob.Backend.SubEnum.Expectation.\n"
PREAMBLE = '''(** Role: Finite weighted expectation and native coupling/continuity facts.
    Shared by the native SubEnum domain adapter and raw FreeOmega evaluators.
    No FreeOmega syntax or external domain is used here. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals.
From mathcomp.classical Require Import classical_sets.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.Enum Require Import
  Representation Map Bind Coupling SemanticCoupling Measure FrontierLift Iteration.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Interface Require Import Measure Subprobability AE Coupling Omega Mixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum PTree.Prob.Backend.Enum.Map PTree.Prob.Backend.Enum.Coupling
  RatSubTypes GRing.Theory Num.Theory Order.Theory.
Import EnumCouplingClassical.
Local Open Scope ring_scope.

'''


def logical(path):
    return "PTree." + path.removeprefix("theories/").removesuffix(".v").replace("/", ".")


def declarations(source):
    return re.findall(r"^(?:Fixpoint|Definition|Lemma|Theorem|Corollary) (\w+)", source, re.M)


def expected_sources(before):
    after = dict(before)
    moved = []

    def take(path, start, end):
        src = after[path]
        assert src.count(start) == 1 and src.count(end) == 1, (path, start, end)
        a, b = src.index(start), src.index(end)
        assert a < b
        payload = src[a:b]
        after[path] = src[:a] + src[b:]
        moved.extend((logical(path) + "." + n, logical(NEW) + "." + n)
                     for n in declarations(payload))
        return payload

    expectation, coupling, continuity = UPPER
    prefix = take(expectation, "Fixpoint enum_real_expect", "Fixpoint free_omega_upper")
    zero = take(expectation, "Lemma enum_real_expect_zero", "Lemma free_omega_upper_zero")
    one = take(expectation, "Lemma enum_real_expect_one", "End UpperExpectation.")
    native = take(coupling, "(** Weighted numeric soundness", "(** Raw finite-subbehavior")
    scalar = take(continuity, "Lemma scalar_increasing_le", "Lemma countable_upper_swap")
    countable = take(continuity, "Lemma enum_real_expect_countable_ae", "(** Scott continuity")
    after[NEW] = (PREAMBLE + "Section FiniteExpectation.\nVariable R : realType.\n\n"
                  + prefix + zero + one + "End FiniteExpectation.\n\n" + native
                  + "Section FiniteSuprema.\nVariable R : realType.\n"
                  + "Local Notation upper := (@countable_upper R).\n\n" + scalar
                  + "End FiniteSuprema.\n\nSection FiniteContinuity.\nVariable R : realType.\n"
                  + "Local Notation expect := (enum_real_expect (R := R)).\n\n" + countable
                  + "End FiniteContinuity.\n")
    for path in UPPER:
        marker = "Set Implicit Arguments."
        assert after[path].count(marker) == 1
        after[path] = after[path].replace(marker, EXPORT + "\n" + marker)
    # Recreate the pre-extraction Section-local application spine. The raw
    # proofs used @countable_upper_ge before R was generalized by End.
    marker = "Section UpperExpectation.\nVariable R : realType.\n"
    assert after[expectation].count(marker) == 1
    after[expectation] = after[expectation].replace(marker, marker +
        "Local Notation countable_upper_ge := (@Expectation.countable_upper_ge R).\n")
    native_path = DIR + "Domain.v"
    old = ("From PTree.Prob.Backend.SubEnum.FreeOmega Require Import\n"
           "  UpperExpectation UpperCoupling UpperContinuity.")
    assert after[native_path].count(old) == 1
    after[native_path] = after[native_path].replace(old,
        "From PTree.Prob.Backend.SubEnum Require Import Expectation.")
    aggregate = "theories/Regression/Infrastructure/AllImports.v"
    marker = "Require PTree.Prob.Backend.SubEnum.Domain.\n"
    assert after[aggregate].count(marker) == 1
    after[aggregate] = after[aggregate].replace(marker, marker + "Require " + logical(NEW) + ".\n")
    assert len(moved) == len(set(moved))
    return after, dict(moved)


def audit_sources(before, actual):
    expected, _ = expected_sources(before)
    assert expected.keys() == actual.keys(), "Unexpected/missing .v module"
    for path, content in expected.items():
        assert actual[path] == content, "Non-relocation source edit: " + path
    return len(before), len(actual)


@lru_cache(maxsize=1)
def relocation():
    return expected_sources(frozen(BASE))[1]


def normalize(text):
    """Only exact qualified moved identifiers and Coq printer whitespace.

    Unqualified names are unchanged. Strings are never normalized.
    Also accepts Coq's shortest printed module-qualified form.
    """
    moves = dict(relocation())
    for old, new in list(moves.items()):
        moves[".".join(old.split(".")[-2:])] = new
        moves[".".join(new.split(".")[-2:])] = new
    tokens = re.findall(r'"(?:""|[^"\\]|\\.)*"|[A-Za-z_][\w\'.]*|\s+|.', text)
    return "".join(" " if t.isspace() else moves.get(t, t) for t in tokens).strip()


def query(before, relocated):
    import audit_capabilities as compiled
    moves = relocation() if relocated else {}
    names = [logical(p) + "." + n for p in UPPER + [DIR + "Domain.v"]
             for n in declarations(before[p])]
    endpoints = [moves.get(n, n) for n in names]
    groups = {}
    for n in endpoints:
        module, name = n.rsplit(".", 1)
        groups.setdefault(module, []).append(name)
    previous = compiled.GROUPS, compiled.ENDPOINTS
    try:
        compiled.GROUPS, compiled.ENDPOINTS = groups, endpoints
        return {"baseline": BASE, "endpoints": [dict(name=n, type=t, assumptions=a)
                 for n, t, a in compiled.query()]}
    finally:
        compiled.GROUPS, compiled.ENDPOINTS = previous


def compare(before, after):
    def rows(snapshot):
        entries = snapshot["endpoints"]
        result = {normalize(e["name"]): {k: normalize(v) for k, v in e.items()}
                  for e in entries}
        assert len(result) == len(entries), "Duplicate endpoint"
        return result
    left, right = rows(before), rows(after)
    assert left.keys() == right.keys(), "Changed endpoint scope"
    changes = [n for n in left if left[n] != right[n]]
    assert not changes, "Changed types/assumptions: " + str(changes)


def patch(expected):
    print("*** Begin Patch")
    for path, content in expected.items():
        file = ROOT / path
        old = file.read_text() if file.exists() else ""
        if old == content:
            continue
        if not file.exists():
            print("*** Add File: " + path)
            print("\n".join("+" + line for line in content.splitlines()))
        else:
            print("*** Update File: " + path)
            for line in list(difflib.unified_diff(old.splitlines(), content.splitlines(), n=3))[2:]:
                print("@@" if line.startswith("@@") else line)
    print("*** End Patch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--patch", action="store_true")
    group.add_argument("--capture-before", action="store_true")
    group.add_argument("--source", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    before = frozen(BASE)
    if args.patch:
        patch(expected_sources(before)[0])
    elif args.capture_before:
        assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().startswith(BASE)
        for path, text in before.items():
            assert (ROOT / path).read_text() == text, "Capture before editing .v files"
        print(json.dumps(query(before, False), indent=2))
    else:
        actual = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT / "theories").rglob("*.v")}
        counts = audit_sources(before, actual)
        print(f"Exact DS2.5 source relocation: {counts[0]} -> {counts[1]} modules; no proof edits.")
        if args.check:
            baseline = json.loads(SNAPSHOT.read_text())
            compare(baseline, query(before, True))
            print(f"{len(baseline['endpoints'])} Upper/native compiled contracts unchanged modulo declared relocation.")
