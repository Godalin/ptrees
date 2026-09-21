#!/usr/bin/env python3
"""DS5a first increment: countable/dual foundations, NOT general realization."""
import argparse
import re
from pathlib import Path

import audit_capabilities as compiled
from audit_domain_soundness import ALLOWED_AXIOMS
from audit_migration import frozen, without_comments

ROOT = Path(__file__).resolve().parents[1]
BASE = "10b5563"
REPORT = ROOT / "docs/DOMAIN_DS5A_FOUNDATIONS_AUDIT.md"
COUNTABLE = "Prob/Domain/Countable"
COUPLING = "Prob/Domain/Coupling"
COVER = "Prob/Backend/SubEnum/FreeOmega/CountableSupport"
BRIDGE = "Prob/Backend/SubEnum/FreeOmega/CouplingSoundness"
REGRESSION = "Regression/Probability/FreeOmegaRelationalDomain"
NEW = {"theories/" + p + ".v" for p in (COUNTABLE, COUPLING, COVER, BRIDGE, REGRESSION)}
GROUPS = {
    "PTree." + COUNTABLE.replace("/", "."): [
        "oval_ae", "oval_ae_le", "oval_countably_supported", "oval_code_spec",
        "oval_countable_representation"],
    "PTree." + COUPLING.replace("/", "."): [
        "oval_dual", "oval_bidual", "oval_joint", "oval_coupled", "oval_joint_dual",
        "oval_bidual_mass", "oval_dual_hall", "oval_joint_off_relation_zero",
        "oval_eq_joint", "oval_eq_coupled_iff"],
    "PTree." + COVER.replace("/", "."): [
        "free_omega_enumerate_covers", "free_omega_domain_enumerated",
        "free_omega_domain_countable", "free_omega_domain_countable_representation"],
    "PTree." + BRIDGE.replace("/", "."): [
        "free_omega_qlift_domain_bidual", "free_omega_qlift_countable_constraints",
        "free_omega_qlift_domain_mass", "free_omega_qlift_domain_hall",
        "free_omega_qlift_eq_joint", "free_omega_qlift_eq_joint_agrees_ds3"],
    "PTree.Prob.Backend.SubEnum.FreeOmega.UpperQuotient": ["free_omega_qlift_upper_birel"],
    "PTree." + REGRESSION.replace("/", "."): [
        "empty_cover", "raw_invalid_cover", "heterogeneous_invalid_middle",
        "geometric_valid", "geometric_enumerates_all", "geometric_countable",
        "geometric_on_naturals", "countable_cover_is_not_validity",
        "heterogeneous_dual_through_invalid", "equality_joint_through_invalid",
        "zero_joint_empty_relation", "nonzero_joint_empty_relation_impossible",
        "unequal_mass_no_joint"],
}


def aggregate_after(text):
    for marker, modules in [
        ("Require PTree.Prob.Backend.SubEnum.FreeOmega.CodedJoint.\n", [COVER, BRIDGE]),
        ("Require PTree.Prob.Domain.Expectation.\n", [COUNTABLE, COUPLING]),
        ("Require PTree.Regression.Probability.FreeOmegaQuotientDomain.\n", [REGRESSION]),
    ]:
        assert text.count(marker) == 1, "Missing/duplicate frozen aggregate marker"
        addition = "".join("Require PTree." + p.replace("/", ".") + ".\n" for p in modules)
        text = text.replace(marker, addition + marker if modules[0] == COUNTABLE else marker + addition)
    return text


def audit_sources(before, after):
    assert set(after) == set(before) | NEW, "Unexpected new/deleted theory module"
    for path, text in before.items():
        if path == "theories/Regression/Infrastructure/AllImports.v":
            text = aggregate_after(text)
        assert after[path] == text, "Frozen source changed: " + path
    for path in NEW:
        code = without_comments(after[path])
        assert not re.search(r"\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Class)\b", code), path
    for module in [COUNTABLE, COUPLING]:
        code = without_comments(after["theories/" + module + ".v"])
        assert not re.search(r"\b(?:FreeOmega|free_omega_\w+|Semantic\w+|ptree|Inductive|CoInductive)\b", code), "External mathematical domain is not independent"
    bridge = without_comments(after["theories/" + BRIDGE + ".v"])
    assert not re.search(r"\b(?:induction|elim|Fixpoint|Inductive|CoInductive)\b", bridge), "Use the all-raw bridge, not intermediate validity"
    assert "free_omega_qlift_upper_birel" in bridge
    assert "free_omega_qlift_eq_sound" in bridge
    assert "Theorem free_omega_qlift_sound " not in bridge, "General realization is outside this increment"
    return len(before), len(after)


def check_answer(name, typ, assumptions):
    axioms = {n for n in re.findall(r"^([\w.]+)\s*:", assumptions, re.M) if n != "Axioms"}
    if "Axioms:" in assumptions:
        assert axioms, "Unparsed assumptions: " + name
    assert axioms <= ALLOWED_AXIOMS, (name, axioms - ALLOWED_AXIOMS)
    assert not re.search(r":\s*@?(?:\w+\.)*Semantic\w+\b", typ), "New capability premise"
    if ".Prob.Domain." in name:
        assert not re.search(r"\b(?:FreeOmega|free_omega_\w+|Semantic\w+|ptree)\b", typ), "Domain depends on formal representation"
    if ".CouplingSoundness." in name:
        assert "free_omega_admissible" in typ, "Missing endpoint validity boundary"
        if name.endswith("_domain_bidual"):
            assert "oval_bidual" in typ and "oval_coupled" not in typ, "Do not confuse constraints with realization"


def report():
    previous = compiled.GROUPS, compiled.ENDPOINTS
    try:
        compiled.GROUPS = GROUPS
        compiled.ENDPOINTS = [m + "." + n for m, ns in GROUPS.items() for n in ns]
        answers = compiled.query()
    finally:
        compiled.GROUPS, compiled.ENDPOINTS = previous
    lines = ["# DS5a foundations: compiled contracts", "",
             "Generated by `python3 tools/audit_domain_relational.py`; compare with `--check`.", "",
             f"Scope: {len(answers)} countable-support, dual-constraint and equality-joint endpoints.",
             "GENERAL qlift joint realization is NOT established by this increment. Countable transport existence remains open work.",
             "The domain is mathematical and independent. Backend bridges require admissible endpoints, not admissible derivation intermediates.",
             "No new semantic class or axiom; the DS2-DS4 logical whitelist is unchanged. Earlier compiled snapshots are not regenerated.", ""]
    for name, typ, assumptions in answers:
        check_answer(name, typ, assumptions)
        lines += ["## `" + name + "`", "", "```coq", typ, "```", "",
                  "```text", assumptions, "```", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--source", action="store_true")
    args = parser.parse_args()
    if args.check or args.source:
        after = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT / "theories").rglob("*.v")}
        counts = audit_sources(frozen(BASE), after)
        print(f"DS5a source isolation: {counts[0]} frozen modules unchanged except exact aggregate insertions; {counts[1]} modules now.")
    if not args.source:
        text = report()
        if args.check:
            assert REPORT.read_text() == text, "DS5a foundations compiled report changed"
            print("DS5a foundations compiled signatures/assumptions match; not a general realization claim.")
        else:
            print(text, end="")
