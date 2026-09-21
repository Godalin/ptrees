#!/usr/bin/env python3
"""Gate C: frozen public scope, full compiled types, and logical dependencies.

This is not a mathematical minimality test. A baseline/delta records complete
types, including local contracts, rather than merely counting class names.
Run after dune build. No command in this tool writes a file.
"""
import argparse
import json
import re
from pathlib import Path

import audit_capabilities as compiled
from audit_migration import frozen, without_comments

ROOT = Path(__file__).resolve().parents[1]
BASE = "2af47aa"
BASELINE = ROOT / "docs/CAPABILITY_GATE_C_BEFORE.json"
CURRENT = ROOT / "docs/CAPABILITY_GATE_C_AFTER.json"
INDEX = ROOT / "docs/CAPABILITY_PUBLIC_INDEX.md"
FACADES = ["API/Generic", "API/FreeOmega", "API/Enum", "API/SubEnum", "API/Weighted", "Semantics"]
EXPERT = [
    "Eq/PEutt", "Eq/PStruct", "Eq/PStrong", "Eq/ProbabilisticTrace",
    "Eq/FreeOmega/Algebra", "Eq/FreeOmega/Iter", "Eq/FreeOmega/Bind", "Eq/FreeOmega/Relation",
    "Interp/Structural", "Interp/FreeOmega/Base", "Interp/FreeOmega/Translate",
    "Interp/FreeOmega/Guarded", "Interp/FreeOmega/Atomic", "Interp/FreeOmega/MDP",
    "Interp/Backend/SubEnum", "Semantics/HeadTransition", "Semantics/TreeTransition",
    "Semantics/TreeTransitionBisim", "Semantics/TreeTransitionSoundness",
    "Semantics/MDPFragment", "Semantics/MDPCoincidence", "Semantics/MDPEmbedding",
    "Semantics/FreeOmega/MDPCoincidenceFreeOmega", "Semantics/Backend/MDPEmbeddingSubEnum",
    "Eq/Backend/ProbabilisticTraceEnum", "Eq/Backend/ProbabilisticTraceSubEnum",
]
# Also inspect the key helper chain, even where it is deliberately not facade API.
HELPERS = {
    "Eq/PTreeKernel": ["ptree_stable_hitting_ret", "ptree_stable_hitting_vis", "ptree_stable_hitting_bind",
                       "ptree_primitive_hitting_adequate", "ptree_primitive_stable_hitting_adequate", "ptree_primitive_ast_adequate"],
    "Eq/FreeOmega/Base": ["ptree_hitting_mono", "ptree_observable_hitting_increasing"],
    "Eq/PEutt": ["stable_hitting_front_choice"],
    "Interp/FreeOmega/Cofinality": ["ptree_interp_cofinal_all"],
    "Interp/FreeOmega/Atomic": ["atomic_interp_head_hitting", "atomic_finish_bind"],
    "Interp/FreeOmega/Guarded": ["guarded_handler_of_hitting"],
    "Eq/Backend/ProbabilisticTraceEnum": ["enum_finite_interaction_probability", "enum_finite_interaction_probability_intro"],
    "Eq/Backend/ProbabilisticTraceSubEnum": ["subenum_finite_interaction_probability", "subenum_finite_interaction_probability_intro"],
}


def scope(sources):
    """Explicit expert selection plus every identifier exposed by our facades.

    Parameterized syntax notation is checked at its defining constructor.
    Symbolic ≈ₚ notation is covered by its peutt alias and parser regressions.
    """
    result = set(compiled.ENDPOINTS)
    for module in FACADES:
        src = without_comments(sources["theories/" + module + ".v"])
        names = re.findall(r"^Notation\s+(\w+)\s*:=", src, re.M)
        names += re.findall(r"^(?:Definition|Variant|Inductive)\s+(\w+)", src, re.M)
        result.update("PTree." + module.replace("/", ".") + "." + n for n in names)
    for n in ["go", "RetF", "TauF", "VisF", "ProbF"]:
        result.add("PTree.Core.PTreeDefinition." + n)
    for module in EXPERT:
        src = without_comments(sources["theories/" + module + ".v"])
        names = re.findall(r"^(?:Theorem|Corollary|Global Instance|#\[global\] Instance)\s+(\w+)", src, re.M)
        result.update("PTree." + module.replace("/", ".") + "." + n for n in names)
    for module, names in HELPERS.items():
        result.update("PTree." + module.replace("/", ".") + "." + n for n in names)
    return sorted(result)


def current_scope():
    sources = {p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT / "theories").rglob("*.v")}
    expected = scope(frozen(BASE))
    assert scope(sources) == expected, "Public scope changed: review the frozen Gate C endpoint inventory"
    return expected


def query():
    endpoints = current_scope()
    groups = {}
    for endpoint in endpoints:
        module, name = endpoint.rsplit(".", 1)
        groups.setdefault(module, []).append(name)
    previous = compiled.GROUPS, compiled.ENDPOINTS
    try:
        compiled.GROUPS, compiled.ENDPOINTS = groups, endpoints
        return {"source_baseline": BASE, "scope": "curated facades + listed expert endpoints + helper probes",
                "endpoints": [{"name": name, "type": typ, "assumptions": axioms}
                              for name, typ, axioms in compiled.query()]}
    finally:
        compiled.GROUPS, compiled.ENDPOINTS = previous


def changes(before, after):
    left = {e["name"]: e for e in before["endpoints"]}
    right = {e["name"]: e for e in after["endpoints"]}
    assert len(left) == len(before["endpoints"]) and len(right) == len(after["endpoints"]), "Duplicate endpoint"
    assert left.keys() == right.keys(), "Missing/extra endpoint in capability comparison"
    return [n for n in sorted(left) if left[n] != right[n]]


WEAKENED = {"PTree.Interp.FreeOmega.Base.peutt_interp_structural",
            "PTree.Interp.FreeOmega.Base.peutt_translate_structural",
            "PTree.Interp.FreeOmega.Base.peutt_translate_Proper",
            "PTree.Interp.FreeOmega.Base.peutt_translate_id",
            "PTree.Interp.FreeOmega.Base.peutt_translate_compose",
            "PTree.Interp.FreeOmega.Base.peutt_interp_trigger",
            "PTree.Interp.FreeOmega.Translate.peutt_translate",
            "PTree.Eq.PTreeKernel.ptree_primitive_hitting_adequate",
            "PTree.Eq.PTreeKernel.ptree_primitive_stable_hitting_adequate",
            "PTree.Eq.PTreeKernel.ptree_primitive_ast_adequate"}
FUNEXT_REMOVED = {"PTree.Interp.FreeOmega.Translate.peutt_translate",
                  "PTree.Interp.FreeOmega.Base.peutt_translate_Proper",
                  "PTree.Interp.FreeOmega.Base.peutt_translate_id",
                  "PTree.Interp.FreeOmega.Base.peutt_translate_compose",
                  "PTree.Interp.FreeOmega.Base.peutt_interp_trigger"}


def check_delta(before, after):
    delta = changes(before, after)
    assert set(delta) == WEAKENED, "Unreviewed signature/assumption changes: " + str(delta)
    left = {e["name"]: e for e in before["endpoints"]}
    for e in after["endpoints"]:
        expected = left[e["name"]]["assumptions"]
        if e["name"] in FUNEXT_REMOVED:
            expected, count = re.subn(
                r"^FunctionalExtensionality\.functional_extensionality_dep :\n(?:  .*\n)+",
                "", expected, flags=re.M)
            assert count == 1, "Missing baseline funext dependency"
        assert e["assumptions"] == expected, "Unreviewed logical dependency change: " + e["name"]
        if e["name"] in WEAKENED and ".PTreeKernel." not in e["name"]:
            assert "SemanticMeasureAELiftLaws" in left[e["name"]]["type"]
            assert "SemanticMeasureAELiftLaws" not in e["type"]
    return delta


def index(snapshot):
    rows = ["# Gate C public capability index", "",
            "Generated by `python3 tools/audit_public_capabilities.py --index`. "
            "The exact scope is frozen against `2af47aa`; facade aliases count as entries "
            "even when they name the same underlying constant. Parameterized constructor "
            "notations are audited via `go` and the four node constructors.", "",
            "This table is a navigation aid, not a minimality claim. Full carrier assignments, "
            "structural parameters, local contracts and logical axiom types are retained in "
            "[before](CAPABILITY_GATE_C_BEFORE.json) and [after](CAPABILITY_GATE_C_AFTER.json). "
            "The [review](CAPABILITY_REVIEW.md) explains proof-helper dependencies and retained premises.", "",
            f"**{len(snapshot['endpoints'])} entries**. Concrete endpoints with no class parameters "
            "instantiate their backend; they are not measure-independent.", "",
            "| Endpoint (source module) | Operation/law classes in full type | Logical axiom names |",
            "| --- | --- | --- |"]
    for e in snapshot["endpoints"]:
        module, _ = e["name"].rsplit(".", 1)
        path = "../theories/" + module.removeprefix("PTree.").replace(".", "/") + ".v"
        classes = sorted(set(re.findall(
            r"\b(?:Semantic\w+|MixedMeasure\w*|[A-Z]\w*Laws|MathCompCouplingGluing)\b", e["type"])))
        axioms = [n for n in re.findall(r"^([\w.]+)\s*:", e["assumptions"], re.M) if n != "Axioms"]
        if "Axioms:" in e["assumptions"] and not axioms:
            raise AssertionError("Unparsed assumptions: " + e["name"])
        fmt = lambda xs: ", ".join("`" + x + "`" for x in xs) or "none"
        rows.append(f"| [{e['name']}]({path}) | {fmt(classes)} | {fmt(axioms)} |")
    return "\n".join(rows) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--scope", action="store_true")
    parser.add_argument("--index", action="store_true", help="Render the checked-in after snapshot as an index")
    args = parser.parse_args()
    if args.scope:
        print("\n".join(current_scope()))
    elif args.index:
        print(index(json.loads(CURRENT.read_text())), end="")
    else:
        result = query()
        if args.check:
            assert result == json.loads(CURRENT.read_text()), "Current public capability snapshot is stale"
            assert index(result) == INDEX.read_text(), "Public capability index is stale"
            delta = check_delta(json.loads(BASELINE.read_text()), result)
            print(f"Checked {len(result['endpoints'])} public/helper endpoints; {len(delta)} full-signature/assumption deltas.")
            for endpoint in delta:
                print(endpoint)
        else:
            print(json.dumps(result, ensure_ascii=False, indent=2))
