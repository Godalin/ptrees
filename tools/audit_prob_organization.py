#!/usr/bin/env python3
"""Exact Prob organization conservation against Gate C (05a2431).

Read-only: --patch renders a mechanical migration patch, never writes files.
Unlike a proof-token comparison, this checks comments and whitespace too.
The only assembly changes are Require lists, qualified namespace references,
the sorted aggregate, and explicitly listed extraction preambles. Every line
of each split source belongs to exactly one payload or its shared preamble.
"""
import argparse
import difflib
import json
import re
from functools import lru_cache
from pathlib import Path

from audit_migration import REQUIRE, frozen, current_sources, logical, without_comments

ROOT = Path(__file__).resolve().parents[1]
PLAN = json.loads((ROOT / "docs/prob-organization.json").read_text())
BASE = PLAN["baseline"]
MOVES = PLAN["moves"]
SPLITS = PLAN["splits"]
SYMBOLS = PLAN["symbols"]
MODULES = {logical(a): logical(b) for a, b in MOVES.items()}
AGGREGATE = "theories/Regression/Infrastructure/AllImports.v"
TOKEN = re.compile(r"(?<![\w.])[A-Za-z_]\w*(?:\.\w+)+")


def expansion(module):
    path = "theories/" + module.removeprefix("PTree.").replace(".", "/") + ".v"
    if path in SPLITS:
        return [module.rsplit(".", 1)[0] + "." + n for n in SPLITS[path]["parts"]]
    return [MODULES.get(module, module)]


def relocate_token(token):
    if token in SYMBOLS:
        return SYMBOLS[token]
    for old, new in MODULES.items():
        if token == old or token.startswith(old + "."):
            return new + token[len(old):]
    # A qualified reference to a split declaration needs its individual owner.
    for old, new in SYMBOLS.items():
        if old.rsplit(".", 2)[-2] + "." + old.rsplit(".", 1)[-1] == token:
            if ".TwoLevelMeasure." in old or ".FreeOmegaMeasure." in old:
                return new
    for old, new in MODULES.items():
        stem = old.rsplit(".", 1)[-1]
        # These two files contain same-named inner modules. Their short inner
        # module references stay valid, so do not confuse them with file names.
        if stem in {"Coupling", "EnumMap", "IndexedCoupling"}:
            continue
        if token.startswith(stem + "."):
            return new + token[len(stem):]
    return token


def rewrite(source):
    def references(text):
        # A qualified-looking string literal is program data, not a name.
        return "".join(part if i % 2 else TOKEN.sub(lambda x: relocate_token(x[0]), part)
                       for i, part in enumerate(re.split(r'("(?:[^"]|"")*")', text)))
    def req(m):
        prefix, kind, words = m.groups()
        modules = [(prefix + "." if prefix else "") + word for word in words.split()]
        mapped = [n for mod in modules for n in expansion(mod)]
        if mapped == modules:
            return m[0]
        # Fully qualified Require names avoid ambiguity between e.g. the
        # generic Measure and the three concrete backend Measure modules.
        return "Require " + ((kind + " ") if kind else "") + " ".join(mapped) + "."
    # Hide Require commands while qualifying references in the rest of source.
    pieces, last = [], 0
    for m in REQUIRE.finditer(source):
        pieces += [references(source[last:m.start()]), req(m)]
        last = m.end()
    pieces.append(references(source[last:]))
    result = "".join(pieces)
    # Some clients open a transitively loaded file by its former short name.
    # The same-named inner EnumMap/Coupling modules remain unchanged. Opening
    # the relocated outer module retains its original Export behavior.
    for short, target in [("EnumMap", "PTree.Prob.Backend.Enum.Map"),
                          ("Coupling", "PTree.Prob.Backend.Enum.Coupling")]:
        if "Module " + short + "." in source:
            continue  # do not rewrite the file's own Export of its inner module
        result = re.sub(r"^(Import|Export) ([\w. ]+)\.$",
                        lambda m: m[1] + " " + " ".join(target if n == short else n for n in m[2].split()) + ".",
                        result, flags=re.M)
    return result


ROLES = {
    "Interface/Measure": "Generic semantic operations, core relational laws and Kleisli laws.",
    "Interface/Subprobability": "Individual validity, closure laws and intrinsic carrier validity; distinct capabilities.",
    "Interface/AE": "Almost-everywhere capabilities; no omega or mixed-measure assumption.",
    "Interface/Coupling": "Mass comparison and support transport/restriction for couplings.",
    "Interface/Omega": "Order, totality and countable-limit capabilities on one semantic carrier.",
    "Interface/Mixed": "Native-to-behavior bridge and its optional unit, bind, exchange and omega laws.",
    "FreeOmega/Definition": "Universe-separated completion syntax, bind, structural AE and lifting; no concrete backend.",
    "FreeOmega/Approximation": "Finite subbehavior order and cofinal chains for the free completion.",
    "FreeOmega/Observation": "Low-universe observation and quotient-closed denotation; not chosen representatives.",
    "FreeOmega/StructuralMeasure": "Auxiliary structural measure instances and laws; not the observable canonical quotient.",
    "FreeOmega/SupportLift": "High-universe support transport required by observable coupling.",
    "FreeOmega/Quotient": "Observation-closed coupling and its support soundness.",
    "FreeOmega/Measure": "Canonical observable measure, mixed and omega instances and laws.",
}


def expected_sources(before):
    expected = {}
    for old, source in before.items():
        if old not in SPLITS:
            expected[MOVES.get(old, old)] = rewrite(source)
            continue
        spec = SPLITS[old]
        lines = source.splitlines(keepends=True)
        ranges = [spec["preamble"]] + [r for rs in spec["parts"].values() for r in rs]
        assert sorted(i for a, b in ranges for i in range(a, b + 1)) == list(range(1, len(lines) + 1)), "Lost/duplicated source lines: " + old
        a, b = spec["preamble"]
        preamble = "".join(lines[a-1:b])
        # Original options/imports repeat verbatim, except the role comment.
        preamble = preamble[preamble.index("\n")+1:]
        for part, spans in spec["parts"].items():
            new = str(Path(old).with_name(part + ".v"))
            role = ROLES[new.removeprefix("theories/Prob/").removesuffix(".v")]
            imports = spec["imports"][part]
            extra = ("Require Import " + " ".join(logical(str(Path(old).with_name(n + '.v'))) for n in imports) + ".\n\n") if imports else ""
            body = "".join("".join(lines[x-1:y]) for x, y in spans)
            header = preamble
            if "capabilities" in spec:
                header = header.replace("From PTree.Prob.Interface Require Import TwoLevelMeasure.",
                    "From PTree.Prob.Interface Require Import " + " ".join(spec["capabilities"][part]) + ".")
            expected[new] = "(** Role: " + role + " *)\n" + rewrite(header) + extra + rewrite(body)
    header = before[AGGREGATE].split("Require PTree.", 1)[0]
    expected[AGGREGATE] = header + "".join("Require " + logical(p) + ".\n" for p in sorted(expected) if p != AGGREGATE)
    return expected


def audit(before=None, after=None):
    before = frozen(BASE) if before is None else before
    after = current_sources() if after is None else after
    expected = expected_sources(before)
    assert expected.keys() == after.keys(), "Added/missing module: " + str(expected.keys() ^ after.keys())
    for path, text in expected.items():
        if text != after[path]:
            diff = "".join(difflib.unified_diff(text.splitlines(True), after[path].splitlines(True), n=2))
            raise AssertionError("Non-relocation/extraction change: " + path + "\n" + diff[:4000])
    return len(before), len(after)


def patch(before, after):
    result = ["*** Begin Patch"]
    for path in sorted(before.keys() | after.keys()):
        if path not in after:
            result.append("*** Delete File: " + path)
        elif path not in before:
            result.append("*** Add File: " + path)
            result.extend("+" + line for line in after[path].splitlines())
        elif before[path] != after[path]:
            result.append("*** Update File: " + path)
            diff = list(difflib.unified_diff(before[path].splitlines(), after[path].splitlines(), lineterm=""))[2:]
            result.extend("@@" if line.startswith("@@") else line for line in diff)
    return "\n".join(result + ["*** End Patch"])


@lru_cache(maxsize=1)
def compiled_aliases():
    symbols = dict(SYMBOLS)
    # Unsplit files retain every declaration in their relocated module.
    # Include these names to disambiguate short printed Measure.* instances.
    for path, source in frozen(BASE).items():
        if path not in MOVES:
            continue
        old, new = logical(path), logical(MOVES[path])
        clean = without_comments(source)
        declarations = re.finditer(
            r"^Module(?: Export| Import)? (\w+)\.|^End (\w+)\.|"
            r"\b(?:Definition|Instance|Class|Record|Inductive|Variant|Lemma|Theorem|Corollary|Fixpoint|CoFixpoint)\s+(\w+)",
            clean, re.M)
        modules = []
        for d in declarations:
            opened, closed, name = d.groups()
            if opened:
                modules.append(opened)
            elif closed:
                if modules and modules[-1] == closed:
                    modules.pop()
            else:
                suffix = "." + ".".join(modules + [name])
                symbols[old + suffix] = new + suffix
                if d[0].startswith(("Record ", "Class ")):
                    record = re.match(r"[\s\S]*?:=\s*\{([\s\S]*?)\}\.", clean[d.end():])
                    if record:
                        for field in re.findall(r"(?:^|;)\s*(\w+)\s*(?::|\{|\()", record[1]):
                            field_suffix = "." + ".".join(modules + [field])
                            symbols[old + field_suffix] = new + field_suffix
    aliases = {}
    for old, new in symbols.items():
        for token in (old, new):
            for n in range(2, len(token.split(".")) + 1):
                suffix = ".".join(token.split(".")[-n:])
                aliases.setdefault(suffix, set()).add(old)
    return {k: next(iter(v)) for k, v in aliases.items() if len(v) == 1}


def normalize_compiled(text):
    """Only undo named relocations plus pretty-printer whitespace wrapping.

    Do not drop parameters, universes, classes, contracts, or axiom types.
    Map longest printed suffixes first; ambiguous suffixes are never guessed.
    """
    reverse = compiled_aliases()
    parts = re.split(r'("(?:[^"]|"")*")', text)
    return "".join(part if i % 2 else re.sub(r"\s+", " ",
        TOKEN.sub(lambda m: reverse.get(m[0], m[0]), part))
        for i, part in enumerate(parts)).strip()


def compare_snapshots(before, after):
    def normalized(snapshot):
        entries = snapshot["endpoints"]
        result = {normalize_compiled(e["name"]): tuple(normalize_compiled(e[k]) for k in ["type", "assumptions"])
                  for e in entries}
        assert len(result) == len(entries), "Duplicate/ambiguous capability endpoint"
        return result
    left, right = normalized(before), normalized(after)
    assert left.keys() == right.keys(), "Changed endpoint inventory: " + str(left.keys() ^ right.keys())
    for name in left:
        assert left[name] == right[name], "Changed compiled contract/assumptions: " + name + "\nBEFORE: " + str(left[name]) + "\nAFTER: " + str(right[name])
    return len(left)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--patch", action="store_true")
    parser.add_argument("--revision", help="Audit a frozen accepted target")
    args = parser.parse_args()
    if args.patch:
        print(patch(current_sources(), expected_sources(frozen(BASE))))
    else:
        old, new = audit(after=current_sources(args.revision))
        print(f"Exact Prob conservation passes: {old} original modules -> {new} modules; all payload bytes preserved modulo explicit namespace relocation.")
