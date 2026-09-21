#!/usr/bin/env python3
"""Gate C source conservation: named context/import edits, no proof changes.

The historical Gate B audit still runs against --revision 2af47aa. This
separate check describes today's authorized source delta; it does not relax
the old migration normalization or treat a successful build as conservation.
"""
import re

from audit_migration import REQUIRE, current_sources, frozen, without_comments

BASE = "2af47aa"
IMPORT_ONLY = {
    "API/FreeOmega", "Eq/FreeOmega/Algebra", "Eq/FreeOmega/Bind",
    "Interp/FreeOmega/Translate", "Semantics",
}
UNUSED_AE = {"Eq/FreeOmega/Base", "Eq/FreeOmega/Relation", "Eq/FreeOmega/Iter",
             "Interp/FreeOmega/Cofinality", "Interp/FreeOmega/Translate"}
AE = "  `{NAE : @SemanticMeasureAELiftLaws MN NI}\n"
NI = "  `{NI : SemanticMeasure MN}\n"
NEW = {"theories/Regression/Infrastructure/CapabilityBoundaries.v"}
AGGREGATE = "theories/Regression/Infrastructure/AllImports.v"


def clean_imports(source):
    # Preserve all nonempty source lines, including proof/string whitespace.
    source = REQUIRE.sub("", without_comments(source))
    return "\n".join(line for line in source.splitlines() if line.strip())


def remove_exact(source, text, count=1):
    assert source.count(text) == count, "Context cleanup no longer matches the frozen source"
    return source.replace(text, "")


def simplify_kernel_bridge(source):
    start = source.index("Section GenericKernelAdequacy.")
    end = source.index("End GenericKernelAdequacy.", start)
    body = source[start:end]
    for line in [NI, "  `{NC : @SemanticMeasureCoreLaws MN NI}\n",
                 "  `{FB : @SemanticMeasureBindLaws MF FI}\n",
                 "  `{ML : @MixedMeasureLaws MN MF NI FI MX}\n",
                 "Context `{FOL : @SemanticOmegaLaws MF FI FO}.\n"]:
        body = remove_exact(body, line)
    for name, proof in [("ptree_primitive_hitting_adequate", "apply sem_eq_refl."),
                        ("ptree_primitive_stable_hitting_adequate", "reflexivity."),
                        ("ptree_primitive_ast_adequate", "reflexivity.")]:
        a = body.index("Proof.", body.index("Theorem " + name))
        b = body.index("Qed.", a) + len("Qed.")
        body = body[:a] + "Proof. " + proof + " Qed." + body[b:]
    return source[:start] + body + source[end:]


def audit(before=None, after=None):
    before = frozen(BASE) if before is None else before
    after = current_sources() if after is None else after
    assert set(after) == set(before) | NEW, "Unexpected theory addition/deletion/move"
    for path in NEW:
        assert not re.search(r"\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit)\b",
                             without_comments(after[path])), "Unproved declaration in regression: " + path
    changed = []
    for path, source in before.items():
        module = path.removeprefix("theories/").removesuffix(".v")
        current = after[path]
        expected = source
        if module in UNUSED_AE:
            expected = remove_exact(source, AE)
        elif module in {"Interp/Kernel", "Eq/ProbabilisticTrace"}:
            expected = remove_exact(source, NI, count=2)
        elif module == "Interp/FreeOmega/Base":
            # Only the explicit, unused binder on this one declaration.
            start = source.index("Theorem peutt_interp_structural")
            end = source.index("Qed.", start)
            body = remove_exact(source[start:end], "  " + AE)
            expected = source[:start] + body + source[end:]
            # Identity/composition of event renamings no longer inherit AE
            # from the formerly overstrong definitional kernel bridge.
            for section in ["FreeOmegaTranslateIdentity", "FreeOmegaTranslateComposition"]:
                a = expected.index("Section " + section + ".")
                b = expected.index("End " + section + ".", a)
                body = remove_exact(expected[a:b], AE)
                expected = expected[:a] + body + expected[b:]
        elif module == "Eq/PTreeKernel":
            expected = simplify_kernel_bridge(source)
        elif module == "API/Weighted":
            contexts = "Context `{Monad M}.\nContext `{MonadMeasure M}.\n"
            expected = remove_exact(source, contexts)
            expected = expected.replace("Definition stuckM", contexts + "Definition stuckM")
        elif path == AGGREGATE:
            expected = source.replace(
                "Require PTree.Regression.Infrastructure.ArchitectureBoundaries.\n",
                "Require PTree.Regression.Infrastructure.ArchitectureBoundaries.\n"
                "Require PTree.Regression.Infrastructure.CapabilityBoundaries.\n")
            assert current == expected, "Unexpected aggregate change"
            continue
        elif module not in IMPORT_ONLY:
            assert current == source, "Unreviewed source change: " + path
            continue
        assert clean_imports(current) == clean_imports(expected), "Non-hygiene/proof change: " + path
        if current != source:
            changed.append(path)
    return changed


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", help="Check an accepted historical target, e.g. 05a2431")
    args = parser.parse_args()
    changed = audit(after=frozen(args.revision)) if args.revision else audit()
    print(f"Gate C conservation passes: {len(changed)} reviewed hygiene/signature files; "
          "one regression plus its aggregate import; only three enumerated definitional bridge proofs simplified.")
    for path in changed:
        print(path)
