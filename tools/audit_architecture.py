#!/usr/bin/env python3
"""Read-only post-migration ownership/dependency audit. Run dune build first."""
import argparse
import re
from pathlib import Path
from audit_assumptions import without_comments
from mathcomp_policy import GATE_M, check_gate_boundary
from rocq_paths import source_files, module_key, source_path, SOURCE_ROOTS

ROOT = Path(__file__).resolve().parents[1]
AGGREGATE = "Tests/AllImports"
INTERNAL_REASON = (
    "maintained execution/scheduling contract; private, not another equality"
)


def external_validation(path):
    """Independent domain and the explicitly planned one-way adapters.

    Classify adapters before they exist so a future soundness file cannot
    silently enter the mainline through an otherwise ordinary Backend edge.
    """
    return path.startswith(("Examples/Validation/", "Examples/Counterexamples/Validation/",
                            "Prob/Domain/", "Prob/FreeOmega/Validation/",
                            "Execution/Validation/")) or path in {
        "Prob/Backend/Common/DomainTransport",
        "Prob/Backend/Common/CountableCoupling",
        "Prob/Backend/Common/CountableRelationalLimit",
        "Prob/Backend/SubEnumQ/Domain", "Prob/Backend/MathComp/Domain",
        "Prob/Backend/SubEnumR/Domain",
        "Prob/Backend/SubEnumR/FreeOmega/Validation",
        "Prob/Backend/SubEnumR/FreeOmega/NativeReflection",
        "Prob/Backend/SubEnumR/FreeOmega/CountableSupport",
        "Prob/Backend/SubEnumR/FreeOmega/JointRealization",
        "Prob/Backend/SubEnumQ/FreeOmega/CountableSupport",
        "Prob/Backend/SubEnumQ/FreeOmega/JointRealization",
        "Prob/Backend/SubEnumQ/FreeOmega/Compatibility",
        "Prob/Backend/SubEnumQ/FreeOmega/Validation",
        "Eq/Backend/StableHittingDomainSubEnumQ",
        "Eq/Backend/StableHittingDomainSubEnumR",
    }


def ownership(path):
    if path in GATE_M:
        return path.rsplit('/', 1)[0], 'universe-unchecked Gate M', 'MathComp assembly/probes; excluded from safe aggregate'
    if path.startswith(("CaseStudies/", "Events/", "API/", "Regression/")):
        raise AssertionError("Unsupported top-level namespace: " + path)
    if path in {"PTree", "Eq", "PTreeFacts", "Semantics"}:
        return "EntryPoint", "aggregate", "explicit syntax/relation/facts/comparison entry point"
    if path.startswith("Experimental/"):
        raise AssertionError("Unreviewed experiment: " + path)
    if path == AGGREGATE:
        return "Tests", "integration", "root build compiles every Gate S module; not installed theory"
    if path.startswith("Tests/"):
        return path.rsplit("/", 1)[0], "technical contract", "isolated compilation client; not mathematical theory"
    if path.startswith("Examples/") and external_validation(path):
        return path.rsplit("/", 1)[0], "external model example", "one-way mathematical validation; never a reasoning dependency"
    if path.startswith("Examples/"):
        return path.rsplit("/", 1)[0], "mathematical example", "program, supporting mathematics or counterexample; no tests dependency"
    if path.startswith("Prob/FreeOmega/Validation/"):
        return "Prob/FreeOmega/Validation", "external validation", "native-parametric bridge to independent mathematical models"
    if path in {"Eq/Backend/StableHittingDomainSubEnumQ", "Eq/Backend/StableHittingDomainSubEnumR"}:
        return "Eq/Backend", "external validation", "specializes generic hitting validity/adequacy; never a reasoning premise"
    if path.startswith("Core/"):
        return "Core", "syntax", "primitive syntax/combinators only"
    if path == "Execution/Validation/SubEnumQ":
        return "Execution/Validation", "external validation", "one-way runner-to-hitting correspondence; never an executable dependency"
    if path.startswith("Execution/Validation/"):
        return "Execution/Validation", "execution validation", "conditional sampler/replay probability laws; never an executable dependency"
    if path.startswith("Execution/Backend/"):
        return "Execution/Backend", "concrete", "executable native sampling; no external validation or recursive frontier"
    if path.startswith("Execution/"):
        return "Execution", "generic", "operational runner and finite path correctness; sampler laws are separate"
    if path.startswith("Prob/Backend/"):
        parts = path.split("/")
        assert len(parts) >= 4 and parts[2] in {"Common", "EnumQ", "SubEnumQ", "SubEnumR", "MathComp"}, "Ungrouped concrete probability module: " + path
        family = parts[2]
        assert not (family == "MathComp" and "FreeOmega" in parts[3:]), \
            "Removed MathComp completion namespace: " + path
        owner = "/".join(parts[:3])
        if path in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling", "Prob/Backend/Common/CountableRelationalLimit"}:
            return owner, "external validation", "one-way adapter: independent real transport to expectation-domain joints"
        if family == "Common":
            return owner, "shared arithmetic/combinatorics", "no native carrier specialization"
        if len(parts) >= 5 and parts[3] == "FreeOmega":
            return owner + "/FreeOmega", family, "FreeOmega over a concrete native carrier, not generic FreeOmega MN"
        return owner, family, "native representation, laws or realization adapters"
    for prefix, profile, disposition in (
        ("Prob/Domain", "external validation", "independent mathematical domain; not a free completion or mainline premise"),
        ("Prob/Interface", "generic", "operation/law interfaces"),
        ("Prob/FreeOmega", "FreeOmega", "canonical measure model, not a concrete native backend"),
        ("Prob/Legacy", "weighted legacy", "explicit retained clients; not canonical probability"),
        ("Eq/Internal/Backend", "concrete", INTERNAL_REASON),
        ("Eq/Internal/FreeOmega", "FreeOmega", INTERNAL_REASON),
        ("Eq/Internal", "generic", INTERNAL_REASON),
        ("Eq/Backend", "concrete", "tree equations/quantitative endpoints for concrete carriers"),
        ("Eq/FreeOmega", "FreeOmega", "canonical-model equational theory"),
        ("Eq", "generic", "canonical equivalence, validity and hitting algebra"),
        ("Semantics/Backend", "SubEnumQ", "retain comparison semantics; not canonical equality"),
        ("Semantics/FreeOmega", "FreeOmega", "retain comparison semantics; not canonical equality"),
        ("Semantics", "generic", "independent comparison semantics"),
        ("Interp/Backend", "SubEnumQ", "concrete interpreter endpoint"),
        ("Interp/FreeOmega", "FreeOmega", "canonical-model interpreter compositionality"),
        ("Interp", "generic", "structural interpretation or generic hitting infrastructure"),
    ):
        if path.startswith(prefix + "/"):
            return prefix, profile, disposition
    raise AssertionError("Module lacks an architectural owner: " + path)


def permitted(module, dependency):
    if module.startswith(('API/', 'Regression/')) or dependency.startswith(('API/', 'Regression/')):
        return False
    if dependency in GATE_M and module not in GATE_M:
        return False
    def under(*prefixes):
        return any(dependency.startswith(p + "/") for p in prefixes)
    if external_validation(dependency) and not (
            external_validation(module) or module.startswith("Tests/")):
        return False
    if dependency.startswith('Tests/') and not module.startswith('Tests/'):
        return False
    if dependency.startswith('Examples/') and not module.startswith(('Examples/', 'Tests/')):
        return False
    if module.startswith("Prob/Domain/"):
        return under("Prob/Domain")
    if module.startswith("Prob/FreeOmega/Validation/"):
        if module == "Prob/FreeOmega/Validation/StableHitting":
            return under("Prob/Domain", "Prob/Interface", "Prob/FreeOmega") or dependency in {
                "Core/PTreeDefinition", "Eq/PrimitiveStableHitting",
                "Eq/UnifiedFrontier", "Eq/PTreeKernel"}
        if module != "Prob/FreeOmega/Validation/Soundness" and dependency in {
                "Prob/FreeOmega/Validation/Soundness", "Prob/FreeOmega/Validation/StableHitting"}:
            return False
        return under("Prob/Domain", "Prob/Interface", "Prob/FreeOmega")
    if module in {"Prob/Backend/Common/DomainTransport", "Prob/Backend/Common/CountableCoupling", "Prob/Backend/Common/CountableRelationalLimit"}:
        return under("Prob/Domain", "Prob/Backend/Common")
    # A generic theorem layer may not silently fix its observable carrier.
    if ownership(module)[1] == "generic" and ownership(dependency)[1] == "FreeOmega":
        return False
    if module == "PTree":
        return under("Core")
    if module == "Eq":
        return dependency in {"Eq/PStruct", "Eq/PStrong", "Eq/PEutt", "Eq/Canonical", "Eq/UpToPeutt", "Eq/UpToProb"}
    if module == "PTreeFacts":
        return dependency in {"PTree", "Eq", "Eq/UnifiedFrontier", "Eq/PrimitiveStableHitting",
            "Eq/WellFormedness", "Eq/StableHittingComputation", "Eq/ProbabilisticTrace", "Eq/Bind", "Eq/Algebra", "Eq/Iter",
            "Eq/FreeOmega/Bind", "Eq/FreeOmega/Algebra", "Eq/FreeOmega/Iter",
            "Interp/Guarded", "Interp/FreeOmega/Atomic", "Interp/FreeOmega/MDP",
            "Interp/Unrestricted", "Interp/HandlerRelation", "Interp/HandlerFacts",
            "Interp/State", "Interp/Reader", "Interp/Writer", "Interp/Exception",
            "Interp/StateFacts", "Interp/StatePreservation", "Interp/StandardFacts",
            "Interp/ExceptionFacts", "Interp/FreeOmega/HandlerCompletion",
            "Interp/FoldPTree", "Interp/StateFold", "Interp/StateFoldFacts"}
    if module == "Semantics":
        return under("Semantics")
    if module.startswith("Core/"):
        return under("Core")
    if module == "Execution/Validation/SubEnumQ":
        return under("Core", "Execution", "Prob", "Eq")
    if module.startswith("Execution/Validation/"):
        return under("Core", "Execution", "Prob/Backend/Common", "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ")
    if module.startswith("Execution/Backend/"):
        return under("Core", "Execution", "Prob/Backend/Common", "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ")
    if module.startswith("Execution/"):
        return under("Core", "Execution") and not under("Execution/Backend")
    if module.startswith("Prob/Interface/"):
        return under("Prob/Interface")
    if module.startswith("Prob/FreeOmega/"):
        return under("Prob/Interface", "Prob/FreeOmega")
    if module.startswith("Prob/Backend/Common/"):
        return under("Prob/Interface", "Prob/Backend/Common")
    if module.startswith("Prob/Backend/MathComp/"):
        return under("Prob/Interface", "Prob/Backend/Common", "Prob/Backend/MathComp", "Prob/Domain")
    if module.startswith("Prob/Backend/SubEnumR/"):
        if module == "Prob/Backend/SubEnumR/RationalEmbedding":
            return under("Prob/Backend/SubEnumR", "Prob/Backend/SubEnumQ",
                         "Prob/Backend/EnumQ", "Prob/Backend/Common")
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/SubEnumR", "Prob/Domain")
    if module.startswith(("Prob/Backend/EnumQ/", "Prob/Backend/SubEnumQ/")):
        # SubEnumQ is a validated EnumQ carrier, not an unrelated implementation.
        # Realization/observation adapters legitimately cross this boundary.
        return under("Prob/Interface", "Prob/FreeOmega", "Prob/Backend/Common",
                     "Prob/Backend/EnumQ", "Prob/Backend/SubEnumQ", "Prob/Domain")
    if module.startswith("Prob/Legacy/"):
        return under("Prob")
    if module.startswith("Eq/"):
        ok = under("Core", "Prob", "Eq")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend")
        return ok
    if module.startswith("Semantics/"):
        ok = under("Core", "Prob", "Eq", "Semantics")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend", "Semantics/Backend")
        return ok
    if module.startswith("Interp/"):
        ok = under("Core", "Prob", "Eq", "Semantics", "Interp")
        if "/Backend/" not in module:
            ok = ok and not under("Prob/Backend", "Prob/Legacy", "Eq/Backend", "Eq/Internal/Backend", "Semantics/Backend", "Interp/Backend")
        return ok
    if module.startswith("Examples/"):
        return not under("Tests", "Experimental")
    if module.startswith("Tests/"):
        return True
    return False


def closure(edges, roots):
    seen, todo = set(), list(roots)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo.extend(edges[module])
    return seen


def check_auxiliary_boundary(edges):
    # Formal theory/facades, not the regression fixtures used to test them.
    roots = {m for m in edges if m.startswith("Interp/")}
    roots |= {m for m in {"Eq/PEutt", "Eq/Canonical", "PTree", "Eq", "PTreeFacts", "Semantics"} if m in edges}
    internal = {m for m in closure(edges, roots) if m.startswith("Eq/Internal/")}
    assert not internal, "Formal mainline depends on auxiliary internal machinery: " + str(sorted(internal))


def check_external_validation_boundary(edges):
    # Explicit validation adapters can live under Eq/Backend; they validate
    # reasoning and must not themselves be counted as reasoning roots.
    roots = {m for m in edges if not external_validation(m) and m.startswith(
        ("Core/", "Eq/", "Semantics/", "Interp/", "Execution/", "Examples/"))}
    roots |= {m for m in ("PTree", "Eq", "PTreeFacts", "Semantics") if m in edges}
    leaked = {m for m in closure(edges, roots) if external_validation(m)}
    assert not leaked, "Mainline depends on external validation: " + str(sorted(leaked))


def check_native_expectation_boundary(edges):
    # Native SubEnumQ validation precedes formal omega completion, even through
    # indirect finite-helper imports. Upper evaluators may use finite facts,
    # but finite facts must never depend on external validation in return.
    roots = {m for m in ("Prob/Backend/SubEnumQ/Expectation",
                         "Prob/Backend/SubEnumQ/NativeLimit",
                         "Prob/Backend/SubEnumQ/Domain", "Prob/Backend/SubEnumR/Domain",
                         "Prob/Backend/SubEnumR/Representation", "Prob/Backend/SubEnumR/Measure") if m in edges}
    leaked = {m for m in closure(edges, roots) if "/FreeOmega/" in m}
    assert not leaked, "Native expectation/domain depends on FreeOmega: " + str(sorted(leaked))
    finite = "Prob/Backend/SubEnumQ/Expectation"
    if finite in edges:
        leaked = {m for m in closure(edges, {finite}) if external_validation(m)}
        assert not leaked, "Finite expectation depends on validation: " + str(sorted(leaked))


def check_generic_validation_boundary(edges):
    # Canonical adapters must not quietly route through old rational validation,
    # joint existence, or the PTree-facing validation entry point.
    roots = {m for m in ("Prob/Backend/SubEnumQ/FreeOmega/Validation",
                         "Prob/Backend/SubEnumR/FreeOmega/Validation") if m in edges}
    allowed = {"Prob/Backend/SubEnumQ/FreeOmega/Validation",
               "Prob/Backend/SubEnumR/FreeOmega/Validation"}
    bad = {m for m in closure(edges, roots) if
           (m.startswith("Prob/Backend/") and "/FreeOmega/" in m and m not in allowed)
           or m.startswith(("Core/", "Eq/", "Interp/", "Semantics/"))}
    assert not bad, "Native validation adapter depends on specialized completion/tree theory: " + str(sorted(bad))
    # Canonical countable support and external joint realization likewise
    # bypass the legacy scalar/compatibility route, for both finite backends.
    clients = {"Prob/Backend/" + backend + "/FreeOmega/" + name
               for backend in ["SubEnumQ", "SubEnumR"]
               for name in ["CountableSupport", "JointRealization"]}
    bad = {m for m in closure(edges, clients & edges.keys()) if
           (m.startswith("Prob/Backend/") and "/FreeOmega/" in m
            and m not in allowed | clients)
           or m.startswith(("Core/", "Eq/", "Interp/", "Semantics/"))}
    assert not bad, "Canonical realization depends on legacy validation/tree theory: " + str(sorted(bad))


def aggregate_check(actual=None, expected=None):
    if expected is None:
        expected = sorted('PTree.' + module_key(p).replace('/', '.')
                          for p in source_files()
                          if module_key(p) not in GATE_M | {AGGREGATE})
    if actual is None:
        actual = re.findall(r'^Require (PTree\.[\w.]+)\.$',
                            source_path(AGGREGATE).read_text(), re.M)
    assert actual == sorted(set(expected)), 'AllImports must contain every other Gate S module exactly once, sorted'


def check_mathcomp_native_sources(sources):
    """Reject the removed concrete completion, including simple local aliases.

    This is a source guard, not a Coq elaborator. The import-closure check
    independently excludes completion dependencies from all native modules.
    Generic arbitrary-MN completion theorems remain unrestricted.
    """
    for module, text in sources.items():
        code = re.sub(r'"(?:""|[^"\n])*"', '""', without_comments(text))
        assert not re.search(r'\bMathCompBehaviorMeasure\b', code), \
            'Removed behavioral alias: ' + module
        if module.startswith('Prob/Backend/MathComp/'):
            assert not re.search(r'\b(?:FreeOmega\w*|free_omega_\w*)\b', code), \
                'Native MathComp source mentions formal completion: ' + module
        native_names = {'MathCompKernelMeasure'}
        aliases = re.findall(
            r'\b(?:Notation|Let|Definition)\s+(\w+)[^\n]*?:=\s*\(?\s*@?\s*'
            r'((?:\w+\.)*\w+)\b', code)
        while True:
            extended = native_names | {name for name, target in aliases
                                       if target.rsplit('.', 1)[-1] in native_names}
            if extended == native_names:
                break
            native_names = extended
        names = '|'.join(re.escape(n) for n in sorted(native_names))
        assert not re.search(r'\b(?:FreeOmega|FreeOmegaAt)\s*\(?\s*@?\s*'
                             r'(?:\w+\.)*(?:' + names + r')\b', code), \
            'Removed MathComp completion instantiation: ' + module


def check_mathcomp_native_boundary(edges):
    roots = {m for m in edges if m.startswith('Prob/Backend/MathComp/')}
    leaked = {m for m in closure(edges, roots) if m.startswith('Prob/FreeOmega/')}
    assert not leaked, 'Native MathComp transitively loads completion: ' + str(sorted(leaked))


def graph():
    aggregate_check()
    check_mathcomp_native_sources({module_key(p): p.read_text() for p in source_files()})
    paths = {module_key(p) for p in source_files()}
    edges = {p: set() for p in paths}
    seen = set()
    built = ROOT / '_build/default'
    local_objects = {(built / p.relative_to(ROOT)).with_suffix('.vo').resolve(): module_key(p)
                     for p in source_files()}
    for directory, prefix in SOURCE_ROOTS:
        folder = built / directory
        depfile = folder / '.PTree.theory.d'
        for line in depfile.read_text().splitlines():
            lhs, rhs = line.split(": ", 1)
            target = lhs.split()[0]
            if not target.endswith('.vo'):
                continue
            module = local_objects.get((folder / target).resolve())
            assert module in edges, 'Stale coqdep target: ' + target
            seen.add(module)
            for dep in rhs.split():
                if not dep.endswith('.vo'):
                    continue
                resolved = (folder / dep).resolve()
                if resolved in local_objects:
                    edges[module].add(local_objects[resolved])
                elif resolved.is_relative_to(built):
                    raise AssertionError('Missing local dependency: ' + dep)
    assert seen == paths, "Run a full build: incomplete coqdep graph"
    assert edges[AGGREGATE] == paths - {AGGREGATE} - GATE_M, "Incomplete safe AllImports"
    check_gate_boundary(edges)
    assert all(AGGREGATE not in ds for ds in edges.values()), "Aggregate used as library"
    for module, deps in edges.items():
        ownership(module)
        for dep in deps:
            assert permitted(module, dep), "Forbidden ownership edge: " + module + " -> " + dep
    check_auxiliary_boundary(edges)
    check_external_validation_boundary(edges)
    check_generic_validation_boundary(edges)
    check_native_expectation_boundary(edges)
    check_mathcomp_native_boundary(edges)
    return edges


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aggregate-only", action="store_true")
    parser.add_argument("--inventory", action="store_true", help="Print current ownership and direct clients (TSV)")
    args = parser.parse_args()
    if args.aggregate_only:
        if args.inventory:
            parser.error("--inventory needs the compiled dependency graph")
        aggregate_check()
        print('AllImports coverage/order/uniqueness passed (no build required).')
    else:
        edges = graph()
        print(f'{len(edges)} modules; {sum(map(len, edges.values()))} checked dependency edges.')
        if args.inventory:
            clients = {m: 0 for m in edges}
            for module, deps in edges.items():
                if module != AGGREGATE:
                    for dep in deps:
                        clients[dep] += 1
            print('Module\tOwner\tProfile\tDisposition\tDirect clients (excluding AllImports)')
            for module in sorted(edges):
                print('\t'.join([module, *ownership(module), str(clients[module])]))
