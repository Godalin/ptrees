#!/usr/bin/env python3
"""Gate B proof-text conservation, independent of whether the library builds.

Compare the frozen Gate A source with all migrated sources and extracted
sections. Ignore comments, Require commands, whitespace and the explicit
namespace relocation map; do not ignore theorem statements or proof bodies.
The API/aggregate exceptions are explicitly enumerated, not blanket globs.
"""
import io
import json
import re
import subprocess
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = "2258907"
MANIFEST = json.loads((ROOT / "docs/gate-b-moves.json").read_text())
MOVES = MANIFEST["moves"]
REQUIRE = re.compile(r"\b(?:From\s+([\w.]+)\s+)?Require\s+(?:(Import|Export)\s+)?([\w.\s]+?)\.(?=\s|$)")
EXTRACTS = [
    ("Core/PTreeDefinition", "API/Weighted", "Section stuck.", "End stuck."),
    ("Eq/FreeOmega/Base", "Interp/FreeOmega/Translate", "Section TranslateApproximants.", "End TranslatePreservation."),
    ("Eq/FreeOmega/Bind", "Interp/FreeOmega/Cofinality", "Section InterpCofinality.", "End InterpCofinality."),
    ("Eq/PTreeKernel", "Interp/Kernel", "Section KernelInterpDiagonal.", "End KernelInterpSoundness."),
    ("Eq/PStruct", "Interp/Structural", "Section PStructInterp.", "End PStructInterpHandlerCongruence."),
]
# Intentional new facade aliases and the new aggregate import list. None
# contains a changed Stage 1-4 proof. Original program syntax/semantic
# definitions in every other old module remain checked below.
ASSEMBLY = {"theories/Eq/FreeOmega.v", "theories/Eq/ProbabilisticSemantics.v",
            "theories/Regression/Infrastructure/AllImports.v"}


def logical(path):
    return "PTree." + path.removeprefix("theories/").removesuffix(".v").replace("/", ".")


def without_comments(source):
    result, depth, quoted, i = [], 0, False, 0
    while i < len(source):
        pair = source[i:i+2]
        if not quoted and pair == "(*":
            depth += 1
            i += 2
        elif depth and pair == "*)":
            depth -= 1
            i += 2
            if not depth:
                result.append(" ")
        elif depth:
            i += 1
        else:
            if source[i] == '"':
                if quoted and pair == '""':
                    result.append(pair)
                    i += 2
                    continue
                quoted = not quoted
            result.append(source[i])
            i += 1
    assert depth == 0, "Unclosed comment"
    return "".join(result)


def frozen():
    data = subprocess.check_output(["git", "archive", BASE, "theories"], cwd=ROOT)
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        return {m.name: archive.extractfile(m).read().decode()
                for m in archive.getmembers() if m.name.endswith(".v")}


def interval(source, start, end):
    a = source.index(start)
    b = source.index(end, a) + len(end)
    return source[a:b], source[:a] + source[b:]


def normalizer():
    module_map = {logical(new): logical(old) for old, new in MOVES.items()}
    symbols = {}
    for src, target, names in MANIFEST["splits"]:
        for name in names:
            symbols["PTree." + target.replace("/", ".") + "." + name] = "PTree." + src.replace("/", ".") + "." + name
    short_symbols = {".".join(new.split(".")[-2:]): ".".join(old.split(".")[-2:])
                     for new, old in symbols.items()}
    for filename, source in frozen().items():
        new = MOVES.get(filename, filename)
        old_base = Path(filename).stem
        new_base = Path(new).stem
        if old_base != new_base:
            declarations = re.findall(r"^(?:Polymorphic )?(?:Definition|Lemma|Theorem|Corollary|Inductive|Record|Class)\s+(\w+)", source, re.M)
            for name in declarations:
                short_symbols[new_base + "." + name] = old_base + "." + name
    def normalize(source):
        source = REQUIRE.sub("", without_comments(source))
        def qualify(match):
            token = match[0]
            if token in symbols:
                return symbols[token]
            candidates = [n for n in module_map if token == n or token.startswith(n + ".")]
            if candidates:
                n = max(candidates, key=len)
                return module_map[n] + token[len(n):]
            return token
        source = re.sub(r"\bPTree(?:\.\w+)+", qualify, source)
        for new, old in short_symbols.items():
            source = re.sub(r"(?<![\w.])" + re.escape(new) + r"\b", old, source)
        # Fully qualified split references replace formerly short module names.
        for _, old in symbols.items():
            short = ".".join(old.split(".")[-2:])
            source = source.replace(old, short)
        for old, new in [("PTreeProbability", "WellFormedness"), ("GuardedInterp", "Guarded"),
                         ("AtomicInterp", "Atomic"), ("MDPInterp", "MDP")]:
            source = re.sub(r"(?<![\w.])" + new + r"\.(?=\w)", old + ".", source)
        # Whitespace inside a Coq string is data, not layout. Preserve it.
        parts = re.split(r'("(?:[^"]|"")*")', source)
        return "".join(part if i % 2 else re.sub(r"\s+", " ", part)
                       for i, part in enumerate(parts)).strip()
    return normalize


def audit():
    sources = frozen()
    normalize = normalizer()
    for src, target, start, end in EXTRACTS:
        filename = "theories/" + src + ".v"
        body, sources[filename] = interval(sources[filename], start, end)
        current, _ = interval((ROOT / ("theories/" + target + ".v")).read_text(), start, end)
        assert normalize(body) == normalize(current), "Changed extracted section: " + target
    count = 0
    for old, source in sources.items():
        if old in ASSEMBLY:
            continue
        new = MOVES.get(old, old)
        current = (ROOT / new).read_text()
        if old == "theories/Core/PTreeSubEnum.v":
            current = re.sub(r"Notation subenum_mdp_state_interp_atomic :=[\s\S]*?\.\n", "", current)
        if normalize(source) != normalize(current):
            import difflib
            difference = "\n".join(difflib.unified_diff(normalize(source).split(" "), normalize(current).split(" "), n=3))
            raise AssertionError("Changed non-namespace proof text: " + old + " -> " + new + "\n" + difference[:3000])
        count += 1
    print(f"Gate B text conservation passes: {count} original modules and {len(EXTRACTS)} extracted sections; "
          f"{len(ASSEMBLY)} explicit facade/aggregate exceptions. No proof/theorem deletion.")


if __name__ == "__main__":
    audit()
