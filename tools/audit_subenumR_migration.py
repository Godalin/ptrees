#!/usr/bin/env python3
"""Phase 3 SubEnumR-only migration gate; earlier phase gates stay frozen."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from audit_assumptions import query, logical_axioms, SOUNDNESS_AXIOMS, without_comments

ROOT = Path(__file__).resolve().parents[1]
BASELINE = 'aac7516'
SNAPSHOT = ROOT / 'docs/SUBENUMR_MIGRATION_CONTRACTS.json'
BEHAVIOR = 'theories/Regression/Backend/SubEnumRBehavior.v'
JOINT = 'theories/Regression/Probability/SubEnumRJointRealization.v'
REPRESENTATION = 'theories/Prob/Backend/SubEnumR/Representation.v'
REGRESSION = 'theories/Regression/Backend/SubEnumRShared.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'
BASELINE_DIGEST = '24e1bdc1414edd9d2a6973cf351fe95648b534a43428c3a878397ccd59858342'

# Exact, reviewed proof adaptations for clients that unfolded the old native
# Fixpoint. No semantic proof/theorem beyond these transformations is relaxed.
EXPECT_AE = (
    '  induction mu as [|[p x] tl IH]; intros H; cbn [real_enum_expect]; first reflexivity.',
    '  induction mu as [|[p x] tl IH]; intros H;\n    rewrite ?real_enum_expect_cons ?real_enum_expect_nil; first reflexivity.')
ADAPTATIONS = {
    'theories/Prob/Backend/SubEnumR/Domain.v': [EXPECT_AE, (
        '  intros Hnn Hf Hi; induction mu as [|[p x] tl IH]; cbn [real_enum_expect].',
        '  intros Hnn Hf Hi; induction mu as [|[p x] tl IH];\n    rewrite ?real_enum_expect_cons ?real_enum_expect_nil.')],
    'theories/Prob/Backend/SubEnumR/Coupling.v': [EXPECT_AE, (
        '  cbn [real_enum_expect]; destruct Hin as [He|Hin].',
        '  rewrite real_enum_expect_cons; destruct Hin as [He|Hin].'), (
        '  cbn [real_enum_expect fst snd]; congr (_ + _).',
        '  rewrite real_enum_expect_cons; cbn [fst snd]; congr (_ + _).'), (
        '  clear IH tl; induction nu as [|[q y] rest IHn]; cbn; first by rewrite mulr0.',
        '  clear IH tl; induction nu as [|[q y] rest IHn];\n    cbn [List.map fst snd]; rewrite ?real_enum_expect_cons ?real_enum_expect_nil;\n    first by rewrite mulr0.'), (
        '  induction mu as [|[p x] tl IH]; cbn [real_enum_expect].',
        '  induction mu as [|[p x] tl IH];\n    rewrite ?real_enum_expect_cons ?real_enum_expect_nil.'), (
        '  refine (@Build_SubEnumR R (A*C) raw _ _).',
        '  refine (@subenumR_of_list R (A*C) raw _ _).')],
    'theories/Prob/Backend/SubEnumR/RationalEmbedding.v': [(
        'Proof. induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite IH]. Qed.',
        'Proof.\n  induction mu as [|[p x] tl IH]; first reflexivity.\n  change (real_enum_expect f ((ratr (Qval p),x)::real_of_enumQ tl) =\n    ratr (Qval p) * f x + enumQ_real_expect f tl).\n  by rewrite real_enum_expect_cons IH.\nQed.'), (
        '  refine (@Build_SubEnumR R A (real_of_enumQ (subenumQ_raw mu)) _ _).',
        '  refine (@subenumR_of_list R A (real_of_enumQ (subenumQ_raw mu)) _ _).')],
    'theories/Regression/Backend/SubEnumRRelational.v': [(
        '  refine (@Build_SubEnumR R bool [(1/4,true); (1/4,true); (0,false)] _ _).',
        '  refine (@subenumR_of_list R bool [(1/4,true); (1/4,true); (0,false)] _ _).')],
}


def frozen_files():
    return subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines()


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def endpoints():
    names = []
    for path in frozen_files():
        if not (path.startswith('theories/Prob/Backend/SubEnumR/') and path.endswith('.v')
                or path in {BEHAVIOR, JOINT}):
            continue
        code = without_comments(frozen(path).decode())
        decls = re.findall(r'^(?:#\[global\]\s+)?(?:Definition|Fixpoint|Record|Lemma|Theorem|Example|Instance)\s+(\w+)', code, re.M)
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        names.extend(module + '.' + n for n in decls)
    return names


def capture_baseline():
    # This mode is usable only before changing ANY old theory source.
    for path in frozen_files():
        if path.endswith('.v'):
            assert (ROOT / path).read_bytes() == frozen(path), 'Capture must precede migration: ' + path
    data = {'baseline': BASELINE, 'endpoints': query(endpoints())}
    print(json.dumps(data, indent=2, ensure_ascii=False))


def adapted(path, text):
    for before, after in ADAPTATIONS.get(path, []):
        assert text.count(before) == 1, 'Stale adaptation: ' + path
        text = text.replace(before, after)
    return text


def theorem_statements(text):
    return {m[0]: ' '.join(m[1].split()) for m in re.findall(
        r'^(?:Lemma|Theorem)\s+(\w+)([\s\S]*?)\bProof\.', without_comments(text), re.M)}


def definition(text, name):
    m = re.search(r'^Definition\s+' + name + r'\b[\s\S]*?\.(?=\s|$)', without_comments(text), re.M)
    assert m, 'Missing definition: ' + name
    return ' '.join(m[0].split())


def representation_check(old, new):
    code = without_comments(new)
    assert not re.search(r'\b(?:Record|Inductive|CoInductive|Fixpoint|Class|Axiom|Parameter|Admitted|induction)\b', code)
    assert 'Build_SubEnumR' not in code
    assert definition(new, 'SubEnumR') == 'Definition SubEnumR (A : Type) := FiniteSubdist R A.'
    assert 'Lemma subenumR_nonnegative' in code
    assert 'finite_enum_nonnegative (finite_subdist_enum mu)' in code
    for name, body in {
        'real_enum_expect': 'finite_expect f mu',
        'real_enum_nonnegative': 'finite_nonnegative mu',
        'subenumR_raw': 'finite_enum_raw (finite_subdist_enum mu)',
        'subenumR_of_list': 'finite_subdist_of_list Hnn Hmass',
        'subenumR_ret': 'finite_subdist_ret R x',
        'subenumR_zero': '@finite_subdist_zero R A',
        'subenumR_bind': 'finite_subdist_bind mu k',
        'real_enum_bind': 'finite_bind mu (fun x => subenumR_raw (k x))',
    }.items():
        assert definition(new, name).endswith(':= ' + body + '.'), 'Not shared implementation: ' + name
    for name in ['subenumR_eq', 'subenumR_ae', 'subenumR_lift', 'subenumR_expect']:
        assert definition(new, name) == definition(old, name), 'Changed native semantics: ' + name
    prior, current = theorem_statements(old), theorem_statements(new)
    for name, statement in prior.items():
        assert current.get(name) == statement, 'Changed theorem statement: ' + name
    # Backend-facing finite lemmas are only specializations, not copied proofs.
    for suffix in ['ext', 'zero', 'add', 'scale', 'mono', 'nonnegative', 'ae_mono', 'app', 'weight_map', 'bind']:
        assert 'Proof. exact: finite_expect_' + suffix + '. Qed.' in code, suffix


def source_check():
    paths = frozen_files()
    previous = {p for p in paths if p.endswith('.v')}
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')}
    assert actual == previous | {REGRESSION}, 'Unexpected module addition/deletion'
    for path in paths:
        old, new = frozen(path), (ROOT / path).read_bytes()
        if path == REPRESENTATION:
            representation_check(old.decode(), new.decode())
        elif path in ADAPTATIONS:
            assert new.decode() == adapted(path, old.decode()), 'Unexpected client edit: ' + path
        elif path == AGGREGATE:
            line = b'Require PTree.Regression.Backend.SubEnumRShared.\n'
            assert new.count(line) == 1 and new.replace(line, b'') == old
        elif path == POLICY:
            expected, current = json.loads(old), json.loads(new)
            names = re.findall(r'^Example\s+(\w+)', (ROOT / REGRESSION).read_text(), re.M)
            assert current['regressions'].pop(REGRESSION) == names
            assert current == expected, 'Frozen policy altered'
        elif path != REPORT:
            assert new == old, 'Frozen file altered: ' + path
    from audit_architecture import report
    assert (ROOT / REPORT).read_text() == report(), 'Architecture inventory stale'
    assert hashlib.sha256(SNAPSHOT.read_bytes()).hexdigest() == BASELINE_DIGEST, 'Migration baseline refreshed'
    print('Phase 3: shared SubEnumR carrier; exact scoped client adaptations; all other old sources/snapshots unchanged.')


def compiled_check():
    assert hashlib.sha256(SNAPSHOT.read_bytes()).hexdigest() == BASELINE_DIGEST
    data = json.loads(SNAPSHOT.read_text())
    assert data['baseline'] == BASELINE
    assert [e['name'] for e in data['endpoints']] == endpoints()
    actual = query(endpoints())
    compare_contracts(data['endpoints'], actual)
    print(f"{len(actual)} SubEnumR native/validation/behavior/joint contracts: identical types and logical assumptions.")


def compare_contracts(expected, actual):
    assert len(expected) == len(actual), 'Endpoint count changed'
    for before, after in zip(expected, actual):
        assert before['name'] == after['name'], 'Endpoint identity changed'
        assert ' '.join(before['type'].split()) == ' '.join(after['type'].split()), 'Type drift: ' + before['name']
        # Match the actual pre-migration per-endpoint contract, as the mainline
        # audit does. Behavioral bind has pre-existing relational/unique choice
        # dependencies absent from the narrower external-soundness whitelist.
        logical_axioms(before['assumptions']); logical_axioms(after['assumptions'])
        assert ' '.join(before['assumptions'].split()) == ' '.join(after['assumptions'].split()), \
            'Assumption drift: ' + before['name']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture-baseline', action='store_true')
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    if args.capture_baseline:
        capture_baseline()
    else:
        source_check()
        if not args.source_only:
            compiled_check()
