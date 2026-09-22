#!/usr/bin/env python3
"""Phase 4b.1: production position extraction; no rational carrier switch yet.

Replay the 49 frozen IndexedCoupling declarations in an isolated Coq session
and compare elaborated types AND logical assumptions, never recapture a
post-migration baseline. All other old theory and snapshot files stay exact.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

from audit_assumptions import without_comments, parse, query, logical_axioms

ROOT = Path(__file__).resolve().parents[1]
BASELINE = '7121338'
CLIENT = 'theories/Prob/Backend/EnumQ/IndexedCoupling.v'
COMMON = 'theories/Prob/Backend/Common/FinitePositions.v'
REGRESSION = 'theories/Regression/Backend/RationalPositions.v'
AGGREGATE = 'theories/Regression/Infrastructure/AllImports.v'
POLICY = 'docs/CONTRACT_POLICY.json'
REPORT = 'docs/ARCHITECTURE_AUDIT.md'
MODULE = 'PTree.Prob.Backend.EnumQ.IndexedCoupling'
PROOFS = {
    'emap_fst_value_index_joint_from': 'Proof. exact: finite_value_index_fst. Qed.',
    'emap_snd_value_index_joint_from': 'Proof. exact: finite_value_index_snd. Qed.',
    'index_from_shift_from': '''Proof.
  revert offset start.
  induction mu as [|[p a] mu IH]; intros offset start; cbn.
  - reflexivity.
  - unfold shift_index at 1.
    rewrite <- Nat.add_succ_r.
    unfold index_from in IH.
    rewrite IH. reflexivity.
Qed.''',
    'index_from_scale': '''Proof.
  revert offset.
  induction mu as [|[q a] mu IH]; intro offset; cbn=> //.
  unfold index_from in IH.
  rewrite IH. reflexivity.
Qed.''',
    'index_from_app': '''Proof.
  revert offset.
  induction mu as [|[p a] mu IH]; intro offset; cbn.
  - rewrite Nat.add_0_r. reflexivity.
  - unfold index_from in IH. rewrite IH Nat.add_succ_r. reflexivity.
Qed.''',
    'index_from_bind_EnumQ': '''Proof.
  revert offset.
  induction mu as [|[p a] mu IH]; intro offset;
    cbn [bind_EnumQ seq.foldr indexed_bind_blocks]=> //.
  rewrite index_from_app index_from_scale size_scale_EnumQ IH.
  reflexivity.
Qed.''',
    'index_from_bind_as_position_bind': '''Proof.
  revert start offset.
  induction mu as [|[p a] mu IH]; intros start offset;
    cbn [bind_EnumQ seq.foldr index_from finite_index_from]=> //.
  change (index_from offset (scale_EnumQ p (k a) ++ bind_EnumQ mu k) =
    scale_EnumQ p (indexed_bind_block_from ((p,a)::mu) k start offset start) ++
    bind_EnumQ (index_from start.+1 mu)
      (indexed_bind_block_from ((p,a)::mu) k start offset)).
  rewrite index_from_app index_from_scale size_scale_EnumQ.
  rewrite (IH start.+1 (Nat.add offset (size (k a)))).
  congr (_ ++ _).
  - cbn. by rewrite Nat.eqb_refl.
  - apply bind_EnumQ_ext_in=> q i Hi. cbn.
    have Hneq : Nat.eqb i start = false.
    { apply Nat.eqb_neq=> Heq. subst i.
      have Hge := index_from_in_ge Hi. lia. }
    by rewrite Hneq.
Qed.''',
}


def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def names(source, kinds='Lemma|Theorem|Example'):
    return re.findall(r'^(?:' + kinds + r')\s+(\w+)', without_comments(source), re.M)


def adapted(source):
    result = source.replace('Set Implicit Arguments.',
        'From PTree.Prob.Backend.Common Require Import FinitePositions.\n\nSet Implicit Arguments.', 1)
    # The Require is placed with the original imports, preserving their order.
    result = result.replace('\n\nFrom PTree.Prob.Backend.Common Require Import FinitePositions.',
                            '\nFrom PTree.Prob.Backend.Common Require Import FinitePositions.', 1)
    for name, replacement in {
        'index_from': '''Definition index_from {A} (n : nat) (mu : EnumQ A) : EnumQ nat :=
  finite_index_from n mu.''',
        'value_index_joint_from': '''Definition value_index_joint_from {A} (n : nat) (mu : EnumQ A)
    : EnumQ (A * nat) :=
  finite_value_index_from n mu.''',
    }.items():
        result, count = re.subn(r'^Fixpoint ' + name + r'\b[\s\S]*?  end\.', replacement, result, count=1, flags=re.M)
        assert count == 1
    for name, proof in PROOFS.items():
        pattern = r'(^Lemma ' + name + r'\b[\s\S]*?\n)(Proof\.[\s\S]*?Qed\.)'
        result, count = re.subn(pattern, lambda m: m[1] + proof, result, count=1, flags=re.M)
        assert count == 1
    return result


def common_boundary(source):
    code = without_comments(source)
    assert not re.search(r'\b(?:Axiom|Axioms|Parameter|Parameters|Admitted|admit|Class|Coercion|Instance)\b', code)
    assert not re.search(r'\b(?:Semantic\w*|FreeOmega|OmegaVal|ptree|nnQ|EnumQ|SubEnum\w*|coupling|realType)\b', code)
    assert not re.search(r'Unset\s+(?:Universe|Guard|Positivity)\s+Checking|bypass_check', code)
    deps = [line.strip() for line in code.splitlines() if 'PTree.' in line]
    assert deps == ['From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.']


def client_check(old, new):
    assert new == adapted(old), 'Unapproved client change'


def check():
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines()
    new = {COMMON, REGRESSION}
    theories = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'theories').rglob('*.v')}
    assert theories == {p for p in paths if p.endswith('.v')} | new
    for path in paths:
        old, actual = frozen(path), (ROOT / path).read_bytes()
        if path == REPORT:
            continue
        if path == CLIENT:
            client_check(old.decode(), actual.decode())
        elif path == AGGREGATE:
            lines = old.decode().splitlines(keepends=True)
            added = ['Require PTree.' + p.removeprefix('theories/').removesuffix('.v').replace('/', '.') + '.\n' for p in new]
            imports = iter(sorted([line for line in lines if line.startswith('Require PTree.')] + added))
            result = [next(imports) if line.startswith('Require PTree.') else line for line in lines]
            assert actual.decode() == ''.join(result + list(imports))
        elif path == POLICY:
            policy = json.loads(actual)
            assert policy['regressions'].pop(REGRESSION) == names((ROOT / REGRESSION).read_text())
            assert policy == json.loads(old)
        else:
            assert actual == old, 'Frozen source/snapshot/tool changed: ' + path
    common_boundary((ROOT / COMMON).read_text())
    from audit_architecture import report
    assert (ROOT / REPORT).read_text() == report()
    print('Phase 4b.1: two exact position extractions, seven approved proof adaptations; '
          'all relation definitions, theorem statements, other backend files and snapshots unchanged.')


def endpoint_query(source, endpoints, queried):
    source += '\nSet Printing Width 100. Set Printing Depth 1000. Set Printing Implicit. Unset Printing Notations.\n'
    for i, name in enumerate(queried):
        source += f'Goal True. idtac "AUDIT_TYPE_{i}". Abort.\nCheck @{name}.\n'
        source += f'Goal True. idtac "AUDIT_AXIOMS_{i}". Abort.\nPrint Assumptions {name}.\n'
        source += f'Goal True. idtac "AUDIT_END_{i}". Abort.\n'
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R', '_build/default/theories', 'PTree'],
                            input=source, text=True, capture_output=True, cwd=ROOT)
    return parse(result, endpoints)


def normalize(text):
    # Only the intentionally fresh historical namespace and print whitespace.
    return ' '.join(text.replace('Phase4bBaseline.', 'IndexedCoupling.IndexedCoupling.').split())


def compare(old, new):
    assert len(old) == len(new)
    for a, b in zip(old, new):
        assert a['name'] == b['name']
        for field in ('type', 'assumptions'):
            assert normalize(a[field]) == normalize(b[field]), (a['name'], field, a[field], b[field])


def compiled_check():
    source = frozen(CLIENT).decode()
    declarations = names(source, 'Definition|Fixpoint|Lemma|Theorem')
    endpoints = [MODULE + '.IndexedCoupling.' + n for n in declarations]
    prefix = source.split('Module IndexedCoupling.')[0]
    current = endpoint_query('Require ' + MODULE + '.\n' + prefix, endpoints, endpoints)
    reference = source.replace('Module IndexedCoupling.', 'Module Phase4bBaseline.').replace(
        'End IndexedCoupling.', 'End Phase4bBaseline.').replace('Export IndexedCoupling.', '')
    baseline = endpoint_query(reference, endpoints, ['Phase4bBaseline.' + n for n in declarations])
    compare(baseline, current)
    print(f'{len(endpoints)} indexed declarations: elaborated types and assumptions equal to independently replayed {BASELINE}.')
    fresh = []
    for path in (COMMON, REGRESSION):
        module = 'PTree.' + path.removeprefix('theories/').removesuffix('.v').replace('/', '.')
        fresh += [module + '.' + n for n in names((ROOT / path).read_text(), 'Definition|Fixpoint|Lemma|Theorem|Example')]
    for entry in query(fresh):
        assert not logical_axioms(entry['assumptions']), entry
    print(f'{len(fresh)} shared/regression constants: closed under the global context.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    check()
    if not args.source_only:
        compiled_check()
