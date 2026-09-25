#!/usr/bin/env python3
"""Eventful iteration: additive theory, immutable old endpoints, no new capabilities."""
import argparse
import json
import re
import subprocess
from functools import lru_cache
from audit_assumptions import ROOT, query, compare, logical_axioms, SOUNDNESS_AXIOMS, without_comments
from audit_mathcomp_direct import parse_direct

BASELINE = 'b592fde'
ALL = 'theories/Regression/Infrastructure/AllImports.v'
DIRECT = 'theories/Regression/Backend/MathCompDirect.v'
MODULES = ['Interp/Iteration', 'Interp/FreeOmega/Iteration', 'Regression/Semantics/EventfulIteration']
NEW = {'theories/' + m + '.v' for m in MODULES}
IMPORTS = {'Require PTree.' + m.replace('/', '.') + '.' for m in MODULES}
DIRECT_APPEND = """
(** Eventful behavioral congruence, not the entry-only closure rule above.
    Only direct assembly is unchecked. Gluing and relational-lub remain
    explicit mathematical premises; no claim that they are discharged. *)
From PTree.Interp Require Import Iteration.
Section BehavioralIteration.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Context {E : Type -> Type} {I J A B : Type}.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Variable Hlimit : relational_lub NO.

Example direct_behavioral_iter_of_relational_lub
    (step1 : I -> ptree E M (I+A)) (step2 : J -> ptree E M (J+B))
    (SI : I -> J -> Prop) (RR : A -> B -> Prop) :
  (forall i j, SI i j -> @peutt E M M NI NC MX NO (I+A) (J+B)
    (pstruct_iter_sum_rel SI RR) (step1 i) (step2 j)) ->
  forall i j, SI i j -> @peutt E M M NI NC MX NO A B RR
    (PTree.iter step1 i) (PTree.iter step2 j).
Proof.
  apply (peutt_iter_eventful_rel (@mathcomp_relational_mixed_bind R)
    (@mathcomp_relational_zero R) Hlimit).
Qed.
End BehavioralIteration.
"""

@lru_cache(None)
def frozen(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT, text=True)

def check_new(sources):
    assert NEW <= set(sources), 'Incomplete iteration increment'
    assert sources[DIRECT] == frozen(DIRECT) + DIRECT_APPEND, 'Unapproved Gate M edit'
    for p in NEW:
        code = without_comments(sources[p])
        assert not re.search(r'\b(?:Axiom|Parameter|Admitted|admit|Abort|Class|Hint)\b|Unset .*Checking', code), p
        assert not re.search(r'#\[global\]|Global (?:Instance|Existing)', code), p
    core = without_comments(sources['theories/Interp/Iteration.v'])
    assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend|\bclassic\b|Classical', core)
    for token in ['iteration_protocol_iter', 'IterationEntry', 'IterationExit', 'IterationActive',
                  'handler_machine_hitting_sound', 'stable_hitting_rel', 'peutt_hitting_lift',
                  'iteration_protocol_related', 'peutt_iter_eventful_rel', 'peutt_iter_eventful']:
        assert token in core, token
    for token in ['no_event', 'iter_eventful_generator_closed', 'HandlerRelation', 'ITreeEutt']:
        assert token not in core, token
    thin = without_comments(sources['theories/Interp/FreeOmega/Iteration.v'])
    assert not re.search(r'\b(?:coinduction|induction|CoFixpoint|Inductive)\b', thin)
    reg = sources['theories/Regression/Semantics/EventfulIteration.v']
    for token in ['heterogeneous_eventful_iteration', 'sampled_eventful_iteration',
                  'partial_eventful_iteration', 'silent_endless_iteration',
                  'infinite_active_step', 'entry_candidate_excludes_residual',
                  'real_heterogeneous_iteration', 'high_eventful_iteration',
                  'Constraint Set < high', 'Fail Check PTree.Prob.Domain']:
        assert token in reg, token

def previous_sources(sources):
    from audit_iteration_algebra import previous_sources as before_algebra
    sources = before_algebra(sources)
    if not (NEW & set(sources)):
        return sources
    check_new(sources)
    result = {p: s for p, s in sources.items() if p not in NEW}
    result[DIRECT] = frozen(DIRECT)
    for line in IMPORTS:
        assert result[ALL].splitlines().count(line) == 1, 'Missing/duplicate import: ' + line
        result[ALL] = result[ALL].replace(line + '\n', '')
    return result

def check_source(sources):
    from audit_iteration_algebra import previous_sources as before_algebra
    sources = before_algebra(sources)
    old = {p for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
               cwd=ROOT, text=True).splitlines() if p.endswith('.v')}
    assert set(sources) == old | NEW, 'Unapproved theory addition/deletion'
    prior = previous_sources(sources)
    for p in old:
        assert prior[p] == frozen(p), 'Frozen theory changed: ' + p
    lines = sources[ALL].splitlines()
    assert lines[2:] == sorted(set(lines[2:])), 'Unsorted/duplicate aggregate'
    print(f'{len(old)} prior modules conserved, except exact aggregate and Gate M client additions.')

def query_direct_iteration():
    names = ['PTree.Regression.Backend.MathCompDirect.direct_behavioral_iter_of_relational_lub',
             'PTree.Interp.Iteration.peutt_iter_eventful_rel']
    commands = ['Local Unset Universe Checking.',
                'Require PTree.Regression.Backend.MathCompDirect.',
                'Set Printing Width 100.', 'Set Printing Depth 1000.', 'Set Printing Implicit.']
    for i, name in enumerate(names):
        for kind, command in [('TYPE', 'Check @' + name), ('AXIOMS', 'Print Assumptions ' + name), ('END', None)]:
            commands.append(f'Goal True. idtac "AUDIT_{kind}_{i}". Abort.')
            if command:
                commands.append(command + '.')
    result = subprocess.run(['opam', 'exec', '--', 'coqtop', '-quiet', '-R',
                             '_build/default/theories', 'PTree'], cwd=ROOT,
                            input='\n'.join(commands) + '\n', text=True, capture_output=True)
    return parse_direct(result, names)

def compiled_check():
    data = json.loads((ROOT/'docs/EVENTFUL_ITERATION_CONTRACTS.json').read_text())
    assert data['baseline'] == BASELINE
    actual = query([e['name'] for e in data['endpoints']])
    compare(data['endpoints'], actual)
    for item in actual:
        assert logical_axioms(item['assumptions']) <= SOUNDNESS_AXIOMS, item['name']
        if item['name'].startswith('PTree.Interp.Iteration.'):
            assert not re.search(r'FreeOmega|MathComp|SubEnum|OmegaVal|Backend', item['type'])
            assert logical_axioms(item['assumptions']) <= {'Eqdep.Eq_rect_eq.eq_rect_eq'}
        if item['name'].endswith('.peutt_iter_eventful_rel'):
            for forbidden in ['no_event', 'generator_closed', 'guarded_handler', 'Classical']:
                assert forbidden not in item['type'], forbidden
            for required in ['relational_lub', 'relational_mixed_bind', 'SemanticOmegaSelection',
                             'pstruct_iter_sum_rel', 'I1 -> I2 -> Prop', 'A -> B -> Prop']:
                assert required in item['type'], required
        if item['name'].endswith('.iteration_protocol_iter'):
            assert not logical_axioms(item['assumptions'])
    direct = query_direct_iteration()
    assert direct == data['direct'], 'Gate M endpoint or unsafe report drift'
    assert direct[0]['unsafe_hierarchy'] and direct[0]['session_collapsed_universes']
    assert not direct[1]['unsafe_hierarchy'], 'Safe generic theorem acquired an unsafe flag'
    for required in ['MathCompCouplingGluing', 'relational_lub']:
        assert required in direct[0]['type'], required
    print(f'{len(actual)} safe iteration contracts, no generic classic; conditional Gate M client separately flagged.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    check_source({p.relative_to(ROOT).as_posix(): p.read_text() for p in (ROOT/'theories').rglob('*.v')})
    if args.compiled:
        compiled_check()
