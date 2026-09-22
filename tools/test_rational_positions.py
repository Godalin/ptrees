"""The first production indexing extraction must not change its semantics."""
import copy
import unittest

import audit_rational_positions as audit


class RationalPositionsTests(unittest.TestCase):
    def test_exact_client_adaptation(self):
        old = audit.frozen(audit.CLIENT).decode()
        audit.client_check(old, (audit.ROOT / audit.CLIENT).read_text())

    def test_relation_change_is_not_in_migration(self):
        old = audit.frozen(audit.CLIENT).decode()
        expected = audit.adapted(old)
        changed = expected.replace('coupling (at_index R mu nu)', 'coupling (fun _ _ => True)')
        with self.assertRaises(AssertionError):
            audit.client_check(old, changed)
        changed = expected.replace('enumQ_eq_eq. exact: emap_fst_value_index_joint_from.',
                                   'enumQ_eq_eq. admit.')
        with self.assertRaises(AssertionError):
            audit.client_check(old, changed)

    def test_common_has_no_backend_semantics(self):
        source = (audit.ROOT / audit.COMMON).read_text()
        audit.common_boundary(source)
        for extra in ['Axiom transport : False.', 'Class Capability := {}.',
                      'Check nnQ.', 'Check SemanticMeasure.', 'Check FreeOmega.',
                      'Local Unset Universe Checking.',
                      'From PTree.Prob.Backend.EnumQ Require Import Representation.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.common_boundary(source + '\n' + extra)

    def test_baseline_namespace_is_only_print_change(self):
        old = [{'name': 'M.t', 'type': '@Phase4bBaseline.t : forall X, X -> X',
                'assumptions': 'Closed under the global context'}]
        new = copy.deepcopy(old)
        new[0]['type'] = '@IndexedCoupling.IndexedCoupling.t :\n forall X, X -> X'
        audit.compare(old, new)

    def test_compiled_premise_or_assumption_change_rejected(self):
        old = [{'name': 'M.t', 'type': 't : forall X, X -> X',
                'assumptions': 'Closed under the global context'}]
        for key, value in [('type', 't : False -> forall X, X -> X'),
                           ('assumptions', 'Axioms:\nnew_axiom : False'),
                           ('name', 'M.other')]:
            bad = copy.deepcopy(old); bad[0][key] = value
            with self.subTest(key=key), self.assertRaises(AssertionError):
                audit.compare(old, bad)
        with self.assertRaises(AssertionError):
            audit.compare(old, [])


if __name__ == '__main__':
    unittest.main()
