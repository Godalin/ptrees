"""Pruning extraction must not change rational equality or lifting contracts."""
import copy
import unittest
import audit_rational_pruning as audit


class RationalPruningTests(unittest.TestCase):
    def test_exact_client(self):
        audit.client_check(audit.frozen(audit.CLIENT).decode(), (audit.ROOT / audit.CLIENT).read_text())

    def test_no_semantic_or_proof_drift(self):
        old = audit.frozen(audit.CLIENT).decode()
        expected = audit.adapted(old)
        for a, b in [('indexed_coupling eq (enumQ_prune mu) (enumQ_prune nu)', 'True'),
                     ('Proof. exact: finite_prune_app. Qed.', 'Proof. admit. Qed.'),
                     ('p <> PTree.Prob.Backend.Common.RatSubTypes.nnQ_0', 'True')]:
            changed = expected.replace(a, b)
            self.assertNotEqual(changed, expected)
            with self.assertRaises(AssertionError):
                audit.client_check(old, changed)

    def test_common_boundary(self):
        source = (audit.ROOT / audit.COMMON).read_text()
        audit.common_boundary(source)
        for extra in ['Axiom transport : False.', 'Class Capability := {}.', 'Check nnQ.',
                      'Check SemanticMeasure.', 'Check FreeOmega.', 'Local Unset Universe Checking.',
                      'From PTree.Prob.Backend.EnumQ Require Import Representation.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.common_boundary(source + '\n' + extra)

    def test_only_historical_namespace_and_whitespace_normalized(self):
        old = [{'name': 'M.t', 'type': '@Phase4bPruneBaseline.t : forall A, A -> A',
                'assumptions': 'Closed under the global context'}]
        new = copy.deepcopy(old)
        new[0]['type'] = '@FrontierLift.t :\n forall A, A -> A'
        audit.compare(old, new)
        for key, value in [('name', 'M.other'), ('type', 't : False -> forall A, A -> A'),
                           ('assumptions', 'Axioms:\nnew_axiom : False')]:
            bad = copy.deepcopy(new); bad[0][key] = value
            with self.subTest(key=key), self.assertRaises(AssertionError):
                audit.compare(old, bad)
        with self.assertRaises(AssertionError):
            audit.compare(old, [])


if __name__ == '__main__':
    unittest.main()
