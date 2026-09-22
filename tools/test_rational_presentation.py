"""The presentation extraction must preserve exact lists and native contracts."""
import copy
import unittest
import audit_rational_presentation as audit


class RationalPresentationTests(unittest.TestCase):
    def test_exact_client(self):
        audit.client_check(audit.frozen(audit.CLIENT).decode(), (audit.ROOT / audit.CLIENT).read_text())

    def test_semantic_change_rejected(self):
        old = audit.frozen(audit.CLIENT).decode()
        expected = audit.adapted(old)
        for a, b in [('  finite_positions mu.', '  finite_positions (enumQ_prune mu).'),
                     ('Proof. exact: finite_positions_decode. Qed.', 'Proof. admit. Qed.'),
                     ('(fun x y => decode x = y)', '(fun x y => True)')]:
            changed = expected.replace(a, b)
            self.assertNotEqual(changed, expected)
            with self.assertRaises(AssertionError):
                audit.client_check(old, changed)

    def test_no_backend_in_common(self):
        source = (audit.ROOT / audit.COMMON).read_text()
        audit.common_boundary(source)
        for extra in ['Axiom transport : False.', 'Class Capability := {}.', 'Check nnQ.',
                      'Check SemanticMeasure.', 'Check FreeOmega.', 'Local Unset Universe Checking.',
                      'From PTree.Prob.Backend.EnumQ Require Import Representation.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.common_boundary(source + '\n' + extra)

    def test_only_namespace_and_whitespace_normalized(self):
        old = [{'name': 'M.t', 'type': '@Phase4bPresentationBaseline.t : forall A, A -> A',
                'assumptions': 'Closed under the global context'}]
        new = copy.deepcopy(old); new[0]['type'] = '@FinitePresentation.t :\n forall A, A -> A'
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
