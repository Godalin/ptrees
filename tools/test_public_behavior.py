"""Public facade changes must not silently change raw theory or proof imports."""
import unittest
from audit_assumptions import ROOT
from audit_public_behavior import (PEUTT, GENERIC, FREEOMEGA, CLIENT,
                                   historical, production_check, client_check)


class PublicBehaviorTests(unittest.TestCase):
    def test_only_reviewed_production_edits(self):
        for path in [PEUTT, GENERIC, FREEOMEGA]:
            old, new = historical(path), (ROOT/path).read_text()
            production_check(path, old, new)
            with self.subTest(path=path), self.assertRaises(AssertionError):
                production_check(path, old, new + '\nLemma extra : True. Proof. exact I. Qed.\n')

    def test_raw_notation_cannot_return(self):
        path = PEUTT
        with self.assertRaises(AssertionError):
            production_check(path, historical(path), (ROOT/path).read_text() +
                             '\nNotation "t ≈ₚ u" := (peutt eq t u) (at level 70) : type_scope.\n')

    def test_glyph_cannot_route_only_by_carrier(self):
        path = GENERIC
        with self.assertRaises(AssertionError):
            production_check(path, historical(path), (ROOT/path).read_text().replace('Behavior.canonical_peutt', 'peutt'))

    def test_bind_cannot_regress_to_explicit_cofinality(self):
        path = FREEOMEGA
        with self.assertRaises(AssertionError):
            production_check(path, historical(path), (ROOT/path).read_text().replace(':= Bind.peutt_bind.', ':= PEutt.peutt_bind.'))

    def test_consumer_has_no_hidden_implementation_imports(self):
        source = (ROOT/CLIENT).read_text()
        client_check(source)
        for extra in ['From PTree.Eq.FreeOmega Require Import Bind.',
                      'Require Import PTree.Eq.FreeOmega.Bind.',
                      '#[local] Existing Instance foo.',
                      'Arguments foo {RR}.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                client_check(source + '\n' + extra + '\n')


if __name__ == '__main__':
    unittest.main()
