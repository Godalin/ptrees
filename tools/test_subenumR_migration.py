"""Phase 3 permits only the shared real carrier, never stronger contracts."""
import copy
import subprocess
import unittest
from unittest.mock import patch
import audit_subenumR_migration as audit


class RealMigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = audit.frozen(audit.REPRESENTATION).decode()
        cls.new = (audit.ROOT / audit.REPRESENTATION).read_text()

    def test_actual_shared_representation(self):
        audit.representation_check(self.old, self.new)

    def test_no_independent_record_or_recursive_arithmetic(self):
        for extra in ['Record Other := {}.', 'Fixpoint second := 0.', 'Class C := {}.',
                      'Axiom shortcut : False.', 'Check Build_SubEnumR.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.representation_check(self.old, self.new + '\n' + extra)

    def test_shared_operations_mandatory(self):
        for before, after in [(':= FiniteSubdist R A.', ':= list (R * A).'),
                              ('finite_subdist_bind mu k.', 'mu.'),
                              ('finite_enum_raw (finite_subdist_enum mu).', 'nil.')]:
            with self.subTest(before=before), self.assertRaises(AssertionError):
                audit.representation_check(self.old, self.new.replace(before, after))

    def test_native_relational_meaning_unchanged(self):
        with self.assertRaises(AssertionError):
            audit.representation_check(self.old, self.new.replace(
                'subenumR_ae j (fun xy => S (fst xy) (snd xy)).', 'True.'))

    def test_theorem_premise_cannot_be_added(self):
        with self.assertRaises(AssertionError):
            audit.representation_check(self.old, self.new.replace(
                'real_enum_expect (fun _ => 0) mu = 0.', 'False -> real_enum_expect (fun _ => 0) mu = 0.'))

    def test_client_adaptations_are_exact(self):
        for path in audit.ADAPTATIONS:
            old = audit.frozen(path).decode()
            accepted = subprocess.check_output(['git', 'show', '683d3c7:' + path],
                                                cwd=audit.ROOT, text=True)
            self.assertEqual(audit.adapted(path, old), accepted)

    def test_types_and_assumptions_fail_closed(self):
        old = [{'name': 'M.t', 'type': 't : forall X, X -> X',
                'assumptions': 'Closed under the global context'}]
        audit.compare_contracts(old, old)
        for key, value in [('type', 't : False -> forall X, X -> X'),
                           ('assumptions', 'Axioms:\nnew_axiom : False'), ('name', 'M.other')]:
            bad = copy.deepcopy(old); bad[0][key] = value
            with self.subTest(key=key), self.assertRaises(AssertionError):
                audit.compare_contracts(old, bad)
        with self.assertRaises(AssertionError):
            audit.compare_contracts(old, [])

    def test_existing_behavioral_choice_is_not_reinterpreted(self):
        old = [{'name': 'M.t', 'type': 't : True',
                'assumptions': 'Axioms:\nRelationalChoice.relational_choice : True'}]
        audit.compare_contracts(old, old)
        bad = copy.deepcopy(old)
        bad[0]['assumptions'] = 'Axioms:\nRelationalChoice.relational_choice : False'
        with self.assertRaises(AssertionError):
            audit.compare_contracts(old, bad)

    def test_baseline_cannot_be_recaptured_after_migration(self):
        with patch.object(audit, 'frozen_files', return_value=[audit.REPRESENTATION]), \
             patch.object(audit, 'query') as query:
            with self.assertRaises(AssertionError):
                audit.capture_baseline()
            query.assert_not_called()


if __name__ == '__main__':
    unittest.main()
