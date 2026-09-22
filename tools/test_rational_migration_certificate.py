"""Keep the pre-migration certificate separate from the actual carrier switch."""
import copy
import json
import unittest

import audit_rational_migration_certificate as audit


class RationalMigrationCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (audit.ROOT / audit.CERTIFICATE).read_text()

    def test_certificate_boundary(self):
        audit.boundary(self.source)

    def test_unsafe_or_new_assumptions_rejected(self):
        for extra in ['Axiom shortcut : False.', 'Admitted.', 'Class C := {}.',
                      'Local Unset Universe Checking.', 'Local Unset Guard Checking.',
                      'Require Import ProofIrrelevance.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.boundary(self.source + '\n' + extra)

    def test_no_compatibility_coercion_or_instance(self):
        for extra in ['Coercion convert : Old >-> New.', 'Instance compat := tt.',
                      'Canonical compat := tt.']:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                audit.boundary(self.source + '\n' + extra)

    def test_missing_obligation_rejected(self):
        with self.assertRaises(AssertionError):
            audit.boundary(self.source.replace('Theorem rational_shared_index',
                                                'Theorem renamed_missing_index'))

    def test_old_backend_and_snapshot_must_not_change(self):
        for path in ['theories/Prob/Backend/EnumQ/Representation.v', 'docs/CONTRACTS.json']:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                audit.preserved(path, b'original', b'modified', self.source)

    def test_exact_sorted_unique_import(self):
        old = b'Require PTree.A.\nRequire PTree.Z.\n'
        new = audit.aggregate(old)
        audit.preserved(audit.AGGREGATE, old, new, self.source)
        lines = new.splitlines()
        self.assertEqual(lines, sorted(set(lines)))
        with self.assertRaises(AssertionError):
            audit.preserved(audit.AGGREGATE, old, new + b'Require PTree.Z.\n', self.source)

    def test_no_old_policy_refresh_or_missing_tests(self):
        old = {'regressions': {'old.v': ['old_contract']}, 'other': 'frozen'}
        good = copy.deepcopy(old)
        good['regressions'][audit.CERTIFICATE] = audit.declarations(self.source)
        audit.preserved(audit.POLICY, json.dumps(old), json.dumps(good), self.source)
        bad = copy.deepcopy(good)
        bad['other'] = 'changed'
        with self.assertRaises(AssertionError):
            audit.preserved(audit.POLICY, json.dumps(old), json.dumps(bad), self.source)
        good['regressions'][audit.CERTIFICATE].pop()
        with self.assertRaises(AssertionError):
            audit.preserved(audit.POLICY, json.dumps(old), json.dumps(good), self.source)


if __name__ == '__main__':
    unittest.main()
