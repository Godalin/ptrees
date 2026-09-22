import unittest
from audit_finite_support import adapted, frozen, CLIENT


class SupportConservation(unittest.TestCase):
    def test_only_one_proof(self):
        old = frozen(CLIENT)
        new = adapted(old)
        self.assertEqual(new.count('exact: finite_expect_entry_le.'), 1)
        self.assertIn('Theorem subenumR_lift_bind', new)

    def test_missing_anchor_rejected(self):
        with self.assertRaises(AssertionError):
            adapted('Lemma unrelated : True. Proof. exact I. Qed.')

    def test_duplicate_proof_rejected(self):
        old = frozen(CLIENT)
        with self.assertRaises(AssertionError):
            adapted(old + '\nLemma real_enum_expect_entry_le : True.\nProof. exact I. Qed.')


if __name__ == '__main__':
    unittest.main()
