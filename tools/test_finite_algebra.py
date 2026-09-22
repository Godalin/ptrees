import unittest
from audit_finite_algebra import replay, common_boundary


class FiniteAlgebraTests(unittest.TestCase):
    def test_exact_replay(self):
        self.assertEqual(replay('a\nb\nc\n', [dict(start=1, old='b\n', new='x\ny\n')]), 'a\nx\ny\nc\n')

    def test_bad_anchor_rejected(self):
        with self.assertRaises(AssertionError):
            replay('a\nb\n', [dict(start=1, old='wrong\n', new='x\n')])

    def test_overlap_rejected(self):
        with self.assertRaises(AssertionError):
            replay('a\nb\n', [dict(start=0, old='a\nb\n', new='x\n'), dict(start=1, old='b\n', new='y\n')])

    def test_common_is_not_backend(self):
        for bad in ['Class Transport := {}.', 'Axiom witness : True.',
                    'Definition x := nnQ.', 'Local Unset Universe Checking.',
                    'From PTree.Prob.Backend.EnumQ Require Import Representation.']:
            with self.subTest(source=bad), self.assertRaises(AssertionError):
                common_boundary(bad)

    def test_explicit_scalar_function_allowed(self):
        common_boundary('Context {W : Type} (mul : W -> W -> W).')


if __name__ == '__main__':
    unittest.main()
