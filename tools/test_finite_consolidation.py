import unittest
from audit_finite_consolidation import native_boundary, compare_contracts, source_check


class FiniteConsolidationTests(unittest.TestCase):
    def test_current_source_boundary(self):
        source_check()

    def test_no_legacy_bridge_in_native_code(self):
        for bad in ['Check nnQ.', 'Check nnQ_0.', 'Check Build_nnQ.',
                    'Check Qval.', 'Check rational_unshare.',
                    'From PTree.Prob.Legacy Require Import RatSubTypes.']:
            with self.subTest(bad=bad), self.assertRaises(AssertionError):
                native_boundary(bad)
        native_boundary('Definition EnumQ A := FiniteEnum rat A.')

    def test_only_owner_names_and_definitional_rat_printing_change(self):
        old = [dict(name='M.t', type='forall A, Measure.SubEnumQ A -> rat.rat',
                    assumptions='Closed under the global context')]
        new = [dict(name='M.t', type='forall A, Representation.SubEnumQ A -> '
                    'ssrnum.Num.NumDomain.sort rat.rat_rat__canonical__Num_NumDomain',
                    assumptions='Closed under the global context')]
        compare_contracts(old, new)
        for bad in ['False -> ' + new[0]['type'], new[0]['type'] + ' -> True']:
            with self.assertRaises(AssertionError):
                compare_contracts(old, [{**new[0], 'type': bad}])
        with self.assertRaises(AssertionError):
            compare_contracts(old, [{**new[0], 'assumptions': 'Axioms:\nnew_axiom : False'}])
        with self.assertRaises(AssertionError):
            compare_contracts(old, [])
        with self.assertRaises(AssertionError):
            compare_contracts([{**old[0], 'assumptions': 'Axioms:\nknown : True'}],
                              [{**new[0], 'assumptions': 'Axioms:\nknown : False'}])


if __name__ == '__main__':
    unittest.main()
