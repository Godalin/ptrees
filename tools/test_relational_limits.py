"""No theorem-as-axiom, no missing monotonicity, no validation back edge."""
import unittest
from audit_assumptions import ROOT
from audit_relational_limits import check_source, ALL
from audit_architecture import permitted, external_validation


class RelationalLimitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT / 'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_additive_only(self):
        check_source(self.sources)

    def test_frozen_foundations(self):
        for p in ['Prob/Interface/Omega', 'Prob/FreeOmega/Quotient', 'Eq/Canonical',
                  'Eq/FreeOmega/Relation', 'Eq/Backend/MathComp/Direct']:
            with self.subTest(path=p):
                self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_realization_axiom_or_class(self):
        for text in ['Axiom realization : True.', 'Class RelationalOmegaLaws := {}.',
                     'Local Unset Universe Checking.', 'Admitted.']:
            with self.subTest(text=text):
                self.reject('theories/Prob/Backend/Common/CountableRelationalLimit.v', lambda s: s + text)

    def test_joint_chain_is_not_inferred_from_marginals(self):
        self.reject('theories/Prob/Interface/RelationalLimit.v',
                    lambda s: s.replace('sem_increasing joints', 'True'))

    def test_no_assumed_countable_transport(self):
        self.reject('theories/Prob/Backend/Common/CountableRelationalLimit.v',
                    lambda s: s.replace('oval_bidual_coupled', 'supplied_transport'))

    def test_countable_scope_is_not_silently_dropped(self):
        self.reject('theories/Prob/Backend/Common/CountableRelationalLimit.v',
                    lambda s: s.replace('(forall n, oval_countably_supported (c n))', 'True'))

    def test_allimports_coverage(self):
        self.reject(ALL, lambda s: s.replace('Require PTree.Prob.Domain.RelationalLimit.\n', ''))

    def test_external_joint_limit_not_mainline_capability(self):
        target = 'Prob/Backend/Common/CountableRelationalLimit'
        self.assertTrue(external_validation(target))
        for owner in ['Eq/PEutt', 'Eq/FreeOmega/Relation', 'Prob/Backend/MathComp/OmegaLaws']:
            self.assertFalse(permitted(owner, target))
        self.assertTrue(permitted('Regression/Probability/RelationalLimit', target))
        self.assertTrue(permitted('Eq/PEutt', 'Prob/Interface/RelationalLimit'))


if __name__ == '__main__':
    unittest.main()
