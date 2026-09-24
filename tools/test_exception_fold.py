"""Exception transformer laws do not change the underlying probability theory."""
import unittest
from audit_assumptions import ROOT
from audit_exception_fold import ALL, NEW, check_source, previous_sources, frozen


class ExceptionFoldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, p, f):
        changed = dict(self.sources)
        changed[p] = f(changed[p])
        with self.assertRaises(AssertionError):
            check_source(changed)

    def test_current_increment(self):
        check_source(self.sources)

    def test_exact_prior(self):
        self.assertEqual(previous_sources(self.sources)[ALL], frozen(ALL))

    def test_no_assumptions_or_global_instances(self):
        for p in NEW:
            for suffix in ['Axiom magic : True.', 'Admitted.', 'Class EffectLaw := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_uniformity_explicit(self):
        for p in ['theories/Core/ExceptT.v', 'theories/Interp/ExceptionFoldFacts.v']:
            self.reject(p, lambda s: s.replace('(Hunif : @iteration_uniform T MT IT QT)', '(Hunif : True)'))

    def test_existing_transformer_used(self):
        self.reject('theories/Core/ExceptT.v', lambda s: s.replace('@MonadIter_eitherT', '@invented_iterator'))

    def test_old_interpreters_frozen(self):
        for p in ['Interp/Exception', 'Interp/StateFoldFacts', 'Core/IterationLaws', 'Eq/PEutt']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_sampling_not_erased(self):
        self.reject('theories/Regression/Semantics/ExceptionFold.v',
                    lambda s: s.replace('sample_then_exception', 'missing'))

    def test_aggregate_unique(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Core.ExceptT.\n')


if __name__ == '__main__':
    unittest.main()
