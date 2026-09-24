"""Keep interpreted algebra generic, lawful, and honest about missing mass."""
import unittest
from audit_assumptions import ROOT
from audit_effect_algebra import ALL, NEW, check_source, previous_sources, frozen


class EffectAlgebraTests(unittest.TestCase):
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

    def test_no_new_assumptions(self):
        for p in NEW:
            for suffix in ['Axiom magic : True.', 'Admitted.', 'Class EffectLaw := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_interpreters_and_old_theorems_frozen(self):
        for p in ['Interp/Writer', 'Interp/State', 'Interp/StateFoldFacts',
                  'Interp/ITreeFacts', 'Eq/PEutt', 'Eq/Canonical', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_writer_laws_and_order_required(self):
        p = 'theories/Interp/Algebra/Writer.v'
        for token in ['MonoidLaws W op', 'monoid_plus op log w']:
            self.reject(p, lambda s, token=token: s.replace(token, 'missing'))
        self.reject(p, lambda s: s + '\nCheck Commutative.\n')

    def test_boundary_is_semantic_not_just_execution(self):
        p = 'theories/Regression/Semantics/EffectAlgebra.v'
        for token in ['free_omega_qlift_upper_mass', 'sampling_before_throw_not_erasable']:
            self.reject(p, lambda s, token=token: s.replace(token, 'missing'))

    def test_uniformity_not_bare_monaditer(self):
        self.reject('theories/Examples/EffectInteractions.v',
                    lambda s: s.replace('iteration_uniform', 'True'))

    def test_aggregate_unique(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Interp.Algebra.Writer.\n')


if __name__ == '__main__':
    unittest.main()
