"""Source relation entry, genuine interpreter square, and trust boundaries."""
import unittest
from audit_assumptions import ROOT
from audit_itree_preservation import ALL, NEW, check_source, previous_sources, frozen


class ITreePreservationTests(unittest.TestCase):
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

    def test_no_new_axioms_search_or_bypass(self):
        for p in NEW:
            for suffix in ['Axiom magic : True.', 'Admitted.', 'Class WeakLaw := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_embedding_is_independent_of_native_lub(self):
        self.reject('theories/Interp/ITreeEutt.v', lambda s: s + '\nCheck relational_lub.\n')
        self.reject('theories/Interp/ITreeEutt.v', lambda s: s.replace('eutt RR t u', 'True'))
        self.reject('theories/Interp/ITreeEutt.v', lambda s: s.replace('classic', 'hidden_split'))

    def test_real_source_square_and_no_guard(self):
        self.reject('theories/Interp/ITreeSourceInterp.v',
                    lambda s: s.replace('Interp.interp h t', 't'))
        self.reject('theories/Interp/ITreePreservation.v',
                    lambda s: s + '\nCheck guarded_handler.\n')

    def test_frozen_definitions_and_gate_m(self):
        for p in ['Core/ITreeBridge', 'Core/PTreeDefinition', 'Eq/PEutt',
                  'Interp/Unrestricted', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_backend_ownership(self):
        self.reject('theories/Interp/ITreePreservation.v',
                    lambda s: s + '\nCheck FreeOmega.\n')

    def test_required_regression_boundaries(self):
        for token in ['divergence_has_no_head', 'embedded_heterogeneous_return',
                      'real_lowering_eutt', 'Constraint Set < high']:
            self.reject('theories/Regression/Semantics/ITreePreservation.v',
                        lambda s, token=token: s.replace(token, 'removed'))

    def test_aggregate_unique(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Interp.ITreeEutt.\n')


if __name__ == '__main__':
    unittest.main()
