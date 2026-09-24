"""The bridge must consume real ITrees, preserve old theory, and not add axioms."""
import unittest
from audit_assumptions import ROOT
from audit_itree_bridge import ALL, NEW, check_source, previous_sources, frozen


class ITreeBridgeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, p, transform):
        changed = dict(self.sources)
        changed[p] = transform(changed[p])
        with self.assertRaises(AssertionError):
            check_source(changed)

    def test_current_increment(self):
        check_source(self.sources)

    def test_prior_exact(self):
        prior = previous_sources(self.sources)
        self.assertEqual(prior[ALL], frozen(ALL))

    def test_no_new_assumptions_or_search(self):
        for p in NEW:
            for suffix in ['Axiom oracle : True.', 'Admitted.', 'Class NewLaw := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_old_semantics_immutable(self):
        for p in ['Core/PTreeDefinition', 'Eq/PEutt', 'Eq/Canonical', 'Interp/HandlerRelation',
                  'Prob/FreeOmega/Quotient', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_actual_itree_and_native_prob(self):
        for token in ['(t : itree E A)', 'Prob mu']:
            self.reject('theories/Core/ITreeBridge.v', lambda s, token=token: s.replace(token, 'missing'))

    def test_generic_theory_and_thin_specialization(self):
        self.reject('theories/Interp/ITreeFacts.v', lambda s: s + '\nCheck FreeOmega.\n')
        self.reject('theories/Interp/FreeOmega/ITreeCompletion.v', lambda s: s + '\ncoinduction.\n')

    def test_aggregate_unique(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Core.ITreeBridge.\n')


if __name__ == '__main__':
    unittest.main()
