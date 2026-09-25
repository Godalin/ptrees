"""Law consumers, exact scope, and the distinction from full uniformity."""
import unittest
from audit_assumptions import ROOT
from audit_iteration_algebra import ALL, DIRECT, NEW, check_source, previous_sources, frozen
from audit_architecture import permitted


class IterationAlgebraTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_current_increment(self):
        check_source(self.sources)

    def test_exact_prior(self):
        prior = previous_sources(self.sources)
        for path in [ALL, DIRECT]:
            self.assertEqual(prior[path], frozen(path))

    def test_frozen_definitions_and_law_interfaces(self):
        for path in ['Core/PTreeDefinition', 'Core/IterationLaws', 'Eq/PEutt',
                     'Eq/Canonical', 'Interp/Iteration', 'Interp/StateFoldFacts',
                     'Interp/WriterFoldITree', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + path + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_capability_or_global_routing(self):
        for path in NEW:
            for text in ['Axiom magic : True.', 'Admitted.', 'Class Magic := {}.',
                         'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(path, lambda s, text=text: s + '\n' + text + '\n')

    def test_generic_proof_reuses_existing_theorems(self):
        for token in ['peutt_iter_eventful_rel', 'pstruct_return_map', 'ptree_peutt_iter_finite_stutter']:
            self.reject('theories/Interp/IterationAlgebra.v', lambda s, token=token: s.replace(token, 'removed'))
        self.reject('theories/Interp/IterationAlgebra.v', lambda s: s + '\nCheck FreeOmega.\n')

    def test_explicit_interface_boundary_preserved(self):
        self.reject('theories/Regression/Semantics/PTreeIterationAlgebra.v',
                    lambda s: s.replace('Fail Definition protocol_uniformity_package', 'Definition protocol_uniformity_package'))
        self.reject('theories/Interp/IterationAlgebra.v',
                    lambda s: s + '\nTheorem ptree_peutt_iteration_uniform : True. Proof. exact I. Qed.\n')

    def test_real_consumers_and_large_carrier(self):
        for token in ['actual_monad_rewriting', 'reader_inherits_monad', 'writer_inherits_monad',
                      'exception_inherits_monad', 'real_lawful_iteration', 'Constraint Set < high']:
            self.reject('theories/Regression/Semantics/PTreeIterationAlgebra.v',
                        lambda s, token=token: s.replace(token, 'removed'))

    def test_completion_is_thin(self):
        self.reject('theories/Interp/FreeOmega/IterationAlgebra.v',
                    lambda s: s + '\nCheck induction.\n')

    def test_gate_m_unchanged_scope(self):
        self.reject(DIRECT, lambda s: s.replace('Variable Hlimit : relational_lub NO.', ''))
        self.assertFalse(permitted('Interp/IterationAlgebra', 'Eq/Backend/MathComp/Direct'))
        self.assertFalse(permitted('Eq/Iter', 'Interp/IterationAlgebra'))

    def test_sorted_unique_aggregate(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Interp.IterationAlgebra.\n')


if __name__ == '__main__':
    unittest.main()
