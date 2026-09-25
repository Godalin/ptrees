"""Direct-machine proof route, old-boundary preservation, and full-interface consumers."""
import unittest
from audit_assumptions import ROOT
from audit_direct_iteration import ALL, DIRECT, NEW, check_source, previous_sources, frozen
from audit_architecture import permitted


class DirectIterationTests(unittest.TestCase):
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

    def test_no_foundational_or_old_proof_changes(self):
        for path in ['Core/PTreeDefinition', 'Core/IterationLaws', 'Eq/PEutt', 'Eq/Canonical',
                     'Interp/Iteration', 'Interp/IterationAlgebra', 'Interp/StateFoldFacts',
                     'Interp/ExceptionFoldFacts', 'Regression/Semantics/PTreeIterationAlgebra']:
            self.reject('theories/' + path + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_axiom_capability_or_global_search(self):
        for path in NEW:
            for text in ['Axiom magic : True.', 'Admitted.', 'Class Magic := {}.',
                         'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(path, lambda s, text=text: s + '\n' + text + '\n')

    def test_no_protocol_or_backend_in_new_route(self):
        for module in ['IterationMachine', 'IterationUniform']:
            for text in ['iteration_protocol', 'iteration_handler', 'peutt_iter_eventful_rel', 'FreeOmega', 'classic']:
                self.reject('theories/Interp/' + module + '.v',
                            lambda s, text=text: s + '\nCheck ' + text + '.\n')

    def test_adequacy_requires_both_directions(self):
        for token in ['iter_primitive_tree', 'iter_phase_grid_le_primitive',
                      'iter_primitive_le_phase_grid', 'sem_lub_double_diagonal']:
            self.reject('theories/Interp/IterationMachine.v', lambda s, token=token: s.replace(token, 'removed'))

    def test_full_interface_and_actual_consumers(self):
        self.reject('theories/Interp/IterationUniform.v', lambda s: s.replace('@iteration_uniform', '@small_uniform'))
        for token in ['fold_run_state', 'fold_run_exception', 'tree_state_uniformity',
                      'writer_inherits_full_uniformity', 'real_full_uniformity', 'Constraint Set < high']:
            self.reject('theories/Regression/Semantics/PTreeUniformity.v',
                        lambda s, token=token: s.replace(token, 'removed'))

    def test_completion_is_thin(self):
        self.reject('theories/Interp/FreeOmega/IterationUniform.v', lambda s: s + '\nCheck induction.\n')

    def test_gate_m_exact_and_isolated(self):
        self.reject(DIRECT, lambda s: s.replace('Variable Hlimit : relational_lub NO.', ''))
        self.assertFalse(permitted('Interp/IterationUniform', 'Eq/Backend/MathComp/Direct'))
        self.assertFalse(permitted('Eq/Iter', 'Interp/IterationUniform'))

    def test_sorted_unique_aggregate(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Interp.IterationMachine.\n')


if __name__ == '__main__':
    unittest.main()
