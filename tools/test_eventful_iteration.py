"""Iteration scope, immutable dependencies and the existing Gate M boundary."""
import unittest
from audit_assumptions import ROOT
from audit_eventful_iteration import ALL, DIRECT, NEW, check_source, previous_sources, frozen
from audit_architecture import permitted


class EventfulIterationTests(unittest.TestCase):
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

    def test_frozen_semantics(self):
        for path in ['Eq/PEutt', 'Eq/Iter', 'Interp/HandlerMachine',
                     'Interp/HandlerMachineAcceleration', 'Core/PTreeDefinition',
                     'Eq/Canonical', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + path + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_capability_axiom_or_global_search(self):
        for path in NEW:
            for text in ['Axiom magic : True.', 'Admitted.', 'Class Magic := {}.',
                         'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(path, lambda s, text=text: s + '\n' + text + '\n')

    def test_no_old_closure_or_no_event_premise(self):
        for text in ['no_event', 'iter_eventful_generator_closed', 'classic', 'ITreeEutt']:
            self.reject('theories/Interp/Iteration.v', lambda s, text=text: s + '\nCheck ' + text + '.\n')

    def test_machine_has_residual_phase_and_reuses_adequacy(self):
        for token in ['IterationActive', 'handler_machine_hitting_sound', 'stable_hitting_rel']:
            self.reject('theories/Interp/Iteration.v', lambda s, token=token: s.replace(token, 'removed'))

    def test_thin_completion_and_generic_owner(self):
        self.reject('theories/Interp/FreeOmega/Iteration.v', lambda s: s + '\nCheck coinduction.\n')
        self.reject('theories/Interp/Iteration.v', lambda s: s + '\nCheck FreeOmega.\n')
        self.assertFalse(permitted('Eq/Iter', 'Interp/Iteration'))
        self.assertTrue(permitted('Interp/Iteration', 'Interp/HandlerMachineAcceleration'))

    def test_gate_m_append_is_exact(self):
        self.reject(DIRECT, lambda s: s.replace('Variable Hlimit : relational_lub NO.', ''))
        self.reject(DIRECT, lambda s: s + '\nLocal Unset Universe Checking.\n')

    def test_regression_boundaries(self):
        for token in ['heterogeneous_eventful_iteration', 'infinite_active_step',
                      'partial_eventful_iteration', 'Constraint Set < high']:
            self.reject('theories/Regression/Semantics/EventfulIteration.v',
                        lambda s, token=token: s.replace(token, 'removed'))

    def test_sorted_unique_aggregate(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Interp.Iteration.\n')


if __name__ == '__main__':
    unittest.main()
