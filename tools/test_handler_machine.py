"""Guard the non-circular handler proof and unchanged backend/trust boundary."""
import unittest
from audit_assumptions import ROOT
from audit_handler_machine import ALL, NEW, check_source


class HandlerMachineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_additive_proof(self):
        check_source(self.sources)

    def test_existing_definitions_and_guarded_route_frozen(self):
        for p in ['Eq/PEutt', 'Interp/Preservation', 'Interp/Guarded', 'Interp/State',
                  'Prob/FreeOmega/Quotient', 'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_axiom_capability_or_checker_bypass(self):
        for text in ['Class InterpPreservation := {}.', 'Axiom fusion : True.', 'Admitted.',
                     'Local Unset Universe Checking.', '#[global] Instance surprise : True := I.']:
            self.reject('theories/Interp/Unrestricted.v', lambda s: s + '\n' + text)

    def test_no_backend_specific_generic_proof(self):
        self.reject('theories/Interp/HandlerMachine.v', lambda s: s + '\nCheck FreeOmega.\n')

    def test_finite_and_complete_schedule_are_both_required(self):
        for name in ['sem_lub_double_diagonal', 'handler_phase_grid_le_primitive',
                     'handler_primitive_le_phase_grid']:
            self.reject('theories/Interp/HandlerMachineAcceleration.v',
                        lambda s: s.replace(name, 'unreviewed_replacement'))

    def test_adequacy_cannot_be_skipped(self):
        self.reject('theories/Interp/Unrestricted.v',
                    lambda s: s.replace('handler_machine_hitting_sound', 'assumed_adequacy'))

    def test_no_hidden_target_preservation_premise(self):
        self.reject('theories/Interp/Unrestricted.v', lambda s: s + '\nVariable Htarget : True.\n')

    def test_no_missing_or_duplicate_import(self):
        line = 'Require PTree.Interp.Unrestricted.\n'
        self.reject(ALL, lambda s: s.replace(line, ''))
        self.reject(ALL, lambda s: s + line)

    def test_no_partial_machine_delivery(self):
        for p in NEW:
            sources = dict(self.sources)
            del sources[p]
            with self.assertRaises(AssertionError):
                check_source(sources)


if __name__ == '__main__':
    unittest.main()
