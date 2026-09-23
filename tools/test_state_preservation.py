"""Keep state-indexed preservation generic, non-circular and additive."""
import unittest
from audit_assumptions import ROOT
from audit_state_preservation import ALL, NEW, check_source


class StatePreservationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_additive_only(self):
        check_source(self.sources)

    def test_operational_state_and_fixed_handler_frozen(self):
        for p in ['Interp/State', 'Interp/StateIter', 'Interp/Unrestricted',
                  'Interp/HandlerMachineAcceleration', 'Prob/FreeOmega/Quotient']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_axiom_capability_or_unchecked_proof(self):
        for text in ['Class StatePreservation := {}.', 'Admitted.', 'Local Unset Universe Checking.']:
            self.reject('theories/Interp/StatePreservation.v', lambda s: s + '\n' + text)

    def test_cannot_replace_weak_premise_with_structural(self):
        self.reject('theories/Interp/StatePreservation.v', lambda s: s.replace(' peutt_coinduction', ' pstruct'))

    def test_no_target_preservation_assumption(self):
        self.reject('theories/Interp/StatePreservation.v', lambda s: s + '\nVariable Htarget : True.\n')

    def test_adequacy_required(self):
        self.reject('theories/Interp/StatePreservation.v',
                    lambda s: s.replace('state_machine_hitting_sound', 'assumed_adequacy'))

    def test_no_missing_or_duplicate_import(self):
        line = 'Require PTree.Interp.StatePreservation.\n'
        self.reject(ALL, lambda s: s.replace(line, ''))
        self.reject(ALL, lambda s: s + line)

    def test_no_partial_delivery(self):
        for p in NEW:
            sources = dict(self.sources)
            del sources[p]
            with self.assertRaises(AssertionError):
                check_source(sources)


if __name__ == '__main__':
    unittest.main()
