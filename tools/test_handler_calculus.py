"""Handler calculus preserves old semantics and keeps backend obligations explicit."""
import unittest
from audit_assumptions import ROOT
from audit_handler_calculus import ALL, NEW, check_source, previous_sources, frozen

class HandlerCalculusTests(unittest.TestCase):
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

    def test_exact_prior_reconstruction(self):
        prior = previous_sources(self.sources)
        self.assertEqual(prior['theories/Interp/Preservation.v'],
                         frozen('theories/Interp/Preservation.v'))
        self.assertEqual(prior['theories/Interp/Unrestricted.v'],
                         frozen('theories/Interp/Unrestricted.v'))

    def test_semantics_routing_and_machine_frozen(self):
        for p in ['Eq/PEutt', 'Eq/Canonical', 'Interp/HandlerMachine',
                  'Interp/Guarded', 'Prob/FreeOmega/Quotient',
                  'Eq/Backend/MathComp/Direct']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_new_axiom_or_global_search(self):
        for p in NEW:
            for suffix in ['Axiom oracle : True.', 'Class HandlerPreservation := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_both_handlers_and_real_adequacy_required(self):
        p = 'theories/Interp/HandlerRelation.v'
        for token in ['active1 active2', 'handler_machine_hitting_sound', 'peutt_state_hitting_lift']:
            self.reject(p, lambda s, token=token: s.replace(token, 'missing_stage'))

    def test_old_statement_not_editable(self):
        self.reject('theories/Interp/Unrestricted.v',
                    lambda s: s.replace('RR t u ->', 'RR t t ->'))

    def test_delegation_not_duplicate_old_proof(self):
        self.reject('theories/Interp/Preservation.v',
                    lambda s: s.replace('exact Hvis.', 'admit.'))

    def test_client_rewrite_and_high_universe_required(self):
        for token in ['setoid_rewrite H', 'Constraint Set < hi']:
            self.reject('theories/Regression/Infrastructure/PublicHandlers.v',
                        lambda s, token=token: s.replace(token, 'missing_client'))

    def test_unique_aggregate(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Core.Handler.\n')

if __name__ == '__main__':
    unittest.main()

