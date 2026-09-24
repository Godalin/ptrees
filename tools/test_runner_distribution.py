"""Probability bridge scope and source conservation; no PRNG fairness claim."""
import unittest
from audit_assumptions import ROOT
from audit_runner_distribution import ALL, NEW, check_source


class RunnerDistributionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def test_additive_bridge(self):
        check_source(self.sources)

    def test_preserves_sampler_and_runner(self):
        for path in ['theories/Execution/Runner.v', 'theories/Execution/Backend/RationalTickets.v']:
            changed = dict(self.sources)
            changed[path] += '\nCheck True.\n'
            with self.assertRaises(AssertionError):
                check_source(changed)

    def test_history_contract_and_existing_execution_required(self):
        for token in ['source history (ticket_count mu)', 'i :: history', 'run (@ticket_replay)',
                      'uniform_ticket_expectation']:
            changed = dict(self.sources)
            path = 'theories/Execution/Backend/UniformReplay.v'
            changed[path] = changed[path].replace(token, 'missing_bridge')
            with self.assertRaises(AssertionError):
                check_source(changed)

    def test_no_new_assumption_or_bypass(self):
        for path in NEW:
            for addition in ['Axiom oracle_fair : True.', 'Local Unset Universe Checking.']:
                changed = dict(self.sources)
                changed[path] += '\n' + addition + '\n'
                with self.assertRaises(AssertionError):
                    check_source(changed)

    def test_no_duplicate_aggregate(self):
        changed = dict(self.sources)
        changed[ALL] += 'Require PTree.Execution.Backend.UniformReplay.\n'
        with self.assertRaises(AssertionError):
            check_source(changed)


if __name__ == '__main__':
    unittest.main()
