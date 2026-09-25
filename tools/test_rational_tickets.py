"""Actual extracted rational-ticket execution and missing-mass boundaries."""
import subprocess
import unittest
from audit_assumptions import ROOT


class RationalTicketTests(unittest.TestCase):
    def run_cli(self, *args):
        exe = ROOT/'_build/default/extraction/rational-state/main.exe'
        self.assertTrue(exe.exists(), 'Build the extracted executable first')
        p = subprocess.run([str(exe), *map(str, args)], capture_output=True, text=True, timeout=30)
        self.assertEqual(p.returncode, 0, p.stderr)
        return p.stdout.splitlines()

    def test_replay_returns_and_retains_unused_input(self):
        self.assertEqual(self.run_cli('replay', 7, 0, '2,0,5'),
                         ['Returned 2', 'remaining=1', 'consumed=2,0'])

    def test_loss_stops_without_resampling(self):
        self.assertEqual(self.run_cli('replay', 100, 0, '5,0'),
                         ['Lost', 'remaining=1', 'consumed=5'])

    def test_timeout_preserves_next_ticket(self):
        self.assertEqual(self.run_cli('replay', 4, 0, '2,0'),
                         ['Timeout', 'remaining=1', 'consumed=2'])

    def test_invalid_or_empty_entropy(self):
        self.assertEqual(self.run_cli('replay', 3, 0, '6')[0], 'EntropyExhausted')
        self.assertEqual(self.run_cli('replay', 3, 0, '')[0], 'EntropyExhausted')

    def test_seed_deterministic_and_replayable(self):
        a = self.run_cli('seed', 1000, 7, 2026, 100)
        self.assertEqual(a, self.run_cli('seed', 1000, 7, 2026, 100))
        trace = a[2].removeprefix('consumed=')
        b = self.run_cli('replay', 1000, 7, trace)
        self.assertEqual((a[0], a[2]), (b[0], b[2]))

    def test_random_mode_records_replay(self):
        a = self.run_cli('random', 1000, 0, 100)
        b = self.run_cli('replay', 1000, 0, a[2].removeprefix('consumed='))
        self.assertEqual((a[0], a[2]), (b[0], b[2]))


if __name__ == '__main__':
    unittest.main()
