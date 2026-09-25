"""Actual extracted State counter behavior; no historical source replay."""
import subprocess
import unittest
from audit_assumptions import ROOT


class ExtractedStateCounterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exe = ROOT/'_build/default/extraction/state-counter/main.exe'
        assert cls.exe.exists(), 'Run dune build before executable contracts (no nested/concurrent build).'

    def execute(self, *args):
        return subprocess.run([str(self.exe), *map(str, args)], check=True,
                              capture_output=True, text=True, timeout=15).stdout.splitlines()

    def test_return_and_unused_entropy(self):
        self.assertEqual(self.execute('replay', 7, 0, '010'),
                         ['Returned 2', 'remaining=1', 'replay=010'])

    def test_timeout(self):
        self.assertEqual(self.execute('replay', 4, 0, '01')[:2], ['Timeout', 'remaining=1'])

    def test_entropy_exhaustion_not_loss(self):
        self.assertEqual(self.execute('replay', 100, 0, '0')[:2], ['EntropyExhausted', 'remaining=0'])

    def test_fuel_monotonicity_for_success(self):
        self.assertEqual(self.execute('replay', 7, 5, '01'), self.execute('replay', 90, 5, '01'))

    def test_seed_record_can_be_replayed(self):
        seeded = self.execute('seed', 100, 3, 42, 20)
        self.assertEqual(seeded, self.execute('replay', 100, 3, seeded[2].removeprefix('replay=')))

    def test_invalid_input_rejected(self):
        for args in [('replay', '-1', '0', '1'), ('replay', '5', '0', 'x')]:
            result = subprocess.run([str(self.exe), *args], capture_output=True, timeout=15)
            self.assertEqual(result.returncode, 2)


if __name__ == '__main__':
    unittest.main()
