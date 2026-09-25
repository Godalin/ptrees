"""Both extracted versions and the no-same-fuel boundary are real tests."""
import subprocess
import unittest
from audit_assumptions import ROOT


class StateRewriteTests(unittest.TestCase):
    def run_cli(self, *args):
        exe = ROOT/'_build/default/extraction/rational-state/main.exe'
        self.assertTrue(exe.exists())
        p = subprocess.run([str(exe), *map(str,args)], capture_output=True, text=True, timeout=30)
        self.assertEqual(p.returncode, 0, p.stderr)
        return p.stdout.splitlines()

    def test_corresponding_traces(self):
        self.assertEqual(self.run_cli('original', 'replay', 7, 0, '2,0,0'),
                         ['Returned 11', 'remaining=0', 'consumed=2,0,0'])
        self.assertEqual(self.run_cli('rewrite', 'replay', 6, 0, '24,0'),
                         ['Returned 11', 'remaining=0', 'consumed=24,0'])

    def test_no_same_fuel_claim(self):
        self.assertEqual(self.run_cli('original', 'replay', 6, 0, '2,0,0'),
                         ['Timeout', 'remaining=1', 'consumed=2,0'])

    def test_missing_mass_remains(self):
        self.assertEqual(self.run_cli('rewrite', 'replay', 100, 0, '47,0'),
                         ['Lost', 'remaining=1', 'consumed=47'])

    def test_each_program_seed_replays(self):
        for program in ['original', 'rewrite']:
            a = self.run_cli(program, 'seed', 1000, 0, 2026, 100)
            b = self.run_cli(program, 'replay', 1000, 0, a[2].removeprefix('consumed='))
            self.assertEqual((a[0],a[2]), (b[0],b[2]))


if __name__ == '__main__':
    unittest.main()
