"""Conservation, operational boundaries, and real extracted executable tests."""
import subprocess
import unittest
from audit_assumptions import ROOT
from audit_effect_execution import check_source, ALL


class EffectExecutionTests(unittest.TestCase):
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

    def test_existing_probability_and_handler_theory_frozen(self):
        for p in ['Eq/PEutt', 'Eq/Canonical', 'Interp/Preservation', 'Interp/Guarded',
                  'Prob/FreeOmega/Quotient']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_no_axiom_or_backend_capability(self):
        for text in ['Class HandlerPreservation := {}.', 'Admitted.', 'Axiom run_ok : True.',
                     'Local Unset Universe Checking.']:
            self.reject('theories/Execution/Runner.v', lambda s: s + text)

    def test_no_fake_behavioral_preservation(self):
        self.reject('theories/Interp/StateFacts.v', lambda s: s + '\nCheck peutt.\n')

    def test_no_resample_or_normalization_of_missing_mass(self):
        self.reject('theories/Execution/Runner.v',
                    lambda s: s.replace("Missing => (Lost, seed')", "Missing => (Timeout, seed')"))

    def test_no_missing_or_duplicate_aggregate(self):
        line = 'Require PTree.Execution.Runner.\n'
        self.reject(ALL, lambda s: s.replace(line, ''))
        self.reject(ALL, lambda s: s + line)

    def test_operational_checkpoint_is_frozen(self):
        self.reject('theories/Execution/Backend/SubEnumQ.v', lambda s: s + '\nCheck True.\n')

    def test_state_iteration_requires_no_probability_capability(self):
        self.reject('theories/Interp/StateIter.v', lambda s: s + '\nClass StateIterLaws := {}.\n')


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
