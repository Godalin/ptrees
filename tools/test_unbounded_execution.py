"""Actual proof-linked, fuel-free OCaml simulation and its explicit boundaries.

Build extraction/unbounded/main.exe first. Statistical checks are fixed-seed
smoke tests, never substitutes for peutt or proofs of PRNG fairness.
"""
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path

from audit_assumptions import ROOT, without_comments

BASELINE = 'ac52a86'
EXE = ROOT / '_build/default/extraction/unbounded/main.exe'


class UnboundedExecutionTests(unittest.TestCase):
    def cli(self, *args, success=True):
        result = subprocess.run([str(EXE), *map(str, args)], text=True,
                                capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0 if success else 2, result.stderr)
        return result

    def stats(self, program, trials=1000):
        result = self.cli(program, 'stats', trials, 42)
        fields = dict(line.split('=', 1) for line in result.stdout.splitlines()
                      if '=' in line and not line.startswith('theory:'))
        self.assertEqual(sum(int(fields[k]) for k in ['true', 'false', 'lost']), trials)
        return fields

    def test_proved_roots_and_no_extraction_override(self):
        source = without_comments((ROOT/'extraction/unbounded/Extract.v.in').read_text())
        self.assertIn('Definition program_correct := peutt_von_neumann_raw_direct.', source)
        self.assertIn('Extraction "simulation.ml" machine_step von_neumann_third direct_fair', source)
        self.assertIn('ticket_sample next (@enumQ_as_subprob X mu H)', source)
        self.assertNotRegex(source, r'Extract (?:Constant|Inductive)|ExtrOcamlNatInt|'
                                   r'Unset .*Checking|\b(?:Axiom|Admitted|Parameter)\b')
        generated = (EXE.parent/'simulation.ml').read_text()
        self.assertIn('Lazy.t', generated)
        self.assertNotIn('AXIOM TO BE REALIZED', generated)

    def test_old_theory_and_executables_unchanged(self):
        paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE],
                                        cwd=ROOT, text=True).splitlines()
        for path in paths:
            if path.startswith(('theories/', 'extraction/')) or (
                path.startswith('docs/') and path.endswith('CONTRACTS.json')
            ):
                expected = subprocess.check_output(['git', 'show', f'{BASELINE}:{path}'], cwd=ROOT)
                self.assertEqual((ROOT/path).read_bytes(), expected, path)

    def test_source_retries_then_returns_and_keeps_unused_entropy(self):
        result = self.cli('vn', 'replay', '0,0,0,3,8').stdout
        self.assertIn('Returned false\n', result)
        self.assertIn('draws=4\n', result)
        self.assertIn('remaining=1\n', result)
        self.assertIn('Returned true', self.cli('vn', 'replay', '3,0').stdout)

    def test_direct_fair_both_outcomes(self):
        for trace, expected in [('0', 'false'), ('2', 'true')]:
            output = self.cli('direct', 'replay', trace).stdout
            self.assertIn('Returned ' + expected, output)
            self.assertIn('draws=1', output)

    def test_long_retry_is_not_fuel_exhaustion(self):
        trace = ','.join(['0', '0'] * 2000 + ['0', '3'])
        result = self.cli('vn', 'replay', trace).stdout
        self.assertIn('Returned false', result)
        self.assertIn('draws=4002', result)
        self.assertNotIn('Timeout', result)

    def test_loss_stops_without_redraw(self):
        output = self.cli('lost', 'replay', '0,0').stdout
        self.assertTrue(output.startswith('Lost\n'))
        self.assertIn('draws=1\n', output)
        self.assertIn('remaining=1\n', output)

    def test_errors_are_not_loss_or_timeout(self):
        for program, trace, message in [('vn', '', 'entropy exhausted'),
                                        ('vn', '9', 'outside requested bound'),
                                        ('overweight', '', 'mass greater than one')]:
            result = self.cli(program, 'replay', trace, success=False)
            self.assertIn(message, result.stderr)
            self.assertEqual(result.stdout, '')

    def test_ret_does_not_request_entropy(self):
        output = self.cli('ret', 'replay', '').stdout
        self.assertIn('Returned true', output)
        self.assertIn('draws=0', output)

    def test_streamed_trace_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'tickets.txt'
            original = self.cli('vn', 'sample', 42, '--trace', path)
            replay = self.cli('vn', 'replay-file', path)
            self.assertEqual(original.stdout, replay.stdout)
            self.assertTrue(path.read_text().strip())
            self.assertIn('9 ', path.read_text())
            # An existing path is never overwritten, even if it is the input.
            saved = path.read_bytes()
            self.cli('vn', 'replay-file', path, '--trace', path, success=False)
            self.assertEqual(path.read_bytes(), saved)
            self.assertIn('replay bound mismatch',
                          self.cli('direct', 'replay-file', path, success=False).stderr)

    def test_both_proved_programs_have_fair_empirical_results(self):
        for program in ['vn', 'direct']:
            fields = self.stats(program)
            self.assertEqual(fields['lost'], '0')
            self.assertTrue(0.40 < float(fields['true_frequency']) < 0.60)
        self.assertEqual(self.cli('vn', 'sample', 42).stdout,
                         self.cli('vn', 'sample', 42).stdout)

    def test_partial_mass_not_conditionally_normalized(self):
        fields = self.stats('partial')
        self.assertEqual(fields['false'], '0')
        self.assertTrue(0.40 < float(fields['lost_frequency']) < 0.60)
        self.assertTrue(0.40 < float(fields['true_frequency']) < 0.60)

    def test_random_mode_and_argument_validation(self):
        self.assertIn('Returned', self.cli('direct', 'random').stdout)
        self.assertIn('Returned', self.cli('vn', 'random').stdout)
        for args in [('vn', 'stats', 0, 42), ('vn', 'replay', '-1'), ('bad', 'random')]:
            self.cli(*args, success=False)

    def test_genuine_divergence_can_be_interrupted(self):
        process = subprocess.Popen([str(EXE), 'spin', 'replay', ''],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            with self.assertRaises(subprocess.TimeoutExpired):
                process.communicate(timeout=0.3)
            process.send_signal(signal.SIGINT)
            out, err = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 130)
            self.assertEqual(out, '')
            self.assertIn('Interrupted (not a program result)', err)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()


if __name__ == '__main__':
    unittest.main()
