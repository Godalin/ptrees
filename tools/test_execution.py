"""Runtime checks of the actual extracted programs, not proof-script checks.

Run dune build first. Replay and fixed-seed statistics exercise implementations;
they do not prove PRNG fairness or replace the Rocq semantic theorems.
"""
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path
from audit_assumptions import ROOT, without_comments


class ExecutableTestCase(unittest.TestCase):
    """One subprocess boundary for every extracted execution target."""
    target = None

    @property
    def exe(self):
        return ROOT / '_build/default/extraction' / self.target / 'main.exe'

    def cli(self, *args, input=None, success=True):
        self.assertTrue(self.exe.exists(), 'Run dune build before runtime tests.')
        result = subprocess.run([str(self.exe), *map(str, args)], input=input,
                                text=True, capture_output=True, timeout=40)
        self.assertEqual(result.returncode, 0 if success else 2, result.stderr)
        return result

    def run_cli(self, *args):
        return self.cli(*args).stdout.splitlines()


class ExtractionSafetyTests(unittest.TestCase):
    def test_no_overrides_or_unrealized_axioms(self):
        for target, generated in [
            ('state-counter', 'counter.ml'),
            ('rational-state', 'rational.ml'),
            ('factory-controller', 'controller.ml'),
            ('unbounded', 'simulation.ml'),
        ]:
            with self.subTest(target=target):
                source = without_comments(
                    (ROOT / 'extraction' / target / 'Extract.v.in').read_text())
                self.assertNotRegex(source,
                    r'Extract (?:Constant|Inductive)|ExtrOcamlNatInt|'
                    r'Unset .*Checking|\b(?:Axiom|Admitted|Parameter)\b')
                code = (ROOT / '_build/default/extraction' / target / generated).read_text()
                self.assertNotIn('AXIOM TO BE REALIZED', code)
                driver = (ROOT / 'extraction' / target / 'main.ml').read_text()
                self.assertNotIn('Obj.magic', driver)


class ExtractedStateCounterTests(ExecutableTestCase):
    target = 'state-counter'

    def test_return_and_unused_entropy(self):
        self.assertEqual(self.run_cli('replay', 7, 0, '010'),
                         ['Returned 2', 'remaining=1', 'replay=010'])

    def test_timeout(self):
        self.assertEqual(self.run_cli('replay', 4, 0, '01')[:2], ['Timeout', 'remaining=1'])

    def test_entropy_exhaustion_not_loss(self):
        self.assertEqual(self.run_cli('replay', 100, 0, '0')[:2], ['EntropyExhausted', 'remaining=0'])

    def test_fuel_monotonicity_for_success(self):
        self.assertEqual(self.run_cli('replay', 7, 5, '01'), self.run_cli('replay', 90, 5, '01'))

    def test_seed_record_can_be_replayed(self):
        seeded = self.run_cli('seed', 100, 3, 42, 20)
        self.assertEqual(seeded, self.run_cli('replay', 100, 3, seeded[2].removeprefix('replay=')))

    def test_invalid_input_rejected(self):
        for args in [('replay', '-1', '0', '1'), ('replay', '5', '0', 'x')]:
            self.cli(*args, success=False)


class RationalTicketTests(ExecutableTestCase):
    target = 'rational-state'

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


class StateRewriteTests(ExecutableTestCase):
    target = 'rational-state'

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


class FactoryControllerTests(ExecutableTestCase):
    target = 'factory-controller'

    def field(self, output, key):
        return int(next(x.split('=', 1)[1] for x in output.splitlines()
                        if x.startswith(key + '=')))

    def test_script_runs_all_reply_branches(self):
        for program in ['impl', 'spec']:
            with self.subTest(program=program):
                out = self.cli(program, 'script', 42).stdout
                events = [x for x in out.splitlines() if '=' not in x]
                self.assertEqual(len(events), 10)
                self.assertEqual(events[0], 'receive 17')
                self.assertTrue(events[1].endswith(' rework'))
                self.assertTrue(events[2].endswith(' jam'))
                self.assertEqual(events[3:5], ['alarm 17', 'reset'])
                self.assertTrue(events[5].endswith(' pass'))
                self.assertEqual(events[6:8], ['ship 17', 'receive 23'])
                self.assertTrue(events[8].endswith(' pass'))
                self.assertEqual(events[9], 'ship 23')
                self.assertIn('experiment=script-exhausted', out)
                self.assertNotIn('Lost', out)

    def test_impl_really_uses_nested_factory_draws(self):
        impl = self.cli('impl', 'script', 42).stdout
        spec = self.cli('spec', 'script', 42).stdout
        self.assertEqual(self.field(spec, 'draws'), 4)
        self.assertGreater(self.field(impl, 'draws'), 4)

    def test_record_and_replay_preserve_actual_log(self):
        with tempfile.TemporaryDirectory() as tmp:
            trace = Path(tmp)/'tickets.txt'
            out = self.cli('impl', 'script', 17, '--trace', trace).stdout
            pairs = [list(map(int, line.split())) for line in trace.read_text().splitlines()]
            self.assertTrue(pairs)
            for bound, index in pairs:
                self.assertGreater(bound, index)
                self.assertGreaterEqual(index, 0)
            replay = self.cli('impl', 'replay', ','.join(str(i) for _, i in pairs)).stdout
            self.assertEqual(out, replay)
            self.cli('impl', 'script', 17, '--trace', trace, success=False)

    def test_entropy_artifacts_are_not_program_loss(self):
        out = self.cli('impl', 'replay', '', success=False)
        self.assertIn('entropy exhausted (not loss)', out.stderr)
        out = self.cli('spec', 'replay', '-1', success=False)
        self.assertIn('outside requested bound', out.stderr)

    def test_interactive_actual_continuations(self):
        out = self.cli('impl', 'interactive', 42,
                       input='17\nrework\njam\nok\npass\nquit\n').stdout
        self.assertEqual(out.count('machine 17 '), 3)
        self.assertIn('alarm 17', out)
        self.assertIn('reset (ok): ', out)
        self.assertIn('ship 17', out)
        self.assertIn('experiment stopped', out)

    def test_quit_without_order_uses_no_entropy(self):
        out = self.cli('impl', 'interactive', 42, input='quit\n').stdout
        self.assertIn('draws=0', out)

    def test_device_input_failure_is_not_missing_mass(self):
        out = self.cli('impl', 'interactive', 42, input='', success=False)
        self.assertIn('device input exhausted (not loss)', out.stderr)


class UnboundedExecutionTests(ExecutableTestCase):
    target = 'unbounded'

    def stats(self, program, trials=1000):
        result = self.cli(program, 'stats', trials, 42)
        fields = dict(line.split('=', 1) for line in result.stdout.splitlines()
                      if '=' in line and not line.startswith('theory:'))
        self.assertEqual(sum(int(fields[k]) for k in ['true', 'false', 'lost']), trials)
        return fields

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

    def test_factory_nested_loops_and_unused_entropy(self):
        # A fair true at x=2/5 stops with false. A fair false continues to
        # x=4/5, where another fair false stops with true.
        for trace, result, draws in [('3,0,8', 'false', 2),
                                     ('0,3,0,3,8', 'true', 4)]:
            output = self.cli('factory', 'replay', trace).stdout
            self.assertIn('Returned ' + result, output)
            self.assertIn(f'draws={draws}\n', output)
            self.assertIn('remaining=1\n', output)
        # 1000 inner VN retries, then 200 full outer binary cycles
        # 2/5 -> 4/5 -> 3/5 -> 1/5 -> 2/5, then a final return.
        trace = ['0', '0'] * 1000 + ['0', '3', '3', '0', '3', '0', '0', '3'] * 200 + ['3', '0']
        output = self.cli('factory', 'replay', ','.join(trace)).stdout
        self.assertIn('Returned false', output)
        self.assertIn('draws=3602\n', output)

    def test_factory_direct_ticket_boundary_and_errors(self):
        # Compiler creates 25 tickets: first 15 false, last 10 true.
        for ticket, result in [(0, 'false'), (14, 'false'), (15, 'true'), (24, 'true')]:
            output = self.cli('factory-direct', 'replay', ticket).stdout
            self.assertIn('Returned ' + result, output)
            self.assertIn('draws=1\n', output)
        for program, trace, error in [('factory', '0,3', 'entropy exhausted'),
                                      ('factory', '9', 'outside requested bound'),
                                      ('factory-direct', '25', 'outside requested bound')]:
            result = self.cli(program, 'replay', trace, success=False)
            self.assertIn(error, result.stderr)
            self.assertEqual(result.stdout, '')

    def test_factory_stats_target_is_two_fifths_not_one_half(self):
        for program in ['factory', 'factory-direct']:
            fields = self.stats(program, 3000)
            self.assertEqual(fields['lost'], '0')
            self.assertTrue(0.35 < float(fields['true_frequency']) < 0.45)
            self.assertTrue(0.55 < float(fields['false_frequency']) < 0.65)
            output = self.cli(program, 'stats', 1, 42).stdout
            self.assertIn('theory: true=2/5 false=3/5 lost=0', output)

    def test_factory_stream_only_uses_biased_source_not_target_draws(self):
        with tempfile.TemporaryDirectory() as directory:
            for program, bound in [('factory', '9'), ('factory-direct', '25')]:
                path = Path(directory)/(program + '.trace')
                original = self.cli(program, 'sample', 42, '--trace', path)
                self.assertEqual(original.stdout, self.cli(program, 'replay-file', path).stdout)
                self.assertTrue(path.read_text().strip())
                self.assertTrue(all(line.split()[0] == bound for line in path.read_text().splitlines()))
                # Random mode uses the very same step/tree pairing.
                self.assertIn('Returned', self.cli(program, 'random').stdout)

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
        process = subprocess.Popen([str(self.exe), 'spin', 'replay', ''],
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
