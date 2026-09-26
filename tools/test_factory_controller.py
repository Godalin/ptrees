"""Actual extracted flagship controller, not a second host implementation.

These tests check execution and separation boundaries, not PRNG correctness.
Build once before running this suite.
"""
import subprocess
import tempfile
import unittest
from pathlib import Path
from audit_assumptions import ROOT, without_comments

EXE = ROOT / '_build/default/extraction/factory-controller/main.exe'


class FactoryControllerTests(unittest.TestCase):
    def cli(self, *args, input=None, success=True):
        p = subprocess.run([str(EXE), *map(str, args)], input=input,
                           text=True, capture_output=True, timeout=40)
        self.assertEqual(p.returncode, 0 if success else 2, p.stderr)
        return p

    def field(self, output, key):
        return int(next(x.split('=', 1)[1] for x in output.splitlines()
                        if x.startswith(key + '=')))

    def test_actual_proof_roots_are_extracted(self):
        source = without_comments((ROOT/'extraction/factory-controller/Extract.v.in').read_text())
        for theorem in ['controller_refinement', 'state_controller_refinement',
                        'scripted_controller_program_rewrite']:
            self.assertIn(theorem, source)
        self.assertIn('closed_step demo_impl demo_spec', source)
        self.assertIn('live_step live_impl live_spec', source)
        self.assertNotRegex(source, r'Extract (?:Constant|Inductive)|Unset .*Checking|\b(?:Axiom|Admitted|Parameter)\b')
        generated = (EXE.parent/'controller.ml').read_text()
        self.assertNotIn('AXIOM TO BE REALIZED', generated)
        self.assertIn('Lazy.t', generated)
        host = (ROOT/'extraction/factory-controller/main.ml').read_text()
        self.assertNotIn('Bernoulli', host)
        self.assertNotIn('0.4', host)

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

    def test_complete_calculation_is_not_a_refinement_shortcut(self):
        source = without_comments((ROOT /
            'theories/Examples/FactoryController/Rewriting.v').read_text())
        proof = source.split('Theorem factory_controller_program_rewrite :', 1)[1].split('Qed.', 1)[0]
        for step in ['peutt_factory_vn_fair', 'peutt_sample_bind', 'peutt_sample_map',
                     'fair_binary_round_measure', 'peutt_factory_standard_direct']:
            self.assertIn(step, proof)
        for shortcut in ['implementation_sampler_correct', 'peutt_factory_vn_direct',
                         'peutt_factory_correct', 'peutt_factory_fair_direct',
                         'peutt_factory_fair_standard', 'controller_refinement',
                         'device_handler_refinement', 'scripted_controller_refinement']:
            self.assertNotIn(shortcut, proof)

    def test_calculation_reuses_generic_algebra(self):
        source = without_comments((ROOT /
            'theories/Examples/FactoryController/Rewriting.v').read_text())
        preamble = source.split('Section FullProgram.', 1)[0]
        self.assertNotIn('Proof.', preamble)
        self.assertNotRegex(source, r'\b(?:Instance|Hint|canonical_peutt)\b')
        self.assertIn('Import FreeOmegaRewriting.', preamble)
        self.assertIn('PEutt.peutt', preamble)
        support = without_comments((ROOT /
            'theories/Interp/FreeOmega/Rewriting.v').read_text())
        for theorem in ['run_state_peutt_eq_Proper', 'peutt_interp_Proper',
                        'run_exception_peutt_eq_Proper', 'peutt_iter_Proper']:
            self.assertIn(theorem, support)
        self.assertNotIn('Proof.', support)
        self.assertNotIn('#[global]', support)
        for concrete in ['EnumQ', 'SubEnumQ', 'SubEnumR', 'MathComp', 'CanonicalBehavior']:
            self.assertNotIn(concrete, support)
        for path, names in [
            ('FactoryController/Facts.v', ['embed_Proper', 'controller_Proper']),
            ('BernoulliFactory/BernoulliFactoryComposition.v', ['factory_with_sampler_Proper'])]:
            owner = without_comments((ROOT/'theories/Examples'/path).read_text())
            for name in names:
                self.assertIn('#[export] Instance ' + name, owner)
        self.assertNotRegex(source, r'Local Lemma sample_(?:bind|map)\b')
        for theorem in ['peutt_sample_bind', 'peutt_sample_map']:
            self.assertIn('setoid_rewrite (' + theorem + ' vn_fair).', source)
        self.assertNotIn('functional_extensionality', source)
        self.assertNotIn('FunctionalExtensionality', source)
        self.assertIn('Hround : forall x,', source)
        self.assertIn('setoid_rewrite Hround.', source)

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


if __name__ == '__main__':
    unittest.main()
