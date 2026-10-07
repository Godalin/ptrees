"""Current-state contract runner: complete coverage and explicit trust contexts."""
import ast
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import audit_contracts as audit
from audit_assumptions import ROOT


class ContractSuiteTests(unittest.TestCase):
    def test_registered_snapshots_and_both_trust_domains(self):
        suites = audit.load_suites()
        self.assertTrue(any(g['context'] == 'gate-m' for g, _, _ in suites))
        self.assertTrue(any(g['context'] == 'safe-joint' for g, _, _ in suites))

    def changed_manifest(self, change):
        manifest = json.loads(audit.MANIFEST.read_text())
        change(manifest)
        with patch.object(audit, 'MANIFEST') as path:
            path.read_text.return_value = json.dumps(manifest)
            with self.assertRaises(AssertionError):
                audit.load_suites()

    def test_group_deletion_or_duplication_fails(self):
        self.changed_manifest(lambda d: d['groups'].pop())
        self.changed_manifest(lambda d: d['groups'].append(d['groups'][0]))

    def test_embedded_gate_m_group_cannot_be_silently_lost(self):
        self.changed_manifest(lambda d: d['groups'].__setitem__(slice(None),
                              [g for g in d['groups'] if g.get('field') != 'direct']))

    def test_joint_context_cannot_be_weakened(self):
        self.changed_manifest(lambda d: next(g for g in d['groups']
                              if g['id'] == 'direct_iteration').update(context='owners'))

    def test_unsafe_data_cannot_be_marked_safe(self):
        self.changed_manifest(lambda d: next(g for g in d['groups']
                              if g['context'] == 'gate-m-joint').update(context='owners'))

    def test_unknown_context_and_path_rejected(self):
        self.changed_manifest(lambda d: d['groups'][0].update(context='auto'))
        self.changed_manifest(lambda d: d['groups'][0].update(snapshot='../other/CONTRACTS.json'))

    def test_context_dispatch_and_exact_comparison(self):
        e = {'name': 'M.x', 'type': 'x : True', 'assumptions': 'Closed under the global context'}
        for context, modules in [('owners', None), ('recorded', ['M']),
                                 ('safe-joint', [audit.ALLIMPORTS])]:
            with patch.object(audit, 'query', return_value=[e]) as query:
                audit.check_group({'id': 'test', 'context': context}, {'modules': ['M']}, [e])
                query.assert_called_once_with(['M.x'], modules)
        for context, joint in [('gate-m', False), ('gate-m-joint', True)]:
            with patch.object(audit, 'query_gate_m', return_value=[e]) as query:
                audit.check_group({'id': 'test', 'context': context}, {}, [e])
                query.assert_called_once_with(['M.x'], joint=joint)
        with patch.object(audit, 'query', return_value=[dict(e, type='x : NewLaw -> True')]):
            with self.assertRaises(AssertionError):
                audit.check_group({'id': 'test', 'context': 'owners'}, {}, [e])

    def test_unknown_axiom_rejected_even_in_changed_snapshot(self):
        original = Path.read_text
        def corrupt(path, *args, **kw):
            text = original(path, *args, **kw)
            if path.name == 'DIRECT_ITERATION_CONTRACTS.json':
                data = json.loads(text)
                data['endpoints'][0]['assumptions'] = 'Axioms:\nnew_transport : False'
                return json.dumps(data)
            return text
        with patch.object(Path, 'read_text', corrupt), self.assertRaises(AssertionError):
            audit.load_suites()

    def test_scope_coverage_has_no_magic_count(self):
        data = json.loads((ROOT / 'tools/data/CONTRACTS.json').read_text())
        data['endpoints'].append({'name': 'M.new'})
        data['api'].append('M.new')
        data['capability'].append('M.new')
        audit.check_manifest(data)
        for scope in ['api', 'capability', 'soundness']:
            with self.subTest(scope=scope):
                changed = {**data, scope: data[scope] + [data[scope][0]]}
                with self.assertRaises(AssertionError):
                    audit.check_manifest(changed)
        with self.assertRaises(AssertionError):
            audit.check_manifest({**data, 'api': data['api'] + ['M.absent']})

    def test_soundness_scope_keeps_its_strict_axiom_whitelist(self):
        data = json.loads((ROOT / 'tools/data/CONTRACTS.json').read_text())
        entry = next(e for e in data['endpoints'] if e['name'] in data['soundness'])
        entry['assumptions'] = 'Axioms:\ntransport_exists : False'
        with self.assertRaises(AssertionError):
            audit.check_manifest(data)

    def test_all_semantic_checks_run_once_and_stay_out_of_gate_m(self):
        from unittest.mock import Mock
        checks = {name: Mock() for name in audit.SEMANTIC_CHECKS}
        self.assertEqual(set(checks), {'mathcomp-native', 'real-joint',
                                      'generic-quotient', 'stable-hitting'})
        with patch.object(audit, 'SEMANTIC_CHECKS', checks), \
             patch.object(audit, 'check_protocol_boundary') as boundary:
            audit.run_checks([], 'S')
            boundary.assert_called_once()
            for check in checks.values():
                check.assert_called_once()
                check.reset_mock()
            boundary.reset_mock()
            audit.run_checks([], 'M')
            boundary.assert_not_called()
            for check in checks.values():
                check.assert_not_called()
            audit.run_checks([], 'S', 'stable-hitting')
            checks['stable-hitting'].assert_called_once()
            for name, check in checks.items():
                if name != 'stable-hitting':
                    check.assert_not_called()
            boundary.assert_not_called()
            for gate, group in [('M', 'stable-hitting'), ('S', 'missing')]:
                with self.assertRaises(AssertionError):
                    audit.run_checks([], gate, group)

    def test_safe_control_cannot_acquire_unsafe_flag(self):
        entry = {'name': 'PTree.Prob.Backend.MathComp.NativeLaws.mathcomp_native_bind_le_k',
                 'type': 'control : True', 'assumptions': 'Closed under the global context',
                 'unsafe_hierarchy': [], 'session_collapsed_universes': True}
        with patch.object(audit, 'query_gate_m', return_value=[
                {**entry, 'unsafe_hierarchy': ['control']}]), self.assertRaises(AssertionError):
            audit.check_group({'id': 'control', 'context': 'gate-m'}, {}, [entry])

    def test_missing_theory_warning_only_for_closed_safe_control(self):
        original = Path.read_text
        for target, assumptions, flag, accepted in [
            (1, 'Closed under the global context', False, True),
            (1, 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P', False, False),
            (0, 'Closed under the global context', False, False),
            (1, 'Closed under the global context', 'false', False),
        ]:
            def changed(path, *args, **kw):
                text = original(path, *args, **kw)
                if path.name == 'DIRECT_ITERATION_CONTRACTS.json':
                    data = json.loads(text)
                    data['direct'][target].update(assumptions=assumptions,
                        session_collapsed_universes=flag)
                    return json.dumps(data)
                return text
            with self.subTest(target=target, assumptions=assumptions, flag=flag), \
                 patch.object(Path, 'read_text', changed):
                if accepted:
                    audit.load_suites()
                else:
                    with self.assertRaises(AssertionError):
                        audit.load_suites()

    def test_helpers_cannot_silently_succeed_as_old_audit_commands(self):
        for script in ['audit_assumptions.py', 'audit_mathcomp.py']:
            result = subprocess.run([sys.executable, 'tools/' + script],
                                    cwd=ROOT, text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('audit_contracts.py', result.stderr)

    def test_no_runtime_migration_replay(self):
        for path in (ROOT / 'tools').glob('*.py'):
            if path.name == Path(__file__).name:
                continue
            text = path.read_text()
            tree = ast.parse(text)
            self.assertFalse(any(isinstance(n, ast.FunctionDef) and n.name == 'previous_sources'
                                 for n in ast.walk(tree)), path.name)
            # Commands, not comments about historical results.
            for n in ast.walk(tree):
                if isinstance(n, (ast.List, ast.Tuple)):
                    strings = [v.value for v in n.elts if isinstance(v, ast.Constant) and isinstance(v.value, str)]
                    self.assertFalse('git' in strings and any(x in strings for x in ['show', 'archive', 'ls-tree']), path.name)

    def test_current_sources_work_without_dot_git(self):
        # A source archive is stronger than a shallow checkout. Copy only source
        # fixtures: no installed toolchain or build needed for these fast checks.
        with tempfile.TemporaryDirectory(prefix='ptree-audit-archive-') as tmp:
            root = Path(tmp)
            for name in ['tools', 'docs', 'theories', 'tests']:
                shutil.copytree(ROOT / name, root / name, ignore=shutil.ignore_patterns('__pycache__'))
            for name in ['dune-project', 'dune', '_CoqProject']:
                if (ROOT / name).exists():
                    shutil.copy2(ROOT / name, root / name)
            self.assertFalse((root / '.git').exists())
            for script, flag in [('audit_architecture.py', '--aggregate-only'),
                                 ('audit_api.py', None),
                                 ('audit_soundness.py', None),
                                 ('audit_contracts.py', '--metadata-only')]:
                result = subprocess.run([sys.executable, 'tools/' + script, *([flag] if flag else [])], cwd=root,
                                        text=True, capture_output=True, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_ci_runs_all_groups_and_keeps_shallow_checkout(self):
        workflow = (ROOT / '.github/workflows/coq.yml').read_text()
        self.assertIn('fetch-depth: 1', workflow)
        self.assertIn('tools/audit_contracts.py --gate S', workflow)
        self.assertIn('tools/audit_contracts.py --gate M', workflow)
        self.assertLess(workflow.index('--metadata-only'), workflow.index('Install Linux'))


if __name__ == '__main__':
    unittest.main()
