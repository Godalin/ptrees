"""Mutation tests for the exact universe exception and trust separation."""
import unittest
import tempfile
from pathlib import Path
from types import SimpleNamespace
from mathcomp_direct_policy import DIRECT, GATE_M, ALLOWLIST, universe_source_check, check_gate_boundary, safe_targets, check_build_flags
from audit_mathcomp_direct import parse_direct


class MathCompDirectTests(unittest.TestCase):
    def test_reviewed_allowlist(self):
        self.assertEqual(GATE_M, {'Eq/Backend/MathComp/Direct', 'Regression/Backend/MathCompDirect'})

    def test_exact_local_exception_only(self):
        for path in ALLOWLIST:
            universe_source_check(path, 'Local Unset Universe Checking.\nDefinition x := 0.')
            for bad in ['Unset Universe Checking.', '#[local] Unset Universe Checking.',
                        'Global Unset Universe Checking.', '',
                        'Local Unset Universe Checking.\nLocal Unset Universe Checking.',
                        'Local Unset Universe Checking.\nUnset Guard Checking.',
                        'Local Unset Universe Checking.\nUnset Positivity Checking.',
                        'Local Unset Universe Checking.\n#[bypass_check(universes)] Definition x := 0.',
                        'Local Unset Universe Checking.\nClass NewLaw := {}.']:
                with self.subTest(path=path, bad=bad), self.assertRaises(AssertionError):
                    universe_source_check(path, bad)

    def test_no_directory_permission(self):
        for path in ['theories/Prob/Backend/MathComp/NativeLaws.v',
                     'theories/Eq/Backend/MathComp/Unreviewed.v',
                     'theories/Regression/Backend/NewMathComp.v',
                     'theories/Examples/MathComp.v', 'theories/Prob/Domain/Expectation.v']:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                universe_source_check(path, 'Local Unset Universe Checking.')

    def test_safe_aggregate_and_indirect_import(self):
        client = 'Regression/Backend/MathCompDirect'
        graph = {DIRECT: set(), client: {DIRECT}, 'Regression/Infrastructure/AllImports': set()}
        check_gate_boundary(graph)
        graph['Regression/Infrastructure/AllImports'] = {client}
        with self.assertRaises(AssertionError):
            check_gate_boundary(graph)
        graph['Regression/Infrastructure/AllImports'] = {'Prob/Backend/MathComp/Helper'}
        graph['Prob/Backend/MathComp/Helper'] = {DIRECT}
        with self.assertRaises(AssertionError):
            check_gate_boundary(graph)

    def test_client_must_use_direct(self):
        with self.assertRaises(AssertionError):
            check_gate_boundary({m: set() for m in GATE_M})

    def test_safe_targets_exclude_exact_allowlist(self):
        from audit_assumptions import ROOT
        targets = safe_targets(ROOT)
        self.assertTrue(all(p[:-3] + '.v' not in ALLOWLIST for p in targets))
        self.assertIn('theories/Regression/Infrastructure/AllImports.vo', targets)

    def test_project_wide_bypass_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'dune-project').write_text('(flags -type-in-type)')
            with self.assertRaises(AssertionError):
                check_build_flags(root)

    def test_unsafe_reports_are_not_logical_axioms(self):
        block = ('Axioms:\nprobe relies on an unsafe hierarchy.\n'
                 'Theory:\nType hierarchy is collapsed (logic is inconsistent)\n')
        def result(body):
            return SimpleNamespace(returncode=0, stderr='', stdout=
                'AUDIT_TYPE_0\nprobe : True\nAUDIT_AXIOMS_0\n' + body + 'AUDIT_END_0\n')
        entry = parse_direct(result(block), ['probe'])[0]
        self.assertTrue(entry['session_collapsed_universes'])
        self.assertEqual(entry['unsafe_hierarchy'], ['probe'])
        safe = parse_direct(result(block.replace('probe relies on an unsafe hierarchy.\n', '')), ['probe'])[0]
        self.assertEqual(safe['unsafe_hierarchy'], [])
        self.assertTrue(safe['session_collapsed_universes'])
        for bad in [block.replace('Theory:', 'UnknownTheory:'),
                    block.replace('Theory:\nType hierarchy is collapsed (logic is inconsistent)\n', ''),
                    block + 'new_transport_axiom : False\n', block + 'Error: failed\n']:
            with self.subTest(bad=bad), self.assertRaises(AssertionError):
                parse_direct(result(bad), ['probe'])


if __name__ == '__main__':
    unittest.main()
