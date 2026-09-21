"""Frozen CI profile must fail closed on dependency/toolchain drift."""
import unittest
import os
import subprocess
from unittest.mock import patch
import check_ci_environment as ci


class FrozenEnvironmentTests(unittest.TestCase):
    def test_opam_frontend_drift_rejected(self):
        with patch.object(ci, 'output', return_value='2.6.0'), self.assertRaises(ValueError):
            ci.main()

    def test_all_constraints_exact_and_unique(self):
        versions = ci.profile_versions(ci.PROFILE.read_text())
        self.assertEqual(versions['ocaml-base-compiler'], '5.2.1')
        self.assertEqual(versions['dune'], '3.17.2')
        self.assertEqual(versions['coq'], '8.20.1')
        self.assertEqual(versions['coq-elpi'], '2.4.0')
        ci.check_versions(versions, versions)

    def test_profile_rejects_unbounded_or_duplicate_versions(self):
        for body in ['"dune" {>= "3.17.2"}',
                     '"dune" {= "3.17.2"}\n"dune" {= "3.23.1"}', '']:
            with self.subTest(body=body), self.assertRaises(ValueError):
                ci.profile_versions('depends: [\n' + body + '\n]')

    def test_missing_changed_and_unlocked_dependency_rejected(self):
        expected = {'dune': '3.17.2', 'elpi': '2.0.7'}
        for actual in [{'dune': '3.17.2'}, {**expected, 'dune': '3.23.1'},
                       {**expected, 'new-lib': '1.0'}]:
            with self.subTest(actual=actual), self.assertRaises(ValueError):
                ci.check_versions(expected, actual)

    def test_platform_probe_and_meta_packages_allowed(self):
        ci.check_versions({'dune': '3.17.2'}, {'dune': '3.17.2', 'ptree-ci': '1',
                                            'conf-linux-libc-dev': '0'})

    def test_installed_output_parsing(self):
        self.assertEqual(ci.installed_versions('# Name Version\ndune 3.17.2\n'),
                         {'dune': '3.17.2'})
        with self.assertRaises(ValueError):
            ci.installed_versions('dune 3.17.2\ndune 3.23.1')

    def test_profile_installed_before_project_solve(self):
        workflow = (ci.ROOT / '.github/workflows/coq.yml').read_text()
        profile = 'opam install ./.github/ci/ptree-ci.opam -y'
        project = 'opam install . --deps-only --with-test -y'
        self.assertLess(workflow.index(profile), workflow.index(project))
        self.assertLess(workflow.index(project), workflow.index('python3 tools/check_ci_environment.py'))
        self.assertIn('OPAMNOSELFUPGRADE: "true"', workflow)
        self.assertLess(workflow.index('bash .github/ci/bootstrap.sh'), workflow.index(profile))
        self.assertNotIn('Install supported Coq', workflow)

    def test_single_frontend_fresh_root_bootstrap(self):
        workflow = (ci.ROOT / '.github/workflows/coq.yml').read_text()
        script = (ci.ROOT / '.github/ci/bootstrap.sh').read_text()
        self.assertNotIn('setup-ocaml', workflow)
        self.assertNotIn('actions/cache', workflow)
        self.assertIn('mktemp -d "$RUNNER_TEMP/ptree-toolchain.XXXXXX"', script)
        self.assertIn('test ! -e "$OPAMROOT"', script)
        self.assertIn('export OPAMNOSELFUPGRADE=true', script)
        self.assertLess(script.index('test "$(opam --version)" = 2.5.1'),
                        script.index('opam init --bare'))
        self.assertIn('opam switch create ptree-ci ocaml-base-compiler.5.2.1', script)
        self.assertIn('OPAMROOT=%s\\nOPAMSWITCH=ptree-ci\\n', script)
        self.assertRegex(script, r'opam-repository.git#[0-9a-f]{40}')
        self.assertRegex(script, r'coq_revision=[0-9a-f]{40}')

    def test_bootstrap_refuses_local_execution(self):
        env = dict(os.environ, GITHUB_ACTIONS='false')
        result = subprocess.run(['bash', str(ci.ROOT / '.github/ci/bootstrap.sh')],
                                env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('only for disposable Linux x64 GitHub runners', result.stderr)


if __name__ == '__main__':
    unittest.main()
