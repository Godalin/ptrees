"""Reject circular fold laws, missing target proofs, and frozen-source drift."""
import unittest
from audit_assumptions import ROOT
from audit_state_fold import ALL, check_source


class StateFoldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_additive_fold_laws(self):
        check_source(self.sources)

    def test_uniformity_not_ptree_specific(self):
        self.reject('theories/Core/IterationLaws.v', lambda s: s + '\nCheck ptree.\n')

    def test_no_new_capability_or_bypass(self):
        for text in ['Class FoldPreservation := {}.', 'Admitted.', 'Local Unset Universe Checking.']:
            self.reject('theories/Interp/StateFoldFacts.v', lambda s: s + '\n' + text)

    def test_requires_a_real_target_proof(self):
        self.reject('theories/Execution/ITreeFold.v', lambda s: s.replace("eutt_iter'", 'assumed_iter'))

    def test_keeps_negative_iterator(self):
        self.reject('theories/Regression/Semantics/StateFold.v',
                    lambda s: s.replace('~ @iteration_uniform', '@iteration_uniform'))

    def test_old_definitions_unchanged(self):
        self.reject('theories/Interp/StateFold.v', lambda s: s + '\nCheck True.\n')

    def test_import_required(self):
        self.reject(ALL, lambda s: s.replace('Require PTree.Core.IterationLaws.\n', ''))


if __name__ == '__main__':
    unittest.main()
