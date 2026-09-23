"""Standard effects must reuse signatures and distinguish errors from loss."""
import unittest
from audit_assumptions import ROOT
from audit_standard_effects import ALL, check_source


class StandardEffectsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_additive_clients(self):
        check_source(self.sources)

    def test_standard_signatures_not_redeclared(self):
        self.reject('theories/Interp/Reader.v', lambda s: s + '\nVariant readerE : Type := Ask.\n')

    def test_reader_writer_use_existing_preservation(self):
        self.reject('theories/Interp/StandardFacts.v',
                    lambda s: s.replace('StatePreservation.run_state_peutt', 'assumed_preservation'))

    def test_no_axiom_or_checker_relaxation(self):
        for text in ['Admitted.', 'Class ExceptionPreservation := {}.', 'Local Unset Universe Checking.']:
            self.reject('theories/Interp/ExceptionFacts.v', lambda s: s + '\n' + text)

    def test_throw_is_not_divergence(self):
        self.reject('theories/Interp/Exception.v',
                    lambda s: s.replace('inl1 ex => Ret (inl (exception_value ex))', 'inl1 ex => Tau arbitrary'))

    def test_native_prob_preserved(self):
        self.reject('theories/Interp/Exception.v',
                    lambda s: s.replace('Prob mu (fun x => run_exception (k x))', 'Vis mu arbitrary'))

    def test_previous_theory_frozen(self):
        self.reject('theories/Interp/StatePreservation.v', lambda s: s + '\nCheck True.\n')

    def test_missing_import_rejected(self):
        self.reject(ALL, lambda s: s.replace('Require PTree.Interp.ExceptionFacts.\n', ''))


if __name__ == '__main__':
    unittest.main()
