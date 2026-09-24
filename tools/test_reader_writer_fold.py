"""Freeze old semantics; distinguish generic transformer laws from target facts."""
import unittest
from audit_assumptions import ROOT
from audit_reader_writer_fold import ALL, NEW, check_source, previous_sources, frozen


class ReaderWriterFoldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}

    def reject(self, p, f):
        changed = dict(self.sources)
        changed[p] = f(changed[p])
        with self.assertRaises(AssertionError):
            check_source(changed)

    def test_current_increment(self):
        check_source(self.sources)

    def test_exact_prior(self):
        self.assertEqual(previous_sources(self.sources)[ALL], frozen(ALL))

    def test_no_assumptions_or_global_instances(self):
        for p in NEW:
            for suffix in ['Axiom magic : True.', 'Admitted.', 'Class EffectLaw := {}.',
                           'Local Unset Universe Checking.', '#[global] Instance magic : True := I.']:
                self.reject(p, lambda s, suffix=suffix: s + '\n' + suffix + '\n')

    def test_uniformity_and_monoid_explicit(self):
        for owner in ['Reader', 'Writer']:
            self.reject(f'theories/Core/{owner}T.v',
                        lambda s: s.replace('(Hunif : @iteration_uniform T MT IT QT)', '(Hunif : True)'))
        self.reject('theories/Core/WriterT.v', lambda s: s.replace('MonoidLaws op', 'True'))

    def test_log_order_not_commutativity(self):
        self.reject('theories/Core/WriterT.v',
                    lambda s: s.replace('monoid_plus op (fst wi) (fst wv)', 'monoid_plus op (fst wv) (fst wi)'))
        self.reject('theories/Core/WriterT.v', lambda s: s + '\nCheck Commutative.\n')

    def test_target_scope_is_explicit(self):
        for owner in ['Reader', 'Writer']:
            self.reject(f'theories/Interp/{owner}FoldITree.v', lambda s: s.replace('-> itree F X', '-> T X'))

    def test_no_interpreter_replacement(self):
        for p in ['Interp/Reader', 'Interp/Writer', 'Core/IterationLaws', 'Core/ExceptT', 'Eq/PEutt']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_aggregate_unique(self):
        self.reject(ALL, lambda s: s + 'Require PTree.Core.WriterT.\n')


if __name__ == '__main__':
    unittest.main()
