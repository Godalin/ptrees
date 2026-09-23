"""Generic consumers must not hide backend laws or rewrite frozen theory."""
import unittest
from audit_assumptions import ROOT
from audit_relational_consumers import check_source, ALL, REL, DIRECT


class RelationalConsumerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT / 'theories').rglob('*.v')}

    def reject(self, path, change):
        sources = dict(self.sources)
        sources[path] = change(sources[path])
        with self.assertRaises(AssertionError):
            check_source(sources)

    def test_exact_migration(self):
        check_source(self.sources)

    def test_unrelated_theory_frozen(self):
        for p in ['Eq/Canonical', 'Eq/PEutt', 'Prob/FreeOmega/Quotient',
                  'Prob/Interface/Omega', 'Interp/Guarded']:
            self.reject('theories/' + p + '.v', lambda s: s + '\nCheck True.\n')

    def test_old_structural_observation_frozen(self):
        self.reject(REL, lambda s: s.replace('Lemma ptree_hitting_pstruct', 'Lemma renamed'))

    def test_no_backend_name_in_generic_proof(self):
        self.reject('theories/Eq/Relation.v', lambda s: s + '\nCheck FreeOmega.\n')

    def test_no_new_theorem_class(self):
        for text in ['Class StructuralPeuttLaws := {}.', 'Axiom strong_sound : True.',
                     'Local Unset Universe Checking.', 'Admitted.']:
            self.reject('theories/Eq/Relation.v', lambda s: s + text)

    def test_limit_increasing_condition(self):
        self.reject('theories/Prob/Interface/RelationalClosure.v',
                    lambda s: s.replace('sem_increasing c ->', 'True ->'))

    def test_extracted_algebra_proof(self):
        self.reject('theories/Eq/Algebra.v', lambda s: s.replace('apply pstruct_bind_assoc.', 'admit.'))

    def test_no_extra_native_ae_requirement(self):
        self.reject('theories/Eq/FreeOmega/Relation.v',
                    lambda s: s.replace('`{NO :', '`{NAE : SemanticMeasureAELiftLaws MN NI}\n  `{NO :'))

    def test_mathcomp_limit_not_claimed_proved(self):
        self.reject(DIRECT, lambda s: s.replace('Variable Hlimit : relational_lub NO.', ''))

    def test_aggregate_complete(self):
        self.reject(ALL, lambda s: s.replace('Require PTree.Eq.Relation.\n', ''))


if __name__ == '__main__':
    unittest.main()
