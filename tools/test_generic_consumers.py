"""Mutation tests for exact upper-layer consumer extraction."""
import unittest
from audit_assumptions import ROOT
from audit_generic_consumers import check_source, BASE, GUARD, COFINAL, REL, ITER, DIRECT, ALL

class GenericConsumerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources={p.relative_to(ROOT).as_posix():p.read_text()
                     for p in (ROOT/'theories').rglob('*.v')}

    def rejected(self,path,change):
        s=dict(self.sources);s[path]=change(s[path])
        with self.assertRaises(AssertionError):check_source(s)

    def test_exact_migration(self):
        check_source(self.sources)

    def test_foundations_and_routes_frozen(self):
        for p in ['Prob/Interface/Measure','Prob/Interface/Omega','Prob/FreeOmega/Quotient',
                  'Prob/FreeOmega/Approximation','Eq/Canonical','Eq/Bind']:
            with self.subTest(path=p):self.rejected('theories/'+p+'.v',lambda s:s+'\nCheck True.\n')

    def test_retained_theorem_statements_and_proofs(self):
        for p in [BASE,GUARD,COFINAL,REL,ITER]:
            with self.subTest(path=p):self.rejected(p,lambda s:s.replace('Qed.','Defined.',1))

    def test_no_conclusion_classes_or_axioms(self):
        for t in ['Class PEuttInterpLaws','Axiom hidden','Admitted','Hint Resolve hidden']:
            with self.subTest(token=t):self.rejected('theories/Interp/Guarded.v',lambda s:s+'\n'+t+'.\n')

    def test_generic_owner_is_backend_independent(self):
        for t in ['Check FreeOmega','Check MathCompNodeSemanticMeasure','Check sem_eq_le']:
            with self.subTest(token=t):self.rejected('theories/Interp/Scheduling.v',lambda s:s+'\n'+t+'.\n')

    def test_no_global_inference_expansion(self):
        self.rejected('theories/Interp/Scheduling.v',lambda s:s.replace('#[local]','#[global]',1))

    def test_old_gate_m_stays_untouched(self):
        self.rejected(DIRECT,lambda s:s.replace('Qed.','Defined.',1))

    def test_aggregate_order_and_coverage(self):
        self.rejected(ALL,lambda s:s.replace('Require PTree.Interp.Guarded.\n',''))

if __name__=='__main__':unittest.main()
