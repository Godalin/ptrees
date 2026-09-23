"""Mutation checks for the ad8705f generic-consumer extraction."""
import subprocess
import unittest
from audit_assumptions import ROOT
from audit_generic_algebra import check_source, ALG, FOALG, COUPLING, MEASURE, COINCIDENCE, DIRECT

class GenericAlgebraTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        paths = subprocess.check_output(['git','ls-tree','-r','--name-only','c2dea6b'],
                                        cwd=ROOT,text=True).splitlines()
        cls.sources = {p:subprocess.check_output(['git','show','c2dea6b:'+p],
                        cwd=ROOT,text=True) for p in paths if p.endswith('.v')}

    def test_conservation(self):
        check_source(self.sources)

    def test_frozen_definitions_and_routing(self):
        for p in ['theories/Prob/FreeOmega/Approximation.v',
                  'theories/Prob/FreeOmega/Quotient.v', 'theories/Eq/Canonical.v',
                  'theories/Eq/Bind.v','theories/Interp/FreeOmega/Guarded.v']:
            s=dict(self.sources);s[p]+='\nCheck True.\n'
            with self.subTest(path=p),self.assertRaises(AssertionError):check_source(s)

    def test_retained_equations_and_dirac_proof(self):
        for p in [FOALG,MEASURE,COINCIDENCE]:
            s=dict(self.sources);s[p]=s[p].replace('Qed.','Defined.',1)
            with self.subTest(path=p),self.assertRaises(AssertionError):check_source(s)

    def test_no_new_class_or_backend_in_generic(self):
        for token in ['Class PEuttBindLaws', 'Axiom hidden', 'Hint Resolve hidden', 'Check FreeOmega']:
            s=dict(self.sources);s[ALG]+='\n'+token+'.\n'
            with self.subTest(token=token),self.assertRaises(AssertionError):check_source(s)

    def test_derived_fact_not_global_instance(self):
        s=dict(self.sources)
        s[COUPLING]=s[COUPLING].replace('Lemma coupling_ae_implies_ae_lift',
                                    '#[global] Instance coupling_ae_implies_ae_lift')
        with self.assertRaises(AssertionError):check_source(s)

    def test_existing_mathcomp_proof_unchanged(self):
        s=dict(self.sources);s[DIRECT]=s[DIRECT].replace('Qed.','Defined.',1)
        with self.assertRaises(AssertionError):check_source(s)

    def test_no_second_owner(self):
        s=dict(self.sources);s[FOALG]+='\nDefinition peutt_bind_Proper := True.\n'
        with self.assertRaises(AssertionError):check_source(s)

if __name__=='__main__':unittest.main()
