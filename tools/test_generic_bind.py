"""Mutation checks for the finite-algebra/generic bind extraction boundary."""
import unittest
from audit_assumptions import ROOT
from audit_generic_bind import check_source

class GenericBindTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources={p.relative_to(ROOT).as_posix():p.read_text()
                     for p in (ROOT/'theories').rglob('*.v')}

    def test_source_conservation(self):
        check_source(self.sources)

    def test_cannot_change_approx_quotient_or_routing(self):
        for p in ['theories/Prob/FreeOmega/Approximation.v',
                  'theories/Prob/FreeOmega/Quotient.v','theories/Eq/Canonical.v']:
            s=dict(self.sources);s[p]+='\nCheck True.\n'
            with self.subTest(path=p),self.assertRaises(AssertionError):check_source(s)

    def test_no_choice_or_backend_in_generic_proof(self):
        for token in ['choice','cid','FreeOmega','PEuttBindLaws','sem_eq_le']:
            s=dict(self.sources);s['theories/Eq/Bind.v']+='\nCheck '+token+'.\n'
            with self.subTest(token=token),self.assertRaises(AssertionError):check_source(s)

    def test_no_second_bind_owner(self):
        s=dict(self.sources);s['theories/Eq/FreeOmega/Bind.v']+='\nDefinition peutt_bind := True.\n'
        with self.assertRaises(AssertionError):check_source(s)

    def test_no_backdoor_interface_edit(self):
        s=dict(self.sources)
        p='theories/Prob/Interface/Omega.v'
        s[p]=s[p].replace('sem_zero_le :','sem_eq_le :',1)
        with self.assertRaises(AssertionError):check_source(s)

    def test_no_backend_coinduction_copy(self):
        s=dict(self.sources);s['theories/Eq/Backend/MathComp/Direct.v']+='\nCheck bind_bisim_candidate.\n'
        with self.assertRaises(AssertionError):check_source(s)

if __name__=='__main__':unittest.main()
