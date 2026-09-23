"""Current public-module ownership and conservative migration contracts."""
import copy
import unittest
from audit_assumptions import ROOT
from audit_public_modules import production_check, surface_check
from public_module_migration import frozen, endpoint, expected_contracts, REMOVED, text_relocation
import audit_architecture as architecture


class PublicModuleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix():p.read_text() for p in (ROOT/'theories').rglob('*.v')}

    def test_bind_rename_does_not_permit_proof_edits(self):
        for p in ['theories/Eq/PEutt.v','theories/Eq/FreeOmega/Bind.v']:
            production_check(p,frozen(p),self.sources[p])
            with self.subTest(path=p), self.assertRaises(AssertionError):
                production_check(p,frozen(p),self.sources[p].replace('Qed.','Defined.',1))

    def test_relation_notation_ownership_and_no_alias_shadowing(self):
        surface_check(self.sources)
        for p,extra in [
            ('theories/Eq/PEutt.v','\nNotation "t ≈ₚ u" := (peutt eq t u) (at level 70).'),
            ('theories/Eq/PStruct.v','\nDefinition peutt_bind := other.'),
            ('theories/PTreeFacts.v','\nNotation peutt_bind := Bind.peutt_bind.')]:
            s=dict(self.sources);s[p]+=extra
            with self.subTest(path=p),self.assertRaises(AssertionError):surface_check(s)

    def test_no_resurrected_api_directory(self):
        s=dict(self.sources);s['theories/API/Empty.v']=''
        with self.assertRaises(AssertionError):surface_check(s)
        with self.assertRaises(AssertionError):architecture.ownership('API/Generic')

    def test_exact_endpoint_disposition(self):
        self.assertEqual(text_relocation('MDPBehavior.peutt Behavior.canonical_peutt'),
                         'MDPBehavior.peutt Canonical.canonical_peutt')
        self.assertEqual(text_relocation('Section Behavior. End Behavior.'), 'Section Behavior. End Behavior.')
        self.assertEqual(len(REMOVED),10)
        self.assertIsNone(endpoint('PTree.API.SubEnumQ.submeas'))
        self.assertEqual(endpoint('PTree.API.Generic.peutt_bind'),'PTree.Eq.PEutt.peutt_bind_cofinal')
        self.assertEqual(endpoint('PTree.API.FreeOmega.peutt_bind'),'PTree.Eq.FreeOmega.Bind.peutt_bind')
        self.assertEqual(endpoint('PTree.API.SubEnumQ.subenumQ_mdp_state_interp_atomic'),
                         'PTree.Interp.Backend.SubEnumQ.subenumQ_mdp_state_interp_atomic')
        expected=expected_contracts()
        self.assertEqual(len(expected['endpoints']),465)
        self.assertEqual(len(expected['api']),266)
        self.assertEqual(len(expected['soundness']),199)

    def test_top_level_loading_boundaries(self):
        self.assertTrue(architecture.permitted('PTree','Core/PTreeDefinition'))
        self.assertTrue(architecture.permitted('Eq','Eq/Canonical'))
        self.assertTrue(architecture.permitted('PTreeFacts','Eq/FreeOmega/Bind'))
        for source,target in [('PTree','Eq/PEutt'),('Eq','Eq/Backend/SubEnumQ'),
                              ('PTreeFacts','Eq/Backend/MathComp/Direct'),
                              ('Eq/Backend/SubEnumQ','Interp/Backend/SubEnumQ')]:
            self.assertFalse(architecture.permitted(source,target))


if __name__=='__main__':unittest.main()
