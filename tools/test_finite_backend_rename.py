"""The naming gate must not change representations or silently rebaseline contracts."""
import json
import unittest
from unittest.mock import patch
import audit_finite_backend_rename as audit


class NamingTests(unittest.TestCase):
    def test_rational_names_and_paths(self):
        self.assertEqual(audit.rename('PTree.Prob.Backend.SubEnum.Measure SubEnum_SemanticMeasure subenum_raw'),
                         'PTree.Prob.Backend.SubEnumQ.Measure SubEnumQ_SemanticMeasure subenumQ_raw')
        self.assertEqual(audit.rename('PTree.Prob.Backend.Enum.Representation Enum enum_expect ret_Enum'),
                         'PTree.Prob.Backend.EnumQ.Representation EnumQ enumQ_expect ret_EnumQ')

    def test_unrelated_and_already_migrated_names(self):
        text = 'SubEnumR subenumR_raw real_enum_expect enum enumT big_enum bigop.index_enum mem_enum map_tnth_enum nnQ rat FreeOmega peutt EnumQ SubEnumQ subenumQ_to_R'
        self.assertEqual(audit.rename(text), text)

    def test_idempotent(self):
        text = 'EnumRT enumRT enumk enumeq finite_enum_transport Enum_SemanticMeasure SubEnum subenumE'
        self.assertEqual(audit.rename(audit.rename(text)), audit.rename(text))

    def test_legacy_representation_is_not_renamed(self):
        text = b'Module Enum. Definition Enum := list nnQ. End Enum.\n'
        self.assertEqual(audit.expected('theories/Prob/Legacy/Discrete.v', text), text)

    def test_source_payload_is_not_normalized(self):
        old = b'Lemma enum_ret : True.\nProof. exact I. Qed.\n'
        self.assertEqual(audit.expected('theories/Test.v', old),
                         b'Lemma enumQ_ret : True.\nProof. exact I. Qed.\n')

    def test_allimports_sorted_without_dropping_entries(self):
        old = b'(* header *)\nRequire PTree.Regression.Backend.SubEnumR.\nRequire PTree.Regression.Backend.SubEnumRegression.\n'
        self.assertEqual(audit.expected(audit.AGGREGATE, old),
                         b'(* header *)\nRequire PTree.Regression.Backend.SubEnumQRegression.\nRequire PTree.Regression.Backend.SubEnumR.\n')

    def test_snapshot_allows_only_rename_and_whitespace(self):
        old = {'endpoints': [{'name': 'M.Enum', 'type': 'Enum -> True',
                              'assumptions': 'Closed under the global context'}]}
        with patch.object(audit, 'frozen', return_value=json.dumps(old).encode()):
            good = audit.map_json(old)
            good['endpoints'][0]['type'] = 'EnumQ\n ->  True'
            audit.check_snapshot('snapshot', good)
            for field, value in [('type', 'True -> EnumQ'),
                                 ('assumptions', 'Axioms: new_assumption : False')]:
                bad = audit.map_json(old)
                bad['endpoints'][0][field] = value
                with self.subTest(field=field), self.assertRaises(AssertionError):
                    audit.check_snapshot('snapshot', bad)


if __name__ == '__main__':
    unittest.main()
