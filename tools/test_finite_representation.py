"""The additive gate must neither migrate old backends nor weaken contracts."""
import json
import unittest
from unittest.mock import patch
import audit_finite_representation as audit


class CommonRepresentationTests(unittest.TestCase):
    def test_original_source_is_byte_exact(self):
        old = b'Lemma same : True. Proof. exact I. Qed.\n'
        audit.preserved_file('theories/Old.v', old, old, '')
        with self.assertRaises(AssertionError):
            audit.preserved_file('theories/Old.v', old, old + b'\n', '')

    def test_allimports_only_three_sorted_insertions(self):
        old = b'(* aggregate *)\nRequire PTree.Core.X.\nRequire PTree.Z.\n'
        changed = audit.inserted_imports(old)
        audit.preserved_file(audit.AGGREGATE, old, changed, '')
        lines = [s for s in changed.splitlines() if s.startswith(b'Require')]
        self.assertEqual(lines, sorted(set(lines)))
        self.assertEqual(len(lines), 5)
        with self.assertRaises(AssertionError):
            audit.preserved_file(audit.AGGREGATE, old, changed.replace(b'Require PTree.Z.\n', b''), '')

    def test_policy_only_adds_new_tests(self):
        old = {'regressions': {'old': ['retained']}, 'classes': {}}
        new = {'regressions': {'old': ['retained'], audit.REGRESSION: ['test']}, 'classes': {}}
        audit.preserved_file(audit.POLICY, json.dumps(old), json.dumps(new), 'Example test : True.')
        new['classes']['extra'] = 'Class Extra.'
        with self.assertRaises(AssertionError):
            audit.preserved_file(audit.POLICY, json.dumps(old), json.dumps(new), 'Example test : True.')

    def test_common_isolation(self):
        sources = {p: (audit.ROOT / p).read_text() for p in [audit.ENUM, audit.SUBDIST]}
        audit.common_boundary(sources)
        for text in ['Axiom shortcut : False.', 'Class Stronger := {}.',
                     'Check SemanticMeasure.', 'Check nnQ.', 'Check Nonneg.',
                     'Local Unset Universe Checking.', 'Check realType.',
                     'From PTree.Prob.Backend.SubEnumR Require Import Representation.']:
            with self.subTest(text=text), self.assertRaises(AssertionError):
                audit.common_boundary({**sources, audit.ENUM: sources[audit.ENUM] + '\n' + text})

    def test_compiled_audit_rejects_axioms(self):
        with patch.object(audit, 'query', return_value=[{
            'name': 'M.bad', 'type': 'bad : True', 'assumptions': 'Axioms:\nextra : False'}]):
            with self.assertRaises(AssertionError):
                audit.compiled_check()

    def test_common_algebra_cannot_acquire_even_whitelisted_axiom(self):
        with patch.object(audit, 'query', return_value=[{
            'name': 'PTree.Prob.Backend.Common.FiniteEnum.finite_expect',
            'type': 'finite_expect : ssrnum.Num.NumDomain.type -> True',
            'assumptions': 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P'}]):
            with self.assertRaises(AssertionError):
                audit.compiled_check()


if __name__ == '__main__':
    unittest.main()
