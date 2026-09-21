"""Long-term regression coverage, source safety and frozen API checks."""
import copy
import json
import unittest
from unittest.mock import patch
import audit_soundness as soundness
import audit_api as api
import audit_assumptions as assumptions


class SoundnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources={p.relative_to(soundness.ROOT).as_posix():p.read_text()
                     for p in (soundness.ROOT/'theories').rglob('*.v')}
        cls.policy=json.loads(soundness.POLICY.read_text())

    def test_current_source_contract(self):
        soundness.source_check(self.sources,self.policy)
        soundness.manifest_check()

    def test_reject_assumptions_and_unfinished_proof(self):
        path='theories/Prob/Backend/SubEnum/FreeOmega/JointSoundness.v'
        for bad in ['Axiom shortcut : False.','Parameter shortcut : False.',
                    'Lemma bad : False. Proof. admit. Admitted.',
                    'Class TransportExists := {}.', 'Check FOQLComp.', 'induction H.', 'elim H.']:
            with self.subTest(bad=bad),self.assertRaises(AssertionError):
                soundness.source_check({**self.sources,path:self.sources[path]+'\n'+bad},self.policy)

    def test_class_field_change(self):
        self.assertNotEqual(soundness.classes('Class C := { p : True }.'),
                            soundness.classes('Class C := { p : False }.'))
        self.assertEqual(soundness.classes('Class C := p : True.'),{'C':'Class C := p : True.'})

    def test_domain_and_scalar_isolation_mutations(self):
        for path, addition in [
            ('theories/Prob/Domain/Expectation.v', 'Check SemanticMeasure.'),
            ('theories/Prob/Domain/CountableTransport.v', 'Check FreeOmega.'),
            ('theories/Prob/Backend/Common/RealTransport.v', 'Check OmegaVal.'),
            ('theories/Prob/Backend/Common/CountableRealTransport.v', 'Check ptree.'),
            ('theories/Prob/Backend/Common/CountableCoupling.v', 'Check SubEnum.'),
        ]:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                soundness.independent_math({**self.sources,path:self.sources[path]+'\n'+addition})

    def test_independent_kernel_cannot_be_formal_denotation(self):
        path='theories/Eq/Backend/StableHittingDomainSubEnum.v'
        for marker in ['Section DomainKernel.', 'Definition ptree_domain_kernel']:
            changed=self.sources[path].replace(marker,marker+' Check ptree_hitting_approx.')
            with self.assertRaises(AssertionError):
                soundness.independent_math({**self.sources,path:changed})

    def test_strings_and_comments_not_commands(self):
        self.assertNotIn('Admitted',soundness.code_only('(* Admitted. *) Check "Axiom Admitted".'))

    def test_lost_regression_is_rejected(self):
        path,names=next(iter(self.policy['regressions'].items()))
        missing=self.sources.copy(); missing.pop(path)
        with self.assertRaises(AssertionError): soundness.source_check(missing,self.policy)
        changed=self.sources.copy(); changed[path]=changed[path].replace(names[0],'renamed_test')
        with self.assertRaises(AssertionError): soundness.source_check(changed,self.policy)

    def test_source_scope_covers_every_regression_with_theorems(self):
        import re
        for path,text in self.sources.items():
            if path.startswith('theories/Regression/') and re.search(r'^(?:Example|Lemma|Theorem) ',text,re.M):
                self.assertIn(path,self.policy['regressions'])

    def test_current_api(self):
        api.surface_check()

    def test_public_alias_drift(self):
        path=next(iter(self.policy['facades']))
        expected=self.policy['facades'][path]
        self.assertNotEqual(api.facade_surface(expected+' Notation hidden := private.'),expected)

    def test_new_axiom_rejected_even_if_snapshot_is_corrupted(self):
        entry={'name':'M.x','type':'x : True','assumptions':'Axioms:\nshortcut : False'}
        data={'endpoints':[entry],'modules':['M'],'soundness':['M.x']}
        with patch.object(assumptions.json,'loads',return_value=data), \
             patch.object(assumptions,'query',return_value=[entry]), self.assertRaises(AssertionError):
            assumptions.check()

    def test_model_and_completeness_endpoints_retained(self):
        manifest=json.loads(assumptions.MANIFEST.read_text())
        names={n.rsplit('.',1)[1] for n in manifest['soundness']}
        for n in ['oval_integral_recovery','oval_probability_roundtrip','probability_oval_roundtrip',
                  'free_omega_qlift_sound','free_omega_sem_eq_sound',
                  'stable_hitting_denotational_adequacy','oval_bidual_coupled_nat']:
            self.assertIn(n,names)


if __name__=='__main__': unittest.main()
