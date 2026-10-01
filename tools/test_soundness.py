"""Long-term regression coverage, source safety and frozen API checks."""
from rocq_paths import source_files
import json
import unittest
from unittest.mock import patch
import audit_soundness as soundness
import audit_api as api
import audit_assumptions as assumptions
import audit_contracts as contracts


class SoundnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources={p.relative_to(soundness.ROOT).as_posix():p.read_text()
                     for p in source_files()}
        cls.policy=json.loads(soundness.POLICY.read_text())

    def test_current_source_contract(self):
        soundness.source_check(self.sources,self.policy)

    def test_reject_assumptions_and_unfinished_proof(self):
        path='theories/Prob/Backend/SubEnumQ/FreeOmega/JointRealization.v'
        for bad in ['Axiom shortcut : False.','Parameter shortcut : False.',
                    'Lemma bad : False. Proof. admit. Admitted.',
                    'Class TransportExists := {}.']:
            with self.subTest(bad=bad),self.assertRaises(AssertionError):
                soundness.source_check({**self.sources,path:self.sources[path]+'\n'+bad},self.policy)

    def test_class_field_change(self):
        self.assertNotEqual(soundness.classes('Class C := { p : True }.'),
                            soundness.classes('Class C := { p : False }.'))
        self.assertEqual(soundness.classes('Class C := p : True.'),{'C':'Class C := p : True.'})

    def test_ordinary_proof_refactoring_is_not_a_safety_violation(self):
        # These are valid Rocq proofs; compilation, not this source scanner,
        # checks them. In particular induction/elimination is not forbidden.
        addition = """
Lemma audit_refactoring_probe (n : nat) : n = n.
Proof. induction n; reflexivity. Qed.
Lemma audit_elimination_probe (b : bool) : b = b.
Proof. elim b; reflexivity. Qed.
"""
        for path in [
            'theories/Prob/Backend/SubEnumQ/FreeOmega/JointRealization.v',
            'theories/Prob/Backend/SubEnumR/FreeOmega/JointRealization.v',
            'theories/Prob/Backend/SubEnumQ/FreeOmega/Compatibility.v',
        ]:
            with self.subTest(path=path):
                soundness.source_check(
                    {**self.sources, path: self.sources[path] + addition}, self.policy)

    def test_no_unsafe_universe_escape_in_maintained_theory(self):
        path='theories/Prob/Backend/MathComp/NativeLaws.v'
        with self.assertRaises(AssertionError):
            soundness.source_check({**self.sources,path:self.sources[path]+'\nLocal Unset Universe Checking.\n'},self.policy)

    def test_domain_and_scalar_isolation_mutations(self):
        for path, addition in [
            ('theories/Prob/Domain/Expectation.v', 'Check SemanticMeasure.'),
            ('theories/Prob/Domain/CountableTransport.v', 'Check FreeOmega.'),
            ('theories/Prob/Backend/Common/RealTransport.v', 'Check OmegaVal.'),
            ('theories/Prob/Backend/Common/CountableRealTransport.v', 'Check ptree.'),
            ('theories/Prob/Backend/Common/CountableCoupling.v', 'Check SubEnumQ.'),
        ]:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                soundness.independent_math({**self.sources,path:self.sources[path]+'\n'+addition})

    def test_independent_kernel_cannot_be_formal_denotation(self):
        path='theories/Prob/FreeOmega/Validation/StableHitting.v'
        for marker in ['Section DomainKernel.', 'Definition ptree_model_kernel']:
            changed=self.sources[path].replace(marker,marker+' Check ptree_hitting_approx.')
            with self.assertRaises(AssertionError):
                soundness.independent_math({**self.sources,path:changed})

    def test_hitting_validation_rejects_backend_or_validity_premises(self):
        for name, typ in [
            ('PTree.Prob.FreeOmega.Validation.StableHitting.stable_hitting_modelable',
             'SubEnumR -> free_omega_modelable'),
            ('PTree.Prob.FreeOmega.Validation.StableHitting.stable_hitting_modelable',
             'SemanticOmegaLaws -> free_omega_modelable'),
            ('PTree.Eq.Backend.StableHittingDomainSubEnumR.subenumR_stable_hitting_modelable',
             'free_omega_modelable -> free_omega_modelable'),
            ('PTree.Eq.Backend.StableHittingDomainSubEnumR.subenumR_stable_hitting_modelable',
             'native_lub -> free_omega_modelable'),
        ]:
            with self.subTest(typ=typ), patch.object(contracts, 'query', return_value=[{
                    'name': name, 'type': typ, 'assumptions': 'Closed under the global context'}]), \
                    self.assertRaises(AssertionError):
                contracts.stable_hitting_validation_check()

    def test_strings_and_comments_not_commands(self):
        self.assertNotIn('Admitted',soundness.code_only('(* Admitted. *) Check "Axiom Admitted".'))

    def test_lost_regression_is_rejected(self):
        path,names=next(iter(self.policy['clients'].items()))
        missing=self.sources.copy(); missing.pop(path)
        with self.assertRaises(AssertionError): soundness.source_check(missing,self.policy)
        changed=self.sources.copy(); changed[path]=changed[path].replace(names[0],'renamed_test')
        with self.assertRaises(AssertionError): soundness.source_check(changed,self.policy)

    def test_named_clients_have_real_sources(self):
        # Freeze selected contracts, not every helper added to an example.
        for path, names in self.policy['clients'].items():
            self.assertIn(path, self.sources)
            self.assertEqual(len(names), len(set(names)))

    def test_current_api(self):
        api.surface_check()

    def test_facade_contract_tracks_exports_and_aliases_not_format(self):
        text = 'From PTree Require Import A B. Export X Y. Notation public := Owner.fact.'
        same = 'Require Import PTree.B. Require Import PTree.A. Export X. Export Y. Notation public := Owner.fact.'
        expected = api.facade_surface(text)
        self.assertEqual(api.facade_surface(same), expected)
        for change in [text.replace('Owner.fact', 'Owner.other'),
                       text.replace('Export X Y', 'Export Y X'),
                       text + ' Notation hidden := private.']:
            self.assertNotEqual(api.facade_surface(change), expected)
        for change in [text + ' Definition hidden := True.',
                       text + ' Notation public := Other.fact.']:
            with self.assertRaises(AssertionError):
                api.facade_surface(change)

    def test_model_and_completeness_endpoints_retained(self):
        manifest=json.loads(assumptions.MANIFEST.read_text())
        names={n.rsplit('.',1)[1] for n in manifest['soundness']}
        for n in ['oval_integral_recovery','oval_probability_roundtrip','probability_oval_roundtrip',
                  'free_omega_qlift_sound','free_omega_sem_eq_sound',
                  'stable_hitting_denotational_adequacy','oval_bidual_coupled_nat']:
            self.assertIn(n,names)

    def test_generic_quotient_audit_rejects_strengthening_or_new_axiom(self):
        name = 'PTree.Prob.FreeOmega.Validation.Quotient.model_qlift_bidual_raw'
        for typ, axioms in [
            ('x : SubEnumQ A', 'Closed under the global context'),
            ('x : SemanticOmegaLaws MN', 'Closed under the global context'),
            ('x : SemanticMeasureBindLaws MN', 'Closed under the global context'),
            ('x : free_omega_modelable t -> True', 'Closed under the global context'),
            ('x : True', 'Axioms:\ntransport_exists : False'),
        ]:
            with self.subTest(typ=typ, axioms=axioms), \
                 patch.object(contracts, 'query', return_value=[{
                     'name': name, 'type': typ, 'assumptions': axioms}]), \
                 self.assertRaises(AssertionError):
                contracts.generic_quotient_check()

    def test_native_order_audit_rejects_circular_or_gluing_assumptions(self):
        name = 'PTree.Prob.Backend.MathComp.OrderLaws.mathcomp_native_bind_le_mu'
        for typ, axioms in [
            ('x : MathCompCouplingGluing R -> True', 'Closed under the global context'),
            ('x : SemanticMeasureOrderLaws M -> True', 'Closed under the global context'),
            ('x : SemanticOmegaLaws M -> True', 'Closed under the global context'),
            ('x : True', 'Axioms:\nnew_integral_axiom : False'),
        ]:
            with self.subTest(typ=typ), patch.object(contracts, 'query', return_value=[{
                    'name': name, 'type': typ, 'assumptions': axioms}]), self.assertRaises(AssertionError):
                contracts.mathcomp_native_check()

    def test_native_completion_and_bind_are_not_assumed(self):
        for module, name in [('OmegaLaws', 'mathcomp_native_bind_diagonal'),
                             ('BindLaws', 'mathcomp_native_lift_bind'),
                             ('Retry', 'mathcomp_retry_fixed_point')]:
            for typ in ['x : SemanticOmegaLaws M -> True',
                        'x : SemanticMeasureBindLaws M -> True',
                        'x : MathCompCouplingGluing R -> True']:
                with self.subTest(module=module, typ=typ), patch.object(contracts, 'query', return_value=[{
                    'name': 'PTree.Prob.Backend.MathComp.' + module + '.' + name,
                    'type': typ, 'assumptions': 'Closed under the global context'}]), self.assertRaises(AssertionError):
                    contracts.mathcomp_native_check()


if __name__=='__main__': unittest.main()
