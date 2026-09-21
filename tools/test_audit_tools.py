"""Fast negative/positive tests for the read-only cleanup audit tools."""
import subprocess
import json
import unittest
from unittest.mock import patch

import audit_architecture as architecture
import audit_capabilities as capabilities
import audit_migration as migration
import audit_gate_c as gate_c
import audit_public_capabilities as public
import audit_prob_organization as prob
import audit_domain as domain
import audit_domain_measure as domain_measure
import audit_domain_soundness as domain_soundness
import audit_ds25 as ds25


class ArchitectureTests(unittest.TestCase):
    def test_external_domain_is_independent(self):
        domain = "Prob/Domain/Expectation"
        self.assertEqual(architecture.ownership(domain)[:2],
                         ("Prob/Domain", "external validation"))
        for dependency in ["Prob/Interface/Measure", "Prob/FreeOmega/Definition",
                           "Core/PTreeDefinition", "Eq/PEutt", "Prob/Backend/SubEnum/Measure"]:
            self.assertFalse(architecture.permitted(domain, dependency))
        self.assertTrue(architecture.permitted("Prob/Domain/MeasureModel", domain))

    def test_external_validation_is_not_mainline_infrastructure(self):
        for source in ["Eq/PEutt", "API/Generic", "Examples/RandomWalk",
                       "Interp/FreeOmega/Guarded", "Prob/Backend/SubEnum/Measure",
                       "Prob/Legacy/Discrete", "Semantics/MDPFragment"]:
            for target in ["Prob/Domain/Expectation",
                           "Prob/Backend/SubEnum/FreeOmega/DomainSoundness",
                           "Eq/Backend/StableHittingDomainSubEnum"]:
                self.assertFalse(architecture.permitted(source, target))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnum/Domain", "Prob/Domain/Expectation"))
        self.assertTrue(architecture.permitted("Regression/Probability/OmegaVal", "Prob/Domain/Expectation"))

    def test_external_boundary_checks_transitive_closure(self):
        graph = {"Examples/RandomWalk": {"Prob/Backend/SubEnum/Measure"},
                 "Prob/Backend/SubEnum/Measure": {"Prob/Backend/SubEnum/Domain"},
                 "Prob/Backend/SubEnum/Domain": {"Prob/Domain/Expectation"},
                 "Prob/Domain/Expectation": set()}
        with self.assertRaises(AssertionError):
            architecture.check_external_validation_boundary(graph)
        graph["Prob/Backend/SubEnum/Measure"] = set()
        architecture.check_external_validation_boundary(graph)

    def test_examples_owns_applications_not_regressions(self):
        self.assertEqual(architecture.ownership("Examples/RandomWalk")[:2],
                         ("Examples", "application"))
        self.assertTrue(architecture.permitted("Regression/Semantics/TreeTransitionSoundness",
                                             "Examples/RandomWalk"))
        self.assertFalse(architecture.permitted("Eq/PEutt", "Examples/RandomWalk"))

    def test_no_old_application_or_local_events_namespace(self):
        for name in ["CaseStudies/RandomWalk", "Events/State"]:
            with self.assertRaises(AssertionError):
                architecture.ownership(name)

    def test_auxiliary_check_follows_transitive_dependencies(self):
        graph = {"Eq/PEutt": set(), "PTree": set(), "Semantics": set(),
                 "Interp/FreeOmega/Base": {"Eq/FreeOmega/Bind"},
                 "Eq/FreeOmega/Bind": {"Eq/Internal/FiniteInternal"},
                 "Eq/Internal/FiniteInternal": set()}
        with self.assertRaises(AssertionError):
            architecture.check_auxiliary_boundary(graph)

    def test_semantic_freeomega_model_is_not_concrete_backend(self):
        self.assertEqual(architecture.ownership("Semantics/FreeOmega/MDPCoincidenceFreeOmega"),
                         ("Semantics/FreeOmega", "FreeOmega",
                          "retain comparison semantics; not canonical equality"))

    def test_semantic_subenum_endpoint_is_concrete_backend(self):
        self.assertEqual(architecture.ownership("Semantics/Backend/MDPEmbeddingSubEnum"),
                         ("Semantics/Backend", "SubEnum",
                          "retain comparison semantics; not canonical equality"))

    def test_interpretation_is_freeomega_qualified(self):
        self.assertEqual(architecture.ownership("Interp/FreeOmega/MDP")[:2],
                         ("Interp/FreeOmega", "FreeOmega"))

    def test_tree_cofinality_is_not_measure_infrastructure(self):
        self.assertEqual(architecture.ownership("Eq/Backend/EnumCofinality")[0],
                         "Eq/Backend")

    def test_forbidden_reverse_dependencies(self):
        for source, target in [
            ("Core/PTreeDefinition", "Prob/Legacy/Monad"),
            ("Prob/FreeOmega/Measure", "Prob/Backend/Enum/Measure"),
            ("Eq/FreeOmega/Bind", "Interp/FreeOmega/Cofinality"),
            ("Eq/PEutt", "Eq/FreeOmega/Bind"),
            ("Semantics/MDPFragment", "Semantics/FreeOmega/MDPCoincidenceFreeOmega"),
            ("Semantics/MDPFragment", "Interp/FreeOmega/MDP"),
            ("Interp/FreeOmega/MDP", "Interp/Backend/SubEnum"),
            ("Eq/PEutt", "Regression/Semantics/PEuttAlgebra"),
            ("Examples/RandomWalk", "Regression/Backend/SubEnumRegression"),
        ]:
            with self.subTest(source=source, target=target):
                self.assertFalse(architecture.permitted(source, target))

    def test_allowed_interpreter_comparison_direction(self):
        self.assertTrue(architecture.permitted("Interp/FreeOmega/MDP", "Semantics/MDPFragment"))

    def test_probability_native_axis_and_canonical_boundary(self):
        self.assertEqual(architecture.ownership("Prob/FreeOmega/Measure")[:2],
                         ("Prob/FreeOmega", "FreeOmega"))
        self.assertEqual(architecture.ownership("Prob/Backend/SubEnum/FreeOmega/Total")[:2],
                         ("Prob/Backend/SubEnum/FreeOmega", "SubEnum"))
        for m in ["Prob/Backend/FreeOmega/TotalSubEnum", "Prob/Backend/TwoLevelMeasureEnum"]:
            with self.assertRaises(AssertionError):
                architecture.ownership(m)
        for m, d in [("Prob/Backend/Common/FiniteMatching", "Prob/Backend/Enum/Measure"),
                     ("Prob/Backend/MathComp/Measure", "Prob/Backend/SubEnum/Measure"),
                     ("Prob/Backend/Enum/Measure", "Prob/Backend/MathComp/Measure")]:
            self.assertFalse(architecture.permitted(m, d))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnum/Measure", "Prob/Backend/Enum/Measure"))

    def test_unknown_experiment_requires_review(self):
        with self.assertRaises(AssertionError):
            architecture.ownership("Experimental/UnreviewedTheory")


class DomainAuditTests(unittest.TestCase):
    def test_no_semantic_interface_premise(self):
        with patch.object(capabilities, "query", return_value=[
                ("endpoint", "SemanticMeasure M -> True", "Closed under the global context")]):
            with self.assertRaises(AssertionError):
                domain.report()

    def test_new_or_unparsed_axiom_is_rejected(self):
        for assumptions in ["Axioms:\nshortcut : False", "Axioms:\nunparsed"]:
            with patch.object(capabilities, "query", return_value=[("endpoint", "True", assumptions)]):
                with self.assertRaises(AssertionError):
                    domain.report()

    def test_domain_query_does_not_mutate_historical_audit_scope(self):
        groups, endpoints = capabilities.GROUPS, capabilities.ENDPOINTS
        with patch.object(capabilities, "query", side_effect=SystemExit("query failure")):
            with self.assertRaises(SystemExit):
                domain.report()
        self.assertIs(capabilities.GROUPS, groups)
        self.assertIs(capabilities.ENDPOINTS, endpoints)


class DomainMeasureAuditTests(unittest.TestCase):
    def test_scope_includes_additivity_integral_and_both_roundtrips(self):
        names = domain_measure.GROUPS["PTree.Prob.Domain.MeasureModel"]
        for name in ["oval_set_measure_sigma_additive", "oval_integral_recovery",
                     "measure_oval_eval_continuous", "oval_probability_integral",
                     "oval_probability_roundtrip", "probability_oval_roundtrip"]:
            self.assertIn(name, names)
        self.assertIs(domain_measure.ALLOWED_AXIOMS, domain.ALLOWED_AXIOMS)

    def test_rejects_mainline_premise_or_new_axiom(self):
        for typ, assumptions in [
                ("SemanticMeasure M -> True", "Closed under the global context"),
                ("FreeOmega M A -> True", "Closed under the global context"),
                ("True", "Axioms:\nshortcut : False"),
                ("True", "Axioms:\nunparsed")]:
            with patch.object(capabilities, "query", return_value=[("endpoint", typ, assumptions)]):
                with self.assertRaises(AssertionError):
                    domain_measure.report()

    def test_preserves_ds1a_and_historical_query_scopes_on_failure(self):
        groups, endpoints, ds1a = capabilities.GROUPS, capabilities.ENDPOINTS, domain.GROUPS
        with patch.object(capabilities, "query", side_effect=SystemExit("query failure")):
            with self.assertRaises(SystemExit):
                domain_measure.report()
        self.assertIs(capabilities.GROUPS, groups)
        self.assertIs(capabilities.ENDPOINTS, endpoints)
        self.assertIs(domain.GROUPS, ds1a)


class DomainSoundnessAuditTests(unittest.TestCase):
    def test_scope_covers_validity_negative_example_and_external_order(self):
        names = {n for ns in domain_soundness.GROUPS.values() for n in ns}
        for n in ["admissible_sample_ae", "admissible_bind_ae", "admissible_lub_approx",
                  "free_omega_denote_bind", "free_omega_denote_lub",
                  "free_omega_denote_approx", "alternating_bool_not_admissible",
                  "null_weight_sample_denotes", "unbounded_retry_denotes_lub"]:
            self.assertIn(n, names)
        self.assertNotIn("free_omega_qlift_eq_sound", names)  # DS3, not DS2

    def test_rejects_generic_capability_or_tree_premise(self):
        for typ in ["forall NI : @Measure.SemanticMeasure M, True", "ptree E M A -> True"]:
            with patch.object(capabilities, "query", return_value=[
                    ("endpoint", typ, "Closed under the global context")]):
                with self.assertRaises(AssertionError):
                    domain_soundness.report()

    def test_rejects_new_or_unparsed_logical_axiom(self):
        for assumptions in ["Axioms:\nshortcut : False", "Axioms:\nunparsed"]:
            with patch.object(capabilities, "query", return_value=[("endpoint", "True", assumptions)]):
                with self.assertRaises(AssertionError):
                    domain_soundness.report()

    def test_preserves_existing_scopes_on_failure(self):
        groups, endpoints = capabilities.GROUPS, capabilities.ENDPOINTS
        with patch.object(capabilities, "query", side_effect=SystemExit("query failure")):
            with self.assertRaises(SystemExit):
                domain_soundness.report()
        self.assertIs(capabilities.GROUPS, groups)
        self.assertIs(capabilities.ENDPOINTS, endpoints)


class MigrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.normalize = staticmethod(migration.normalizer())

    def test_comments_and_explicit_relocation_only(self):
        self.assertEqual(self.normalize("(* outer (* nested *) *) PTree.Interp.FreeOmega.Cofinality.ptree_interp_cofinal_all"),
                         self.normalize("Bind.ptree_interp_cofinal_all"))

    def test_proof_or_contract_change_is_not_erased(self):
        for left, right in [("Lemma p : True.", "Lemma p : False."),
                            ("Proof. exact I. Qed.", "Admitted."),
                            ("Context {A : Type}.", "Context {A : Prop}.")]:
            with self.subTest(left=left):
                self.assertNotEqual(self.normalize(left), self.normalize(right))

    def test_nested_comment_does_not_consume_quoted_string(self):
        self.assertEqual(migration.without_comments('Check "(* not comment *)". (* outer (* nested *) *)'),
                         'Check "(* not comment *)".  ')

    def test_string_whitespace_is_semantic_not_layout(self):
        self.assertNotEqual(self.normalize('Definition label := "a  b".'),
                            self.normalize('Definition label := "a b".'))


class CapabilityTests(unittest.TestCase):
    def test_clean_preserves_type_but_not_prover_chatter(self):
        source = "\nFetching opaque proofs from disk for Test\nAxioms:\nx : True  \n\n1 goal\n===\nTrue\n"
        self.assertEqual(capabilities.clean(source), "Axioms:\nx : True")

    def test_coq_error_is_failure_even_with_zero_exit(self):
        result = subprocess.CompletedProcess([], 0, "", "Error: unknown theorem")
        with patch.object(capabilities.subprocess, "run", return_value=result):
            with self.assertRaises(SystemExit):
                capabilities.query()

    def test_missing_marker_is_failure(self):
        result = subprocess.CompletedProcess([], 0, "incomplete output", "")
        with patch.object(capabilities.subprocess, "run", return_value=result):
            with self.assertRaises(SystemExit):
                capabilities.query()

    def test_unknown_axiom_format_is_not_reported_as_none(self):
        with self.assertRaises(SystemExit):
            capabilities.report([("Test.endpoint", "True", "Axioms:\nunparsed")])

    def test_well_formed_query(self):
        output = ("AUDIT_TYPE_0\n@Test.endpoint : True\n\n1 goal\nTrue\n"
                  "AUDIT_AXIOMS_0\nClosed under the global context\n\n1 goal\nTrue\n"
                  "AUDIT_END_0\n")
        result = subprocess.CompletedProcess([], 0, output, "")
        with patch.object(capabilities, "ENDPOINTS", ["Test.endpoint"]):
            with patch.object(capabilities.subprocess, "run", return_value=result):
                self.assertEqual(capabilities.query(),
                    [("Test.endpoint", "@Test.endpoint : True", "Closed under the global context")])


class GateCTests(unittest.TestCase):
    def test_reviewed_full_type_and_axiom_deltas(self):
        before = json.loads(public.BASELINE.read_text())
        after = json.loads(public.CURRENT.read_text())
        self.assertEqual(set(public.check_delta(before, after)), public.WEAKENED)
        after["endpoints"][0]["assumptions"] += "\nNewAxiom : False"
        with self.assertRaises(AssertionError):
            public.check_delta(before, after)

    def test_kernel_bridge_edit_does_not_license_other_proof_edits(self):
        path = "theories/Eq/PTreeKernel.v"
        before = {path: migration.frozen("2af47aa")[path]}
        after = {path: gate_c.simplify_kernel_bridge(before[path]), **dict.fromkeys(gate_c.NEW, "")}
        gate_c.audit(before, after)
        after[path] = after[path].replace("Proof. apply sem_eq_refl. Qed.", "Proof. admit. Admitted.", 1)
        with self.assertRaises(AssertionError):
            gate_c.audit(before, after)

    def test_scope_covers_facades_and_proper_instances(self):
        names = public.scope(migration.frozen("2af47aa"))
        for name in ["PTree.API.Generic.peutt", "PTree.API.FreeOmega.mdp_state_interp",
                     "PTree.Semantics.tree_trans", "PTree.Eq.FreeOmega.Algebra.peutt_bind_Proper",
                     "PTree.Interp.FreeOmega.Base.peutt_interp_structural"]:
            self.assertIn(name, names)
        self.assertNotIn("PTree.Core.PTreeDefinition.Ret", names)  # parameterized notation
        self.assertIn("PTree.Core.PTreeDefinition.RetF", names)

    def test_duplicate_or_missing_endpoint_fails(self):
        e = {"name": "p", "type": "True", "assumptions": "closed"}
        for entries in [[], [e, e]]:
            with self.assertRaises(AssertionError):
                public.changes({"endpoints": [e]}, {"endpoints": entries})

    def test_import_cleanup_does_not_hide_proof_change(self):
        path = "theories/Eq/FreeOmega/Algebra.v"
        before = {path: "Require Import List.\nLemma p : True. Proof. exact I. Qed.\n"}
        after = {path: "Lemma p : True. Proof. exact I. Qed.\n", **dict.fromkeys(gate_c.NEW, "")}
        gate_c.audit(before, after)
        for replacement in ["Lemma p : False. Proof. exact I. Qed.\n",
                            "Lemma p : True. Admitted.\n"]:
            with self.assertRaises(AssertionError):
                gate_c.audit(before, {**after, path: replacement})

    def test_only_named_context_removal_is_allowed(self):
        path = "theories/Eq/FreeOmega/Base.v"
        text = "Context {MN : Type -> Type}\n" + gate_c.AE + "  `{NO : SemanticOmega MN}.\n"
        before = {path: text}
        after = {path: text.replace(gate_c.AE, ""), **dict.fromkeys(gate_c.NEW, "")}
        gate_c.audit(before, after)
        with self.assertRaises(AssertionError):
            gate_c.audit(before, {**after, path: after[path].replace("Type -> Type", "Type -> Prop")})

    def test_no_axiom_in_new_regression(self):
        with self.assertRaises(AssertionError):
            gate_c.audit({}, dict.fromkeys(gate_c.NEW, "Axiom shortcut : False."))


class DS25Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = migration.frozen(ds25.BASE)
        cls.after, cls.moves = ds25.expected_sources(cls.before)

    def test_exact_extraction(self):
        self.assertEqual(ds25.audit_sources(self.before, self.after), (228, 229))

    def test_rejects_statement_proof_context_comment_or_layout_edit(self):
        for path in [ds25.NEW, ds25.UPPER[0], ds25.DIR + "Domain.v"]:
            for old, new in [("Qed.", "Admitted."), ("realType", "Type"),
                             ("Proof.", "Proof. ")]:
                with self.subTest(path=path, old=old), self.assertRaises(AssertionError):
                    ds25.audit_sources(self.before, {**self.after,
                        path: self.after[path].replace(old, new, 1)})

    def test_frozen_math_cannot_change(self):
        for path in ["theories/Prob/Domain/Expectation.v",
                     "theories/Prob/Domain/MeasureModel.v",
                     ds25.DIR + "FreeOmega/Admissibility.v"]:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                ds25.audit_sources(self.before, {**self.after, path: self.after[path] + "\n"})

    def test_compiled_relocation_is_exact(self):
        old = "PTree.Prob.Backend.SubEnum.FreeOmega.UpperCoupling.subenum_lift_real_expect"
        new = "PTree.Prob.Backend.SubEnum.Expectation.subenum_lift_real_expect"
        self.assertEqual(ds25.normalize(old), ds25.normalize(new))
        self.assertEqual(ds25.normalize('"' + old + '"'), '"' + old + '"')
        e = dict(name=old, type="forall H : True, True", assumptions="Closed under the global context")
        before = {"endpoints": [e]}
        ds25.compare(before, {"endpoints": [{**e, "name": new}]})
        for change in [{"type": "True"}, {"assumptions": "Axioms: added : False"}]:
            with self.assertRaises(AssertionError):
                ds25.compare(before, {"endpoints": [{**e, **change}]})

    def test_native_domain_cannot_import_freeomega_indirectly(self):
        domain = "Prob/Backend/SubEnum/Domain"
        finite = "Prob/Backend/SubEnum/Expectation"
        helper = "Prob/Backend/Enum/Iteration"
        upper = "Prob/Backend/SubEnum/FreeOmega/UpperExpectation"
        graph = {domain: {finite}, finite: {helper}, helper: set(), upper: {finite}}
        architecture.check_native_expectation_boundary(graph)
        for bad in [upper, "Prob/FreeOmega/Definition"]:
            with self.assertRaises(AssertionError):
                architecture.check_native_expectation_boundary({**graph, helper: {bad}, bad: set()})
        with self.assertRaises(AssertionError):
            architecture.check_native_expectation_boundary({**graph, finite: {domain}})


class ProbOrganizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = migration.frozen(prob.BASE)
        cls.after = prob.expected_sources(cls.before)

    def test_every_source_line_accounted_for(self):
        self.assertEqual(prob.audit(self.before, self.after), (209, 220))

    def test_exact_extraction_rejects_comment_proof_context_or_layout_edits(self):
        path = "theories/Prob/FreeOmega/StructuralMeasure.v"
        for old, new in [("Qed.", "Admitted."), ("Type -> Type", "Type -> Prop"),
                         ("(** Role:", "(** Changed:"), ("Proof.", "Proof. ")]:
            with self.subTest(old=old), self.assertRaises(AssertionError):
                prob.audit(self.before, {**self.after, path: self.after[path].replace(old, new, 1)})

    def test_split_qualified_names_follow_declaration_owner(self):
        self.assertEqual(prob.relocate_token("PTree.Prob.Interface.TwoLevelMeasure.SemanticOmega"),
                         "PTree.Prob.Interface.Omega.SemanticOmega")
        self.assertEqual(prob.relocate_token("FreeOmegaMeasure.free_omega_observes"),
                         "PTree.Prob.FreeOmega.Observation.free_omega_observes")

    def test_signature_normalization_does_not_erase_assumptions(self):
        self.assertEqual(prob.normalize_compiled("TwoLevelMeasure.SemanticOmega"),
                         prob.normalize_compiled("Omega.SemanticOmega"))
        self.assertNotEqual(prob.normalize_compiled("forall (L : Omega.SemanticOmega), True"),
                            prob.normalize_compiled("True"))

    def test_signature_normalization_preserves_literal_strings(self):
        self.assertNotEqual(prob.normalize_compiled('"a  b"'), prob.normalize_compiled('"a b"'))
        self.assertEqual(prob.normalize_compiled('"TwoLevelMeasure.SemanticOmega"'),
                         '"TwoLevelMeasure.SemanticOmega"')
        self.assertEqual(prob.rewrite('Definition name := "TwoLevelMeasure.SemanticOmega".'),
                         'Definition name := "TwoLevelMeasure.SemanticOmega".')

    def test_lost_module_is_not_hidden_by_import_migration(self):
        after = dict(self.after)
        del after["theories/Prob/Interface/AE.v"]
        with self.assertRaises(AssertionError):
            prob.audit(self.before, after)

    def test_compiled_comparison_rejects_lost_contract_or_new_axiom(self):
        e = dict(name="Test.endpoint", type="forall H : True, True", assumptions="Closed under the global context")
        old = {"endpoints": [e]}
        prob.compare_snapshots(old, old)
        for changed in [{**e, "type": "True"}, {**e, "assumptions": "Axioms: added : False"}]:
            with self.assertRaises(AssertionError):
                prob.compare_snapshots(old, {"endpoints": [changed]})


if __name__ == "__main__":
    unittest.main()
