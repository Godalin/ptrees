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


class ArchitectureTests(unittest.TestCase):
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
            ("Prob/FreeOmega/FreeOmegaMeasure", "Prob/Backend/TwoLevelMeasureEnum"),
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

    def test_unknown_experiment_requires_review(self):
        with self.assertRaises(AssertionError):
            architecture.ownership("Experimental/UnreviewedTheory")


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


if __name__ == "__main__":
    unittest.main()
