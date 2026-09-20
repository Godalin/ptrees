"""Fast negative/positive tests for the read-only cleanup audit tools."""
import subprocess
import unittest
from unittest.mock import patch

import audit_architecture as architecture
import audit_capabilities as capabilities
import audit_migration as migration


class ArchitectureTests(unittest.TestCase):
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
            ("CaseStudies/RandomWalk", "Regression/Backend/SubEnumRegression"),
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


if __name__ == "__main__":
    unittest.main()
