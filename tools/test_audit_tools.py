"""Fast negative/positive tests for the read-only cleanup audit tools."""
import subprocess
import unittest
from unittest.mock import patch

import audit_architecture as architecture
import audit_capabilities as capabilities


class ArchitectureTests(unittest.TestCase):
    def test_interpretation_is_freeomega_qualified(self):
        self.assertEqual(architecture.ownership("Semantics/MDPInterp")[:2],
                         ("Interp/FreeOmega/MDP", "FreeOmega"))

    def test_tree_cofinality_is_not_measure_infrastructure(self):
        self.assertEqual(architecture.ownership("Prob/EnumCofinality")[0],
                         "Eq/Backend/EnumCofinality")

    def test_unknown_experiment_requires_review(self):
        with self.assertRaises(AssertionError):
            architecture.ownership("Experimental/UnreviewedTheory")


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
