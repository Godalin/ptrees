"""Failure-mode tests for the incremental DS5a.2 preparation audit."""
import unittest

import audit_domain_transport as transport
from audit_migration import frozen


class TransportAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = frozen(transport.BASE)
        cls.after = {p.relative_to(transport.ROOT).as_posix(): p.read_text()
                     for p in (transport.ROOT / "theories").rglob("*.v")}

    def test_isolation(self):
        self.assertEqual(transport.audit_sources(self.before, self.after), (239, 243))

    def test_frozen_theory_is_byte_exact(self):
        path = "theories/Prob/Domain/Countable.v"
        with self.assertRaises(AssertionError):
            transport.audit_sources(self.before, {**self.after, path: self.after[path] + "\n"})

    def test_no_new_semantic_assumption_or_free_syntax(self):
        path = "theories/Prob/Domain/Series.v"
        for addition in ["Axiom transport : False.", "Class TransportExists := {}.",
                         "Inductive NewFree := NRet.", "Admitted.",
                         "Check SemanticMeasure."]:
            with self.subTest(addition=addition), self.assertRaises(AssertionError):
                transport.audit_sources(self.before, {**self.after, path: self.after[path] + addition})

    def test_no_completion_claim_in_preparation(self):
        path = "theories/Prob/Domain/CountableTransport.v"
        with self.assertRaises(AssertionError):
            transport.audit_sources(self.before, {**self.after, path: self.after[path] +
                "Theorem countable_transport_exists : True. Proof. exact I. Qed."})

    def test_new_logical_axiom_rejected(self):
        with self.assertRaises(AssertionError):
            transport.check_answer("PTree.Prob.Domain.Series.oval_series", "True",
                                   "Axioms:\ntransport_existence : False")


if __name__ == "__main__":
    unittest.main()
