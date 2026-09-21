"""Failure-mode tests for the finite real transport increment."""
import unittest

import audit_real_transport as transport
from audit_migration import frozen


class RealTransportAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = frozen(transport.BASE)
        cls.after = frozen("f00478d")

    def test_isolation(self):
        self.assertEqual(transport.audit_sources(self.before, self.after), (243, 245))

    def test_frozen_theory_is_byte_exact(self):
        path = "theories/Prob/Domain/CountableTransport.v"
        with self.assertRaises(AssertionError):
            transport.audit_sources(self.before, {**self.after, path: self.after[path] + "\n"})

    def test_no_existence_assumption_or_formal_domain(self):
        path = "theories/" + transport.MATH + ".v"
        for addition in ["Axiom transport : False.", "Class TransportExists := {}.",
                         "Admitted.", "Check SemanticMeasure.", "Check OmegaVal.",
                         "Theorem free_omega_qlift_sound : True. Proof. exact I. Qed."]:
            with self.subTest(addition=addition), self.assertRaises(AssertionError):
                transport.audit_sources(self.before, {**self.after, path: self.after[path] + addition})

    def test_no_new_logical_axiom(self):
        with self.assertRaises(AssertionError):
            transport.check_answer("finite_real_transport", "True",
                                   "Axioms:\ntransport_existence : False")


if __name__ == "__main__":
    unittest.main()
