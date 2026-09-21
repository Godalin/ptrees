"""Isolation, assumption and one-way adapter tests for DS5a.2c."""
import unittest

import audit_countable_transport as transport
import audit_architecture as architecture
from audit_migration import frozen


class CountableTransportAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = frozen(transport.BASE)
        cls.after = frozen("b91df98")

    def test_isolation(self):
        self.assertEqual(transport.audit_sources(self.before, self.after), (245, 249))

    def test_frozen_theory_is_byte_exact(self):
        path = "theories/Prob/Backend/Common/RealTransport.v"
        with self.assertRaises(AssertionError):
            transport.audit_sources(self.before, {**self.after, path: self.after[path] + "\n"})

    def test_no_existence_assumption_or_free_representation(self):
        path = "theories/" + transport.BRIDGE + ".v"
        for addition in ["Axiom transport : False.", "Class TransportExists := {}.",
                         "Admitted.", "Check SemanticMeasure.", "Inductive Free := Mk.",
                         "Theorem free_omega_qlift_sound : True. Proof. exact I. Qed."]:
            with self.subTest(addition=addition), self.assertRaises(AssertionError):
                transport.audit_sources(self.before, {**self.after, path: self.after[path] + addition})

    def test_no_new_logical_axiom(self):
        with self.assertRaises(AssertionError):
            transport.check_answer("oval_bidual_coupled_nat", "True", "Axioms:\ntransport_existence : False")

    def test_adapter_is_one_way_external_validation(self):
        bridge = transport.BRIDGE
        self.assertTrue(architecture.external_validation(bridge))
        self.assertEqual(architecture.ownership(bridge)[1], "external validation")
        for dep in [transport.SCALAR, transport.MATRIX, "Prob/Domain/Atomic"]:
            self.assertTrue(architecture.permitted(bridge, dep))
        for source in ["Prob/Backend/Common/RealTransport", "Eq/PEutt",
                       "Prob/Backend/SubEnum/Measure", "API/FreeOmega", "Examples/RandomWalk"]:
            self.assertFalse(architecture.permitted(source, bridge))
        self.assertFalse(architecture.permitted("Prob/Domain/Matrix", transport.SCALAR))
        self.assertFalse(architecture.permitted(bridge, "Prob/Backend/SubEnum/Measure"))


if __name__ == "__main__":
    unittest.main()
