"""DS5a.3 isolation, composition-only proof and external-validation boundaries."""
import unittest

import audit_domain_joint as joint
import audit_architecture as architecture
from audit_migration import frozen


class DomainJointAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = frozen(joint.BASE)
        cls.after = {p.relative_to(joint.ROOT).as_posix(): p.read_text()
                     for p in (joint.ROOT / "theories").rglob("*.v")}

    def test_isolation(self):
        self.assertEqual(joint.audit_sources(self.before, self.after), (249, 252))

    def test_aggregate_insertions_preserve_ci_order(self):
        source = self.before["theories/Regression/Infrastructure/AllImports.v"]
        old = [line for line in source.splitlines() if line.startswith("Require PTree.")]
        actual = [line for line in joint.aggregate_after(source).splitlines()
                  if line.startswith("Require PTree.")]
        added = ["Require PTree." + name.replace("/", ".") + "."
                 for name in (joint.EXTERNAL, joint.BRIDGE, joint.TEST)]
        self.assertEqual(actual, sorted(old + added))
        self.assertEqual(len(actual), len(set(actual)))

    def test_frozen_theory_is_byte_exact(self):
        path = "theories/Prob/Backend/Common/DomainTransport.v"
        with self.assertRaises(AssertionError):
            joint.audit_sources(self.before, {**self.after, path: self.after[path] + "\n"})

    def test_no_assumption_or_qlift_induction(self):
        path = "theories/" + joint.BRIDGE + ".v"
        for addition in ["Axiom transport : False.", "Class TransportExists := {}.",
                         "Admitted.", "Inductive Free := Mk.", "induction H.",
                         "elim H.", "Check FOQLComp."]:
            with self.subTest(addition=addition), self.assertRaises(AssertionError):
                joint.audit_sources(self.before, {**self.after, path: self.after[path] + addition})

    def test_no_new_logical_axiom(self):
        with self.assertRaises(AssertionError):
            joint.check_answer("free_omega_qlift_sound", "True", "Axioms:\ntransport_existence : False")

    def test_independent_external_layer(self):
        path = "theories/" + joint.EXTERNAL + ".v"
        with self.assertRaises(AssertionError):
            joint.audit_sources(self.before, {**self.after, path: self.after[path] + "Check FreeOmega."})

    def test_one_way_validation(self):
        for adapter in [joint.EXTERNAL, joint.BRIDGE]:
            self.assertTrue(architecture.external_validation(adapter))
            for source in ["Eq/PEutt", "Prob/Backend/SubEnum/Measure",
                           "API/FreeOmega", "Examples/RandomWalk"]:
                self.assertFalse(architecture.permitted(source, adapter))
        self.assertEqual(architecture.ownership(joint.EXTERNAL)[1], "external validation")
        self.assertTrue(architecture.permitted(joint.EXTERNAL, "Prob/Domain/CountableTransport"))
        self.assertTrue(architecture.permitted(joint.EXTERNAL, "Prob/Backend/Common/DomainTransport"))
        self.assertTrue(architecture.permitted(joint.BRIDGE, joint.EXTERNAL))
        self.assertFalse(architecture.permitted(joint.EXTERNAL, "Prob/Backend/SubEnum/Measure"))
        self.assertFalse(architecture.permitted("Prob/Domain/Coupling", joint.EXTERNAL))
        self.assertFalse(architecture.permitted("Prob/Backend/Common/RealTransport", joint.EXTERNAL))


if __name__ == "__main__":
    unittest.main()
