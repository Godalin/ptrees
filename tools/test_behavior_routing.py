"""Mutation tests for canonical routing and structural registration boundaries."""
import unittest
from audit_assumptions import ROOT
from audit_behavior_routing import (STRUCTURAL, REGISTRY, frozen, structural_check,
                                    registry_check)
import audit_architecture as architecture


class BehaviorRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = frozen(STRUCTURAL)
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}
        cls.internal = structural_check(cls.old, cls.sources[STRUCTURAL])

    def test_whole_suite_not_single_instance(self):
        self.assertEqual(len(self.internal), 10)
        for name in self.internal:
            with self.subTest(name=name), self.assertRaises(AssertionError):
                structural_check(self.old, self.sources[STRUCTURAL].replace(
                    '#[local] Polymorphic Instance ' + name,
                    '#[global] Polymorphic Instance ' + name))

    def test_proof_edits_are_not_registration_cleanup(self):
        with self.assertRaises(AssertionError):
            structural_check(self.old, self.sources[STRUCTURAL] + '\nLemma extra : True. Proof. exact I. Qed.\n')

    def test_shared_operation_stays_global(self):
        with self.assertRaises(AssertionError):
            structural_check(self.old, self.sources[STRUCTURAL].replace(
                '#[global] Polymorphic Instance FreeOmegaMixedMeasure',
                '#[local] Polymorphic Instance FreeOmegaMixedMeasure'))

    def test_registry_exact_and_no_blanket(self):
        registry_check(self.sources, self.internal)
        for extra in [
            '#[global] Instance any {MN} : CanonicalBehavior MN := builder.',
            'Instance any {MN} : CanonicalBehavior MN := builder.',
            '#[global] Instance any {MN} : PTree.API.Behavior.CanonicalBehavior MN := builder.',
            '#[global] Existing Instance FreeOmegaSemanticMeasure.',
            '#[global] Existing Instances FreeOmegaSemanticMeasureCoreLaws FreeOmegaSemanticOmega.',
            '#[global] Existing Instance SubEnumQ_CanonicalBehavior.',
        ]:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                registry_check(dict(self.sources, **{'theories/API/Extra.v': extra}), self.internal)
        for path, name in REGISTRY.items():
            with self.subTest(path=path), self.assertRaises(AssertionError):
                changed = dict(self.sources)
                changed[path] += '\n#[global] Instance duplicate : CanonicalBehavior T := builder.\n'
                registry_check(changed, self.internal)

    def test_no_law_bundle_or_projection_instances(self):
        for mutation in [
            ('behavior_mixed :', 'behavior_laws :'),
            ('behavior_measure :', 'behavior_measure :>'),
        ]:
            changed = dict(self.sources)
            path = 'theories/API/Behavior.v'
            changed[path] = changed[path].replace(*mutation)
            with self.subTest(mutation=mutation), self.assertRaises(AssertionError):
                registry_check(changed, self.internal)

    def test_gate_m_selector_exception_is_exact(self):
        self.assertTrue(architecture.permitted('Eq/Backend/MathComp/Direct', 'API/Behavior'))
        for source, target in [
            ('Eq/PEutt', 'API/Behavior'),
            ('Eq/Backend/MathComp/Direct', 'API/SubEnumQ'),
            ('Eq/Backend/MathComp/Other', 'API/Behavior'),
            ('API/Behavior', 'Eq/Backend/MathComp/Direct'),
            ('API/FreeOmega', 'Eq/Backend/MathComp/Direct'),
        ]:
            with self.subTest(source=source, target=target):
                self.assertFalse(architecture.permitted(source, target))


if __name__ == '__main__':
    unittest.main()
