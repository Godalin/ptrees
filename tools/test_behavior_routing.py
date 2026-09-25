"""Mutation tests for canonical routing and structural registration boundaries."""
import unittest
from audit_assumptions import ROOT
from audit_api import STRUCTURAL, STRUCTURAL_INSTANCES, REGISTRY, current_surface
import audit_architecture as architecture


class BehaviorRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                       for p in (ROOT/'theories').rglob('*.v')}
        cls.internal = STRUCTURAL_INSTANCES

    def test_whole_suite_not_single_instance(self):
        self.assertEqual(len(self.internal), 10)
        for name in self.internal:
            with self.subTest(name=name), self.assertRaises(AssertionError):
                current_surface({**self.sources, STRUCTURAL: self.sources[STRUCTURAL].replace(
                    '#[local] Polymorphic Instance ' + name,
                    '#[global] Polymorphic Instance ' + name)})

    def test_ordinary_proof_edits_are_not_registry_changes(self):
        current_surface({**self.sources, STRUCTURAL: self.sources[STRUCTURAL] +
                         '\nLemma extra : True. Proof. exact I. Qed.\n'})

    def test_shared_operation_stays_global(self):
        with self.assertRaises(AssertionError):
            current_surface({**self.sources, STRUCTURAL: self.sources[STRUCTURAL].replace(
                '#[global] Polymorphic Instance FreeOmegaMixedMeasure',
                '#[local] Polymorphic Instance FreeOmegaMixedMeasure')})

    def test_registry_exact_and_no_blanket(self):
        current_surface(self.sources)
        for extra in [
            '#[global] Instance any {MN} : CanonicalBehavior MN := builder.',
            'Instance any {MN} : CanonicalBehavior MN := builder.',
            '#[global] Instance any {MN} : PTree.Eq.Canonical.CanonicalBehavior MN := builder.',
            '#[global] Existing Instance FreeOmegaSemanticMeasure.',
            '#[global] Existing Instances FreeOmegaSemanticMeasureCoreLaws FreeOmegaSemanticOmega.',
            '#[global] Existing Instance SubEnumQ_CanonicalBehavior.',
        ]:
            with self.subTest(extra=extra), self.assertRaises(AssertionError):
                current_surface(dict(self.sources, **{'theories/Eq/Extra.v': extra}))
        for path, name in REGISTRY.items():
            with self.subTest(path=path), self.assertRaises(AssertionError):
                changed = dict(self.sources)
                changed[path] += '\n#[global] Instance duplicate : CanonicalBehavior T := builder.\n'
                current_surface(changed)

    def test_no_law_bundle_or_projection_instances(self):
        for mutation in [
            ('behavior_mixed :', 'behavior_laws :'),
            ('behavior_measure :', 'behavior_measure :>'),
        ]:
            changed = dict(self.sources)
            path = 'theories/Eq/Canonical.v'
            changed[path] = changed[path].replace(*mutation)
            with self.subTest(mutation=mutation), self.assertRaises(AssertionError):
                current_surface(changed)

    def test_relation_owner_and_interpretation(self):
        for path, addition in [
            ('theories/Eq/PEutt.v', 'Notation "t ≈ₚ u" := (peutt eq t u) (at level 70).'),
            ('theories/PTreeFacts.v', 'Notation peutt_bind := Bind.peutt_bind.'),
            ('theories/Regression/Infrastructure/PublicBehavior.v', 'From PTree.Interp Require Import IterationUniform.'),
        ]:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                current_surface({**self.sources, path: self.sources[path]+'\n'+addition})
        path = 'theories/Eq/Canonical.v'
        with self.assertRaises(AssertionError):
            current_surface({**self.sources, path: self.sources[path].replace(':= (canonical_peutt ', ':= (peutt ')})

    def test_selector_needs_no_gate_m_reverse_exception(self):
        self.assertTrue(architecture.permitted('Eq/Backend/MathComp/Direct', 'Eq/Canonical'))
        self.assertTrue(architecture.permitted('Eq/PEutt', 'Eq/Canonical'))
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
