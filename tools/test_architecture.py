"""Ownership and transitive architecture boundary contracts."""
import unittest
import audit_architecture as architecture


class ArchitectureTests(unittest.TestCase):
    def test_generic_completion_validation_is_one_way(self):
        bridge = "Prob/FreeOmega/Validation/Expectation"
        self.assertTrue(architecture.external_validation(bridge))
        self.assertTrue(architecture.permitted(bridge, "Prob/Domain/Expectation"))
        self.assertTrue(architecture.permitted(bridge, "Prob/FreeOmega/Definition"))
        for target in ["Prob/Backend/SubEnum/Domain", "Prob/Backend/MathComp/Domain",
                       "Core/PTreeDefinition"]:
            self.assertFalse(architecture.permitted(bridge, target))
        for source in ["Prob/Domain/Expectation", "Prob/FreeOmega/Measure",
                       "API/FreeOmega", "Eq/PEutt", "Examples/RandomWalk"]:
            self.assertFalse(architecture.permitted(source, bridge))

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
                           "Prob/Backend/SubEnum/FreeOmega/QuotientSoundness",
                           "Prob/Backend/SubEnum/FreeOmega/CountableSupport",
                           "Prob/Backend/SubEnum/FreeOmega/CouplingSoundness",
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
        self.assertFalse(architecture.permitted("Prob/Backend/SubEnumR/Representation", "Prob/Domain/Expectation"))
        self.assertFalse(architecture.permitted("Prob/Backend/SubEnumR/Measure", "Prob/Backend/SubEnum/Measure"))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnumR/Domain", "Prob/Domain/Expectation"))
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


class AggregateAndFixtureTests(unittest.TestCase):
    def test_sorted_complete_aggregate(self):
        architecture.aggregate_check(['PTree.A','PTree.B'], ['PTree.B','PTree.A'])

    def test_bad_aggregate(self):
        for actual in [['PTree.A'], ['PTree.B','PTree.A'], ['PTree.A','PTree.A','PTree.B']]:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                architecture.aggregate_check(actual,['PTree.A','PTree.B'])

    def test_fixture_has_no_final_regression_dependency(self):
        source='Regression/Fixtures/FreeOmegaSamples'
        self.assertFalse(architecture.permitted(source,'Regression/Probability/FreeOmegaSoundness'))
        self.assertTrue(architecture.permitted(source,'Prob/Backend/SubEnum/FreeOmega/DomainSoundness'))
        self.assertTrue(architecture.permitted('Regression/Probability/CountableCoupling',source))

    def test_native_validation_has_no_completion_dependency(self):
        edges={'Prob/Backend/SubEnum/Domain': {'Prob/Backend/SubEnum/Expectation'},
               'Prob/Backend/SubEnum/Expectation': {'Prob/Backend/SubEnum/FreeOmega/UpperExpectation'},
               'Prob/Backend/SubEnum/FreeOmega/UpperExpectation':set()}
        with self.assertRaises(AssertionError):
            architecture.check_native_expectation_boundary(edges)
        edges['Prob/Backend/SubEnum/Expectation']=set()
        architecture.check_native_expectation_boundary(edges)

    def test_final_joint_adapter_stays_external(self):
        for target in ['Prob/Backend/Common/CountableCoupling',
                       'Prob/Backend/SubEnum/FreeOmega/JointSoundness']:
            self.assertTrue(architecture.external_validation(target))
            for source in ['API/FreeOmega','Eq/PEutt','Examples/RandomWalk',
                           'Prob/Backend/SubEnum/Measure']:
                self.assertFalse(architecture.permitted(source,target))
        self.assertFalse(architecture.permitted('Prob/Domain/Coupling','Prob/Backend/Common/DomainTransport'))
        self.assertTrue(architecture.permitted('Prob/Backend/Common/CountableCoupling','Prob/Domain/CountableTransport'))


if __name__=='__main__':
    unittest.main()
