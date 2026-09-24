"""Ownership and transitive architecture boundary contracts."""
import unittest
import audit_architecture as architecture


class ArchitectureTests(unittest.TestCase):
    def test_runner_validation_is_one_way(self):
        bridge = "Execution/Validation/SubEnumQ"
        self.assertTrue(architecture.external_validation(bridge))
        for dep in ["Execution/Backend/UniformReplay", "Eq/Backend/StableHittingDomainSubEnumQ",
                    "Prob/Domain/Expectation"]:
            self.assertTrue(architecture.permitted(bridge, dep))
        for owner in ["Core/PTreeDefinition", "Execution/Runner", "Execution/Backend/RationalTickets",
                      "Eq/PEutt", "Interp/State", "Examples/RationalState"]:
            self.assertFalse(architecture.permitted(owner, bridge))
        graph = {"Execution/Runner": {"Execution/Backend/Hidden"},
                 "Execution/Backend/Hidden": {bridge}, bridge: set()}
        with self.assertRaises(AssertionError):
            architecture.check_external_validation_boundary(graph)

    def test_native_rational_backends_do_not_import_legacy(self):
        for owner in ['Prob/Backend/EnumQ/Representation', 'Prob/Backend/SubEnumQ/Measure',
                      'Prob/Backend/SubEnumR/Representation', 'Prob/Backend/Common/FiniteEnum']:
            for legacy in ['Prob/Legacy/RatSubTypes', 'Prob/Legacy/RationalDiscrete']:
                with self.subTest(owner=owner, legacy=legacy):
                    self.assertFalse(architecture.permitted(owner, legacy))

    def test_mathcomp_native_excludes_completion(self):
        self.assertFalse(architecture.permitted('Prob/Backend/MathComp/Measure',
                                               'Prob/FreeOmega/Definition'))
        with self.assertRaises(AssertionError):
            architecture.ownership('Prob/Backend/MathComp/FreeOmega/Replacement')
        graph = {'Prob/Backend/MathComp/Measure': {'Prob/Backend/Common/Helper'},
                 'Prob/Backend/Common/Helper': {'Prob/FreeOmega/Definition'},
                 'Prob/FreeOmega/Definition': set()}
        with self.assertRaises(AssertionError):
            architecture.check_mathcomp_native_boundary(graph)

    def test_mathcomp_completion_source_guards(self):
        for bad in ['Definition MathCompBehaviorMeasure := Something.',
                    'Check FreeOmega (MathCompKernelMeasure R).',
                    'Let Node := MathCompKernelMeasure R.\nCheck FreeOmega Node.',
                    'Local Notation MN := (MathCompKernelMeasure R).\nCheck FreeOmegaAt MN A.',
                    'Definition Node := MathCompKernelMeasure R.\nLet Other := Node.\nCheck FreeOmega Other.']:
            with self.subTest(bad=bad), self.assertRaises(AssertionError):
                architecture.check_mathcomp_native_sources({'Regression/Probe': bad})
        with self.assertRaises(AssertionError):
            architecture.check_mathcomp_native_sources({'Prob/Backend/MathComp/Measure':
                'From PTree.Prob.FreeOmega Require Import Definition.'})
        architecture.check_mathcomp_native_sources({'Eq/Generic':
            'Context (MN : Type -> Type).\nCheck FreeOmega MN.'})

    def test_real_joint_realization_is_concrete_validation(self):
        bridge = "Prob/Backend/SubEnumR/FreeOmega/JointRealization"
        generic = "Prob/FreeOmega/Validation/Quotient"
        self.assertTrue(architecture.external_validation(bridge))
        self.assertTrue(architecture.permitted(bridge, generic))
        self.assertFalse(architecture.permitted(generic, bridge))
        for source in ["Core/PTreeDefinition", "Eq/PEutt", "Semantics/MDPFragment",
                       "API/FreeOmega", "Examples/RandomWalk",
                       "Prob/Backend/SubEnumR/Measure"]:
            self.assertFalse(architecture.permitted(source, bridge))

        cover = "Prob/Backend/SubEnumR/FreeOmega/CountableSupport"
        self.assertTrue(architecture.external_validation(cover))
        self.assertTrue(architecture.permitted(bridge, cover))
        self.assertFalse(architecture.permitted("Prob/Backend/SubEnumR/Measure", cover))

    def test_all_reasoning_layers_exclude_indirect_validation(self):
        for root in ["Core/PTreeDefinition", "Eq/PStrong", "Semantics/MDPFragment",
                     "PTree", "Semantics"]:
            with self.subTest(root=root):
                graph = {root: {"Prob/Backend/SubEnumR/Measure"},
                         "Prob/Backend/SubEnumR/Measure": {"Prob/Domain/Expectation"},
                         "Prob/Domain/Expectation": set()}
                with self.assertRaises(AssertionError):
                    architecture.check_external_validation_boundary(graph)

    def test_explicit_eq_validation_adapter_is_not_reasoning_root(self):
        graph = {"Eq/Backend/StableHittingDomainSubEnumQ": {"Prob/Domain/Expectation"},
                 "Prob/Domain/Expectation": set(), "Eq/PEutt": set()}
        architecture.check_external_validation_boundary(graph)
        graph["Eq/PEutt"] = {"Eq/Backend/StableHittingDomainSubEnumQ"}
        with self.assertRaises(AssertionError):
            architecture.check_external_validation_boundary(graph)

    def test_relational_validation_adapters_are_one_way(self):
        for family in ["SubEnumQ", "SubEnumR"]:
            bridge = f"Prob/Backend/{family}/FreeOmega/RelationalValidation"
            self.assertTrue(architecture.external_validation(bridge))
            self.assertTrue(architecture.permitted(bridge, "Prob/FreeOmega/Validation/Quotient"))
            for source in [f"Prob/Backend/{family}/Measure", "API/FreeOmega",
                           "Eq/PEutt", "Examples/RandomWalk"]:
                self.assertFalse(architecture.permitted(source, bridge))

    def test_generic_completion_validation_is_one_way(self):
        bridge = "Prob/FreeOmega/Validation/Expectation"
        self.assertTrue(architecture.external_validation(bridge))
        self.assertTrue(architecture.permitted(bridge, "Prob/Domain/Expectation"))
        self.assertTrue(architecture.permitted(bridge, "Prob/FreeOmega/Definition"))
        for target in ["Prob/Backend/SubEnumQ/Domain", "Prob/Backend/MathComp/Domain",
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
                           "Core/PTreeDefinition", "Eq/PEutt", "Prob/Backend/SubEnumQ/Measure"]:
            self.assertFalse(architecture.permitted(domain, dependency))
        self.assertTrue(architecture.permitted("Prob/Domain/MeasureModel", domain))

    def test_external_validation_is_not_mainline_infrastructure(self):
        for source in ["Eq/PEutt", "API/Generic", "Examples/RandomWalk",
                       "Interp/FreeOmega/Guarded", "Prob/Backend/SubEnumQ/Measure",
                       "Prob/Legacy/Discrete", "Semantics/MDPFragment"]:
            for target in ["Prob/Domain/Expectation",
                           "Prob/Backend/SubEnumQ/FreeOmega/DomainSoundness",
                           "Prob/Backend/SubEnumQ/FreeOmega/QuotientSoundness",
                           "Prob/Backend/SubEnumQ/FreeOmega/CountableSupport",
                           "Prob/Backend/SubEnumQ/FreeOmega/CouplingSoundness",
                           "Eq/Backend/StableHittingDomainSubEnumQ"]:
                self.assertFalse(architecture.permitted(source, target))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnumQ/Domain", "Prob/Domain/Expectation"))
        self.assertTrue(architecture.permitted("Regression/Probability/OmegaVal", "Prob/Domain/Expectation"))

    def test_external_boundary_checks_transitive_closure(self):
        graph = {"Examples/RandomWalk": {"Prob/Backend/SubEnumQ/Measure"},
                 "Prob/Backend/SubEnumQ/Measure": {"Prob/Backend/SubEnumQ/Domain"},
                 "Prob/Backend/SubEnumQ/Domain": {"Prob/Domain/Expectation"},
                 "Prob/Domain/Expectation": set()}
        with self.assertRaises(AssertionError):
            architecture.check_external_validation_boundary(graph)
        graph["Prob/Backend/SubEnumQ/Measure"] = set()
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

    def test_semantic_subenumQ_endpoint_is_concrete_backend(self):
        self.assertEqual(architecture.ownership("Semantics/Backend/MDPEmbeddingSubEnumQ"),
                         ("Semantics/Backend", "SubEnumQ",
                          "retain comparison semantics; not canonical equality"))

    def test_interpretation_is_freeomega_qualified(self):
        self.assertEqual(architecture.ownership("Interp/FreeOmega/MDP")[:2],
                         ("Interp/FreeOmega", "FreeOmega"))

    def test_tree_cofinality_is_not_measure_infrastructure(self):
        self.assertEqual(architecture.ownership("Eq/Backend/EnumQCofinality")[0],
                         "Eq/Backend")

    def test_forbidden_reverse_dependencies(self):
        for source, target in [
            ("Core/PTreeDefinition", "Prob/Legacy/Monad"),
            ("Prob/FreeOmega/Measure", "Prob/Backend/EnumQ/Measure"),
            ("Eq/FreeOmega/Bind", "Interp/FreeOmega/Cofinality"),
            ("Eq/PEutt", "Eq/FreeOmega/Bind"),
            ("Semantics/MDPFragment", "Semantics/FreeOmega/MDPCoincidenceFreeOmega"),
            ("Semantics/MDPFragment", "Interp/FreeOmega/MDP"),
            ("Interp/FreeOmega/MDP", "Interp/Backend/SubEnumQ"),
            ("Eq/PEutt", "Regression/Semantics/PEuttAlgebra"),
            ("Examples/RandomWalk", "Regression/Backend/SubEnumQRegression"),
        ]:
            with self.subTest(source=source, target=target):
                self.assertFalse(architecture.permitted(source, target))

    def test_allowed_interpreter_comparison_direction(self):
        self.assertTrue(architecture.permitted("Interp/FreeOmega/MDP", "Semantics/MDPFragment"))

    def test_probability_native_axis_and_canonical_boundary(self):
        self.assertFalse(architecture.permitted("Prob/Backend/SubEnumR/Representation", "Prob/Domain/Expectation"))
        self.assertFalse(architecture.permitted("Prob/Backend/SubEnumR/Measure", "Prob/Backend/SubEnumQ/Measure"))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnumR/Domain", "Prob/Domain/Expectation"))
        self.assertEqual(architecture.ownership("Prob/FreeOmega/Measure")[:2],
                         ("Prob/FreeOmega", "FreeOmega"))
        self.assertEqual(architecture.ownership("Prob/Backend/SubEnumQ/FreeOmega/Total")[:2],
                         ("Prob/Backend/SubEnumQ/FreeOmega", "SubEnumQ"))
        for m in ["Prob/Backend/FreeOmega/TotalSubEnumQ", "Prob/Backend/TwoLevelMeasureEnumQ"]:
            with self.assertRaises(AssertionError):
                architecture.ownership(m)
        for m, d in [("Prob/Backend/Common/FiniteMatching", "Prob/Backend/EnumQ/Measure"),
                     ("Prob/Backend/MathComp/Measure", "Prob/Backend/SubEnumQ/Measure"),
                     ("Prob/Backend/EnumQ/Measure", "Prob/Backend/MathComp/Measure")]:
            self.assertFalse(architecture.permitted(m, d))
        self.assertTrue(architecture.permitted("Prob/Backend/SubEnumQ/Measure", "Prob/Backend/EnumQ/Measure"))

    def test_unknown_experiment_requires_review(self):
        with self.assertRaises(AssertionError):
            architecture.ownership("Experimental/UnreviewedTheory")


class AggregateAndFixtureTests(unittest.TestCase):
    def test_execution_is_not_a_probability_model_or_theory_dependency(self):
        self.assertEqual(architecture.ownership('Execution/Runner')[:2], ('Execution', 'generic'))
        self.assertTrue(architecture.permitted('Execution/Runner', 'Core/PTreeDefinition'))
        self.assertTrue(architecture.permitted('Execution/Backend/SubEnumQ', 'Prob/Backend/SubEnumQ/Representation'))
        self.assertTrue(architecture.permitted('Examples/StateCounter', 'Execution/Runner'))
        for source in ['Core/Fold', 'Eq/PEutt', 'Interp/State', 'Prob/Backend/SubEnumQ/Measure']:
            self.assertFalse(architecture.permitted(source, 'Execution/Runner'))
        for target in ['Prob/Domain/Expectation', 'Prob/FreeOmega/Measure',
                       'Eq/PEutt', 'Execution/Backend/SubEnumQ']:
            self.assertFalse(architecture.permitted('Execution/Runner', target))
        self.assertFalse(architecture.permitted('Execution/Backend/SubEnumQ', 'Prob/Backend/SubEnumQ/Domain'))

    def test_sorted_complete_aggregate(self):
        architecture.aggregate_check(['PTree.A','PTree.B'], ['PTree.B','PTree.A'])

    def test_bad_aggregate(self):
        for actual in [['PTree.A'], ['PTree.B','PTree.A'], ['PTree.A','PTree.A','PTree.B']]:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                architecture.aggregate_check(actual,['PTree.A','PTree.B'])

    def test_fixture_has_no_final_regression_dependency(self):
        source='Regression/Fixtures/FreeOmegaSamples'
        self.assertFalse(architecture.permitted(source,'Regression/Probability/FreeOmegaSoundness'))
        self.assertTrue(architecture.permitted(source,'Prob/Backend/SubEnumQ/FreeOmega/DomainSoundness'))
        self.assertTrue(architecture.permitted('Regression/Probability/CountableCoupling',source))

    def test_native_validation_has_no_completion_dependency(self):
        edges={'Prob/Backend/SubEnumQ/Domain': {'Prob/Backend/SubEnumQ/Expectation'},
               'Prob/Backend/SubEnumQ/Expectation': {'Prob/Backend/SubEnumQ/FreeOmega/UpperExpectation'},
               'Prob/Backend/SubEnumQ/FreeOmega/UpperExpectation':set()}
        with self.assertRaises(AssertionError):
            architecture.check_native_expectation_boundary(edges)
        edges['Prob/Backend/SubEnumQ/Expectation']=set()
        architecture.check_native_expectation_boundary(edges)

    def test_final_joint_adapter_stays_external(self):
        for target in ['Prob/Backend/Common/CountableCoupling',
                       'Prob/Backend/SubEnumQ/FreeOmega/JointSoundness']:
            self.assertTrue(architecture.external_validation(target))
            for source in ['API/FreeOmega','Eq/PEutt','Examples/RandomWalk',
                           'Prob/Backend/SubEnumQ/Measure']:
                self.assertFalse(architecture.permitted(source,target))
        self.assertFalse(architecture.permitted('Prob/Domain/Coupling','Prob/Backend/Common/DomainTransport'))
        self.assertTrue(architecture.permitted('Prob/Backend/Common/CountableCoupling','Prob/Domain/CountableTransport'))


if __name__=='__main__':
    unittest.main()
