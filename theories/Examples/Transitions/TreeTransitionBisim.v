(** Role: supporting program/semantic example, not a flagship claim. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From Coq Require Import RelationClasses Morphisms Setoid.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.

(** No behavioral-equality module is loaded by the new GFP. *)
Fail Check PTree.Eq.PEutt.peutt.

(** Even an abstract native carrier suffices: no native laws, hitting
    existence, BindLaws or OmegaLaws are needed for the equivalence API. *)
Section GenericEquivalence.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI} {R : Type}.
Local Notation TB := (@trans_bisim E MN MF FI FC MX FO R R eq).
Example generic_transition_equivalence : Equivalence TB.
Proof. typeclasses eauto. Qed.
Example generic_transition_symmetry t u : TB t u -> TB u t.
Proof. intro H. symmetry. exact H. Qed.
Example generic_transition_transitivity t u v : TB t u -> TB u v -> TB t v.
Proof. intros Htu Huv. transitivity u; assumption. Qed.
Example generic_transition_rewrite t u v (H : TB t u) : TB t v <-> TB u v.
Proof. setoid_rewrite H. reflexivity. Qed.
End GenericEquivalence.

Section GenericReturnReflection.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{CA : @SemanticMeasureCouplingAELaws MF FI}
  `{D : @SemanticMeasureDiracAELaws MF FI}.
Example generic_heterogeneous_return_reflection {A B} (RR : A -> B -> Prop) a b :
  @trans_bisim E MN MF FI FC MX FO A B RR (Ret a) (Ret b) -> RR a b.
Proof.
  exact (@trans_bisim_ret_inv E MN MF FI FC MX FO A B RR FB FOL FCO CA D a b).
Qed.
End GenericReturnReflection.

Fail Check PTree.Eq.PEutt.peutt.

Require Import PTree.Examples.Transitions.TreeTransition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation tree := (ptree rawE SubEnumQ bool).
Local Notation bisim := (@trans_bisim rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation generator := (@trans_bisimF rawE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool bool eq).

Example successor_relation_is_raw_tree_candidate (sim : tree -> tree -> Prop)
    {X} (e : rawE X) k l :
  trans_head_rel sim (FHVis e k) (FHVis e l) <-> sim (Vis e k) (Vis e l).
Proof. reflexivity. Qed.

Example return_reflexive b : bisim (Ret b) (Ret b).
Proof. apply trans_bisim_refl. Qed.
Example empty_event_reflexive : bisim deadA deadA.
Proof. apply trans_bisim_refl. Qed.
Example fold_unfold_regression t u : bisim t u <-> generator bisim t u.
Proof. split; [apply trans_bisim_unfold|apply trans_bisim_fold]. Qed.
Example concrete_transition_equivalence : Equivalence bisim.
Proof. typeclasses eauto. Qed.

(** Ret is observed now, not only after a future action. Generic reflection
    uses this SubEnumQ/FreeOmega profile's proved Dirac AE/support laws. *)
Theorem distinct_returns_not_trans_bisim : ~ bisim (Ret true) (Ret false).
Proof.
  intro H.
  apply (trans_bisim_ret_inv (D := free_omega_observable_dirac_ae_laws)) in H.
  discriminate.
Qed.

Theorem boolean_returns_trans_bisim_iff b c : bisim (Ret b) (Ret c) <-> b = c.
Proof.
  split.
  - apply (trans_bisim_ret_inv (D := free_omega_observable_dirac_ae_laws)).
  - intros ->; apply return_reflexive.
Qed.

(** Even the FULL bidirectional action-only test identifies these trees,
    for all witnesses, not merely for the exhibited zero representatives. *)
Theorem empty_events_action_only_match label :
  tree_measure_match (FI := FI) (trans_head_rel (@eq tree))
    (trans (FI := FI) (FO := FO) deadA label) (trans (FI := FI) (FO := FO) deadB label).
Proof.
  split; intros out Hout; exists FOZero.
  - split; [apply empty_b_action_zero|].
    eapply sem_lift_mono; [|exact (trans_unique Hout (empty_a_action_zero label))].
    intros h k ->. reflexivity.
  - split; [apply empty_a_action_zero|].
    eapply sem_lift_mono; [|exact (trans_unique (empty_b_action_zero label) Hout)].
    intros h k ->. reflexivity.
Qed.

(** Offered-event matching prevents exactly that collapse in the full GFP. *)
Theorem empty_events_not_trans_bisim : ~ bisim deadA deadB.
Proof.
  intro H. apply empty_offers_distinct.
  exact (trans_bisim_offered_observations H empty_a_observation empty_b_observation).
Qed.
