(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.

(** No behavioral-equality module is loaded by the new GFP. *)
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Regression.Semantics Require Import TreeTransition.
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
Local Notation bisim := (@tree_trans_bisim rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation generator := (@tree_trans_bisimF rawE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool bool eq).
Local Notation trans := (@tree_trans rawE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool).

Example successor_relation_is_raw_tree_candidate (sim : tree -> tree -> Prop)
    {X} (e : rawE X) k l :
  tree_trans_head_rel sim (FHVis e k) (FHVis e l) <-> sim (Vis e k) (Vis e l).
Proof. reflexivity. Qed.

Example return_reflexive b : bisim (Ret b) (Ret b).
Proof. apply tree_trans_bisim_refl. Qed.
Example empty_event_reflexive : bisim deadA deadA.
Proof. apply tree_trans_bisim_refl. Qed.
Example fold_unfold_regression t u : bisim t u <-> generator bisim t u.
Proof. split; [apply tree_trans_bisim_unfold|apply tree_trans_bisim_fold]. Qed.

(** Ret is observed now, not only after a future action. No generic Dirac
    injectivity is postulated: this negative result uses SubEnumQ/FreeOmega. *)
Theorem distinct_returns_not_tree_trans_bisim : ~ bisim (Ret true) (Ret false).
Proof.
  intro H.
  assert (Hobs : @sem_lift MF FI bool bool eq (FORet true) (FORet false)).
  { refine (tree_trans_bisim_return_observations H _ _);
      apply (tree_return_ret (FI := FI) (FO := FO)). }
  assert (Htrue : free_omega_ae (NI := SubEnumQ_SemanticMeasure)
    (fun b => b = true) (FORet true)).
  { constructor. reflexivity. }
  pose proof (proj1 (free_omega_qlift_support Hobs) _ Htrue) as Hfalse.
  dependent destruction Hfalse. destruct H0 as [b [-> Hbad]]. discriminate.
Qed.

Theorem boolean_returns_tree_trans_bisim_iff b c : bisim (Ret b) (Ret c) <-> b = c.
Proof.
  split; [|intros ->; apply return_reflexive].
  destruct b, c; try reflexivity.
  - intro H. exfalso. exact (distinct_returns_not_tree_trans_bisim H).
  - intro H.
    assert (Hobs : @sem_lift MF FI bool bool eq (FORet false) (FORet true)).
    { refine (tree_trans_bisim_return_observations H _ _);
        apply (tree_return_ret (FI := FI) (FO := FO)). }
    assert (Hfalse : free_omega_ae (NI := SubEnumQ_SemanticMeasure)
      (fun b => b = false) (FORet false)).
    { constructor. reflexivity. }
    pose proof (proj1 (free_omega_qlift_support Hobs) _ Hfalse) as Htrue.
    dependent destruction Htrue. destruct H0 as [b [-> Hbad]]. discriminate.
Qed.

(** Even the FULL bidirectional action-only test identifies these trees,
    for all witnesses, not merely for the exhibited zero representatives. *)
Theorem empty_events_action_only_match label :
  tree_measure_match (FI := FI) (tree_trans_head_rel (@eq tree))
    (trans deadA label) (trans deadB label).
Proof.
  split; intros out Hout; exists FOZero.
  - split; [apply empty_b_action_zero|].
    eapply sem_lift_mono; [|exact (tree_trans_unique Hout (empty_a_action_zero label))].
    intros h k ->. reflexivity.
  - split; [apply empty_a_action_zero|].
    eapply sem_lift_mono; [|exact (tree_trans_unique (empty_b_action_zero label) Hout)].
    intros h k ->. reflexivity.
Qed.

(** Offered-event matching prevents exactly that collapse in the full GFP. *)
Theorem empty_events_not_tree_trans_bisim : ~ bisim deadA deadB.
Proof.
  intro H. apply empty_offers_distinct.
  exact (tree_trans_bisim_offered_observations H empty_a_observation empty_b_observation).
Qed.
