(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition MDPFragment.

(** The unary fragment does not depend on the tree behavioral relation. *)
Fail Check PTree.Eq.PEutt.peutt.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum rat.
Require Import PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.Measure.
From PTree.Regression.Backend Require Import SubEnumRegression.
From PTree.Regression.Probability Require Import CorrelatedSampleAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum.
#[local] Open Scope ring_scope.

Variant decisionE : Type -> Type :=
  | Ask : decisionE unit
  | Reply : bool -> decisionE unit.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation good := (@mdp_head decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).
Local Notation state := (@mdp_state decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).
Local Notation hits t out := (@ptree_stable_hitting decisionE SubEnum MF FI
  FreeOmegaMixedMeasure FO unit (observe t) out).

Lemma dirac_head_total (h : stable_head decisionE SubEnum unit) :
  @sem_total MF FI FO _ (FORet h).
Proof.
  apply free_omega_observable_total_intro.
  exists unit, (fun _ => tt), (subenum_ret tt). split; [constructor|].
  native_compute. reflexivity.
Qed.

Lemma fair_heads_total (f : bool -> stable_head decisionE SubEnum unit) :
  @sem_total MF FI FO _ (FOSample subenum_fair (fun b => FORet (f b))).
Proof.
  apply free_omega_observable_total_intro.
  exists unit, (fun _ => tt),
    (subenum_bind subenum_fair (fun _ => subenum_ret tt)).
  split.
  - change (free_omega_observes (NI := SubEnum_SemanticMeasure)
      (fun _ => tt) (FOSample subenum_fair (fun b => FORet (f b)))
      (@sem_bind SubEnum SubEnum_SemanticMeasure _ _ subenum_fair
        (fun _ => subenum_ret tt))).
    eapply FOOObserveSample. intro b. constructor.
  - native_compute. reflexivity.
Qed.

Definition leaf b : ptree decisionE SubEnum unit := Vis (Reply b) (fun _ => Ret tt).
Definition leaf_head b : stable_head decisionE SubEnum unit :=
  FHVis (Reply b) (fun _ => Ret tt).
Definition hidden_choice := Prob subenum_fair leaf.
Definition hidden_front := FOSample subenum_fair (fun b => FORet (leaf_head b)).
Definition decision := Vis Ask (fun _ => hidden_choice).

Lemma leaf_head_mdp b : good (leaf_head b).
Proof.
  apply (proj2 (mdp_head_vis_iff (Reply b) _)). intro x.
  exists (FORet (FHRet tt)). split.
  - apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)).
  - split; [apply dirac_head_total|]. constructor. apply mdp_head_ret.
Qed.

Lemma hidden_choice_hitting : hits hidden_choice hidden_front.
Proof.
  eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

(** The continuation is a non-Dirac distribution of states. This is
    exactly the discipline of a probabilistic state transition. *)
Theorem visible_sample_visible_is_mdp : state decision.
Proof.
  apply mdp_state_vis. intro x. exists hidden_front. split.
  - apply hidden_choice_hitting.
  - split; [apply fair_heads_total|].
    eapply FOAESample with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros b _. constructor. apply leaf_head_mdp.
Qed.

Example delayed_decision_is_mdp : state (Tau (Tau decision)).
Proof. rewrite !mdp_state_tau_iff. apply visible_sample_visible_is_mdp. Qed.

Example leaf_heads_inequivalent :
  ~ @head_bisim decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq
      (leaf_head true) (leaf_head false).
Proof. intro H. apply head_bisim_unfold in H. dependent destruction H. Qed.

(** A genuine negation, not a failed tactic: support transport would force
    both distinct visible heads to equal the same Dirac head. The argument
    is backend-qualified; no generic Dirac separation axiom is assumed. *)
Theorem hidden_choice_not_mdp_state : ~ state hidden_choice.
Proof.
  intro H. apply (proj1 (mdp_state_hitting_iff hidden_choice_hitting)) in H.
  destruct H as [h [Heq Hgood]].
  change (free_omega_qlift eq hidden_front (FORet h)) in Heq.
  assert (Hsingle : free_omega_ae (fun y => y = h) (FORet h)).
  { constructor. reflexivity. }
  pose proof (proj2 (free_omega_qlift_support Heq) _ Hsingle) as Hsupport.
  apply free_omega_ae_sample_inv in Hsupport.
  destruct (exchange_fair_both_values Hsupport) as [Htrue Hfalse].
  dependent destruction Htrue. dependent destruction Hfalse.
  destruct H as [y [Heq1 Heq2]].
  destruct H0 as [z [Heq3 Heq4]].
  assert (leaf_head true = leaf_head false) by congruence.
  discriminate.
Qed.

Example successor_need_not_be_a_state :
  state decision /\ ~ state hidden_choice.
Proof. split; [apply visible_sample_visible_is_mdp|apply hidden_choice_not_mdp_state]. Qed.

(** Infinite interaction with a fresh random visible state after every
    response. This exercises the unary GFP, not just finite constructors. *)
CoFixpoint service b : ptree decisionE SubEnum unit :=
  Vis (Reply b) (fun _ => Prob subenum_fair service).
Definition service_head b : stable_head decisionE SubEnum unit :=
  FHVis (Reply b) (fun _ => Prob subenum_fair service).

Lemma service_hitting b : hits (service b) (FORet (service_head b)).
Proof.
  change (hits (Vis (Reply b) (fun _ => Prob subenum_fair service))
    (FORet (service_head b))).
  apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
Qed.

Theorem service_head_mdp b : good (service_head b).
Proof.
  eapply mdp_head_coinduction with (P := fun h => exists b, h = service_head b).
  - intros h [c ->]. intro x.
    exists (FOSample subenum_fair (fun d => FORet (service_head d))).
    split.
    + constructor. eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
        (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros d _. apply service_hitting.
    + split; [apply fair_heads_total|].
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros d _. constructor. exists d. reflexivity.
  - exists b. reflexivity.
Qed.

Theorem infinite_service_mdp b : state (service b).
Proof.
  eapply mdp_state_of_hitting; [apply service_hitting| |apply service_head_mdp].
  apply (@sem_eq_refl MF FI FC).
Qed.
