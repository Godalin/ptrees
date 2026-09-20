(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Interp.FreeOmega Require Import Atomic.
From PTree.Semantics Require Import TreeTransitionBisim.
From PTree.Regression.Semantics Require Import TreeTransitionStrictness InterpExposure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation AH := (atomic_handler (NI := SubEnum_SemanticMeasure)
  (NO := SubEnum_SemanticOmega)).
Local Notation TB := (@tree_trans_bisim correlationE SubEnum MF FI FC
  FreeOmegaMixedMeasure FO bool bool eq).

(** A semantic, not syntactic, one-interaction handler. There are Tau and
    Prob nodes after the event; the sample is Dirac and preserves response. *)
Definition delayed_response {E X} (x : X) : ptree E SubEnum X :=
  Prob (@sem_ret SubEnum SubEnum_SemanticMeasure unit tt) (fun _ => Tau (Ret x)).

Lemma delayed_response_hitting {E X} (x : X) :
  @ptree_stable_hitting E SubEnum MF FI FreeOmegaMixedMeasure FO X
    (observe (delayed_response x)) (FORet (FHRet x)).
Proof.
  assert (Hhit : @ptree_stable_hitting E SubEnum MF FI FreeOmegaMixedMeasure FO X
    (observe (delayed_response x))
    (FOSample (@sem_ret SubEnum SubEnum_SemanticMeasure unit tt)
      (fun _ => FORet (FHRet x)))).
  { eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
    - apply sem_ae_true.
    - intros [] _. apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
      apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)). }
  unfold ptree_stable_hitting, stable_hitting in Hhit |- *.
  eapply FOQLComp with (T := eq) (U := eq); [|exact Hhit|].
  - apply (sem_eq_sym (SI := FI)). apply FOQLSampleRetL.
    + intro P. apply sem_ae_ret_iff.
    + apply (sem_eq_refl (SI := FI)).
  - intros a c [b [-> ->]]. reflexivity.
Qed.

Definition delayed_identity {E} X (e : E X) : ptree E SubEnum X :=
  Tau (Vis e (fun x => delayed_response x)).

Definition delayed_identity_atomic {E} : AH (@delayed_identity E).
Proof.
  refine {| atomic_rename := fun X e => e;
            atomic_unrename := fun X e => e;
            atomic_cont := fun X e x => delayed_response x |}.
  - reflexivity.
  - reflexivity.
  - intros X e. apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
  - intros X e x. apply delayed_response_hitting.
Defined.

(** This source pair is NOT peutt: preservation really uses transition
    bisimulation and cannot be obtained by assuming whole-head coupling. *)
Example atomic_preserves_correlated_pair :
  TB (PTree.interp delayed_identity P) (PTree.interp delayed_identity Q).
Proof.
  exact (tree_trans_bisim_interp_atomic delayed_identity_atomic
    correlated_response_tree_trans_bisim).
Qed.

(** Non-identity label permutation, including events with no responses. *)
Variant swapE : Type -> Type :=
| LeftQuery : swapE bool | RightQuery : swapE bool
| LeftDead : swapE Empty_set | RightDead : swapE Empty_set.
Definition swap_event X (e : swapE X) : swapE X :=
  match e in swapE X return swapE X with
  | LeftQuery => RightQuery | RightQuery => LeftQuery
  | LeftDead => RightDead | RightDead => LeftDead
  end.
Lemma swap_event_involution X (e : swapE X) : swap_event (swap_event e) = e.
Proof. destruct e; reflexivity. Qed.
Definition swapping_handler X (e : swapE X) : ptree swapE SubEnum X :=
  Tau (Vis (swap_event e) (fun x => delayed_response x)).
Definition swapping_handler_atomic : AH swapping_handler.
Proof.
  refine {| atomic_rename := @swap_event;
            atomic_unrename := @swap_event;
            atomic_cont := fun X e x => delayed_response x |}.
  - exact swap_event_involution.
  - exact swap_event_involution.
  - intros X e. apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
  - intros X e x. apply delayed_response_hitting.
Defined.

Example swapping_preserves {R} (RR : R -> R -> Prop) t u :
  @tree_trans_bisim swapE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R RR t u ->
  @tree_trans_bisim swapE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R RR
    (PTree.interp swapping_handler t) (PTree.interp swapping_handler u).
Proof. intro Htu. exact (tree_trans_bisim_interp_atomic swapping_handler_atomic Htu). Qed.

(** Negative boundary: one visible guard is insufficient. No certificate
    in this profile can exist for the accepted two-interaction witness. *)
Theorem two_query_handler_not_atomic : AH two_query_handler -> False.
Proof.
  intro atom. apply (proj2 tree_trans_bisim_interp_counterexample).
  exact (tree_trans_bisim_interp_atomic atom correlated_response_tree_trans_bisim).
Qed.
