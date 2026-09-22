(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Interp.FreeOmega Require Import Guarded.
From PTree.Regression.Backend Require Import SubEnumQRegression.
From PTree.Regression.Semantics Require Import TreeTransitionStrictness InterpExposure.
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
Local Notation GH := (guarded_handler (NI := SubEnumQ_SemanticMeasure)
  (NO := SubEnumQ_SemanticOmega)).
Local Notation guard_from_hitting := (guarded_handler_of_hitting
  (NI := SubEnumQ_SemanticMeasure) (NC := SubEnumQ_SemanticMeasureCoreLaws)
  (NO := SubEnumQ_SemanticOmega) (NCAE := SubEnumQ_SemanticMeasureCouplingAELaws)
  (NCount := SubEnumQ_SemanticMeasureCountableAELaws)).
Local Notation W := (@peutt correlationE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation TB := (@TreeTransitionBisim.tree_trans_bisim correlationE SubEnumQ MF FI FC
  FreeOmegaMixedMeasure FO bool bool eq).
Local Notation hits t out := (@ptree_stable_hitting correlationE SubEnumQ MF FI
  FreeOmegaMixedMeasure FO bool (observe t) out).

Lemma two_query_handler_guarded : GH two_query_handler.
Proof.
  apply guard_from_hitting. intros X e. destruct e.
  exists (FORet (FHVis Query (fun _ => Vis Query (fun x => Ret x)))).
  split; [exact two_query_handler_first_hitting|constructor; exact I].
Qed.

(** The SAME handler preserves peutt but not tree_trans_bisim. The source
    transition counterexample is not incorrectly assumed to be peutt. *)
Theorem two_query_peutt_preservation t u : W t u ->
  W (PTree.interp two_query_handler t) (PTree.interp two_query_handler u).
Proof. intro Htu. exact (peutt_interp_guarded two_query_handler_guarded Htu). Qed.

Theorem two_query_compositionality_contrast :
  GH two_query_handler /\
  (forall t u, W t u -> W (PTree.interp two_query_handler t) (PTree.interp two_query_handler u)) /\
  (TB P Q /\ ~ TB (PTree.interp two_query_handler P) (PTree.interp two_query_handler Q)).
Proof.
  split; [exact two_query_handler_guarded|].
  split; [exact two_query_peutt_preservation|exact tree_trans_bisim_interp_counterexample].
Qed.

#[local] Instance two_query_interp_Proper :
  Proper (W ==> W) (@PTree.interp correlationE correlationE SubEnumQ two_query_handler bool).
Proof. exact (peutt_interp_guarded_Proper two_query_handler_guarded). Qed.

Example guarded_interp_setoid_rewrite t u (H : W t u) :
  W (PTree.interp two_query_handler t) (PTree.interp two_query_handler u).
Proof. setoid_rewrite H. reflexivity. Qed.

(** Internal divergence has empty stable support and is allowed. *)
CoFixpoint handler_spin : ptree correlationE SubEnumQ bool := Tau handler_spin.
Lemma handler_spin_hitting_zero : hits handler_spin FOZero.
Proof.
  assert (Hzero : forall n,
    @ptree_hitting_approx correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool
      n (observe handler_spin) = FOZero).
  { intro n. induction n as [|n IH]; [reflexivity|].
    change (@ptree_hitting_approx correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool
      n (observe handler_spin) = FOZero). exact IH. }
  unfold ptree_stable_hitting, stable_hitting.
  eapply (sem_lub_chain_proper (SI := FI) (SO := FO)) with (chain := fun _ => FOZero).
  - intro n. change (@sem_eq MF FI _ FOZero
      (@ptree_hitting_approx correlationE SubEnumQ MF FI FreeOmegaMixedMeasure FO bool
        n (observe handler_spin))).
    rewrite Hzero. apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.

Definition sample_or_diverge_handler X (e : correlationE X) : ptree correlationE SubEnumQ X :=
  match e in correlationE X return ptree correlationE SubEnumQ X with
  | Query => Prob subenumQ_fair (fun b : bool => if b then Tau (two_query_handler Query) else handler_spin)
  end.

Lemma sample_or_diverge_handler_guarded : GH sample_or_diverge_handler.
Proof.
  apply guard_from_hitting. intros X e. destruct e.
  exists (FOSample subenumQ_fair (fun b : bool => if b then
    FORet (FHVis Query (fun _ => Vis Query (fun x => Ret x))) else FOZero)).
  split.
  - eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros [] _.
      * apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
        exact two_query_handler_first_hitting.
      * exact handler_spin_hitting_zero.
  - eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros [] _; [constructor; exact I|constructor].
Qed.

Example probabilistic_partial_handler_preserves t u : W t u ->
  W (PTree.interp sample_or_diverge_handler t) (PTree.interp sample_or_diverge_handler u).
Proof. intro Htu. exact (peutt_interp_guarded sample_or_diverge_handler_guarded Htu). Qed.

(** An unreachable Ret branch is not a violation: guarding is AE, not
    pointwise over the syntactic sample continuation. *)
Definition null_return_handler X (e : correlationE X) : ptree correlationE SubEnumQ X :=
  match e in correlationE X return ptree correlationE SubEnumQ X with
  | Query => Prob (subenumQ_ret true)
      (fun b : bool => if b then two_query_handler Query else Ret false)
  end.

Lemma null_return_handler_guarded : GH null_return_handler.
Proof.
  apply guard_from_hitting. intros X e. destruct e.
  exists (FOSample (subenumQ_ret true) (fun b : bool => if b then
    FORet (FHVis Query (fun _ => Vis Query (fun x => Ret x))) else FORet (FHRet false))).
  split.
  - eapply (ptree_stable_hitting_prob (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros [] _; [exact two_query_handler_first_hitting|
        apply (ptree_stable_hitting_ret (FI := FI) (FO := FO))].
  - eapply FOAESample with (Good := fun b => b = true).
    + apply (sem_ae_ret (SI := SubEnumQ_SemanticMeasure)). reflexivity.
    + intros b ->. constructor. exact I.
Qed.

Definition returning_handler X (e : correlationE X) : ptree correlationE SubEnumQ X :=
  match e in correlationE X return ptree correlationE SubEnumQ X with Query => Ret true end.

Lemma returning_handler_not_guarded : ~ GH returning_handler.
Proof.
  intro Hguard.
  assert (Hret : hits (Ret true) (FORet (FHRet true))).
  { apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)). }
  pose proof (Hguard bool Query (FORet (FHRet true)) Hret) as Hbad.
  change (free_omega_ae (NI := SubEnumQ_SemanticMeasure)
    stable_head_is_visible (FORet (@FHRet correlationE SubEnumQ bool true))) in Hbad.
  dependent destruction Hbad. exact H.
Qed.

(** Heterogeneous returns are preserved, not silently specialized to eq. *)
Example guarded_interp_heterogeneous :
  @peutt correlationE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool nat
    (fun b n => b = true /\ n = O)
    (PTree.interp two_query_handler (Ret true))
    (PTree.interp two_query_handler (Ret O)).
Proof.
  apply (peutt_interp_guarded two_query_handler_guarded).
  apply peutt_ret. split; reflexivity.
Qed.
