Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.Equality Classes.RelationClasses Relations.Relation_Operators.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import FiniteInternal PFiniteResidual PEutt PTreeKernel
  PrimitiveStableHitting UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Negative audit of a tempting shortcut to unrestricted residual
    soundness.  Closing the continuation candidate by equivalence UNDER
    the residual generator is not a sound up-to principle.  This does NOT
    refute raw-GFP soundness or its possible transitivity. *)
Variant closure_event : Type -> Type := .
Local Notation tree := (ptree closure_event SubEnum bool).
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation step := (@pfinite_residualF closure_event SubEnum MF
  SubEnum_SemanticMeasure FI FreeOmegaMixedMeasure bool bool eq).
Local Notation hit := (@ptree_hitting_approx closure_event SubEnum MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool).
Local Notation PE := (@peutt closure_event SubEnum MF FI
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega bool bool eq).

CoFixpoint closure_spin : tree := Tau closure_spin.
Definition closure_return : tree := Ret true.
Definition closure_delayed : tree := Tau closure_return.

Inductive closure_edges : tree -> tree -> Prop :=
| ClosureLoopEdge : closure_edges closure_spin closure_delayed
| ClosureReturnEdge : closure_edges closure_delayed closure_return.

Definition closed_edges := clos_refl_sym_trans tree closure_edges.

Lemma closed_edges_equivalence : Equivalence closed_edges.
Proof.
  split; [intro t; apply rst_refl|intros t u; apply rst_sym|
    intros t u v; apply rst_trans].
Qed.

Lemma closure_spin_return : closed_edges closure_spin closure_return.
Proof.
  eapply rst_trans; apply rst_step; [apply ClosureLoopEdge|apply ClosureReturnEdge].
Qed.

(** Both advertised edges pass the proposed up-to-equivalence check. *)
Lemma closure_edges_upto_postfixed t u : closure_edges t u -> step closed_edges t u.
Proof.
  intro H. destruct H.
  - eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
    apply sem_lift_ret. unfold pfinite_guard, observe. cbn.
    constructor. apply closure_spin_return.
  - eapply PFiniteResidualStep; [apply FITau, FIStop|apply FIStop|].
    apply sem_lift_ret. unfold pfinite_guard, observe. cbn.
    constructor. reflexivity.
Qed.

(** No continuation relation can repair a Tau/Ret guard mismatch after
    every finite cut of the silent loop has left that loop in place. *)
Lemma closure_spin_return_no_step (sim : tree -> tree -> Prop) :
  ~ step sim closure_spin closure_return.
Proof.
  intro Hstep. inversion Hstep as [t1 t2 out1 out2 Hcut1 Hcut2 Hlift]; subst.
  pose proof (finite_internal_self_loop_inv Hcut1 eq_refl) as Hout1.
  pose proof (finite_internal_ret_inv Hcut2) as Hout2. subst out1 out2.
  pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hae : @free_omega_ae SubEnum SubEnum_SemanticMeasure tree
    (fun t => t = closure_spin) (FORet closure_spin)).
  { apply FOAERet. reflexivity. }
  specialize (Hsupport _ Hae). dependent destruction Hsupport.
  destruct H as [t [Hguard ->]]. unfold pfinite_guard, observe in Hguard.
  cbn in Hguard. inversion Hguard.
Qed.

Theorem equivalence_closure_upto_not_postfixed :
  ~ (forall t u, closed_edges t u -> step closed_edges t u).
Proof. intro H. apply (closure_spin_return_no_step (H _ _ closure_spin_return)). Qed.

(** Even when the INPUT candidate is an equivalence, the residual
    generator need not return a transitive relation. *)
Theorem residual_generator_does_not_preserve_equivalences :
  Equivalence closed_edges /\ ~ Transitive (step closed_edges).
Proof.
  split; [apply closed_edges_equivalence|]. intro Htrans.
  apply (closure_spin_return_no_step
    (Htrans _ _ _ (closure_edges_upto_postfixed ClosureLoopEdge)
      (closure_edges_upto_postfixed ClosureReturnEdge))).
Qed.

Lemma closure_spin_approx_zero n : hit n (observe closure_spin) = FOZero.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (hit n (observe closure_spin) = FOZero). exact IH.
Qed.

Lemma closure_spin_not_peutt_return : ~ PE closure_spin closure_return.
Proof.
  intro Hpeutt.
  pose (out := FOLub (fun n => hit n (observe closure_spin))).
  assert (Hspin : @ptree_stable_hitting closure_event SubEnum MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_spin) out).
  { apply free_omega_qlift_refl. intro h. reflexivity. }
  assert (Hret : @ptree_stable_hitting closure_event SubEnum MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_return) (FORet (FHRet true))).
  { exact (@stable_hitting_ret closure_event SubEnum MF
      FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaObservableSemanticMeasureBindLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticOmegaLaws
      FreeOmegaObservableSemanticOmegaCofinalityLaws bool true). }
  pose proof (peutt_hitting_lift Hpeutt Hspin Hret) as Hlift.
  pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hempty : free_omega_ae (fun _ => False) out).
  { apply FOAELub. intro n. rewrite closure_spin_approx_zero. apply FOAEZero. }
  specialize (Hsupport _ Hempty). dependent destruction Hsupport.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

Theorem residual_equivalence_upto_is_unsound :
  (forall t u, closure_edges t u -> step closed_edges t u) /\
  ~ (forall t u, closure_edges t u -> PE t u).
Proof.
  split; [apply closure_edges_upto_postfixed|]. intro Hsound.
  apply closure_spin_not_peutt_return.
  eapply peutt_trans; [exact (Hsound _ _ ClosureLoopEdge)|exact (Hsound _ _ ClosureReturnEdge)].
Qed.

(** The issue persists after adding reflexivity and converse to the
    candidate.  Thus the raw GFP's already-proved reflexivity/symmetry
    cannot justify this shortcut either. *)
Definition symmetric_edges (t u : tree) :=
  t = u \/ closure_edges t u \/ closure_edges u t.
Definition symmetric_closed := clos_refl_sym_trans tree symmetric_edges.

Lemma symmetric_edges_reflexive : Reflexive symmetric_edges.
Proof. intro t. left. reflexivity. Qed.

Lemma symmetric_edges_symmetric : Symmetric symmetric_edges.
Proof. intros t u [->|[H|H]]; unfold symmetric_edges; auto. Qed.

Lemma symmetric_closed_equivalence : Equivalence symmetric_closed.
Proof.
  split; [intro t; apply rst_refl|intros t u; apply rst_sym|
    intros t u v; apply rst_trans].
Qed.

Lemma closed_edges_in_symmetric_closed t u : closed_edges t u -> symmetric_closed t u.
Proof.
  intro H. induction H.
  - apply rst_step. right. left. exact H.
  - apply rst_refl.
  - apply rst_sym. exact IHclos_refl_sym_trans.
  - eapply rst_trans; eassumption.
Qed.

Lemma symmetric_edges_upto_postfixed t u :
  symmetric_edges t u -> step symmetric_closed t u.
Proof.
  intros [->|[H|H]].
  - eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
    apply sem_lift_ret.
    exact (@Equivalence_Reflexive _ _ (pfinite_guard_equivalence symmetric_closed_equivalence) u).
  - eapply pfinite_residualF_monotone; [|apply closure_edges_upto_postfixed; exact H].
    intros x y Hxy. apply closed_edges_in_symmetric_closed. exact Hxy.
  - destruct H.
    + eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
      apply sem_lift_ret. unfold pfinite_guard, observe. cbn. constructor.
      apply rst_sym, closed_edges_in_symmetric_closed, closure_spin_return.
    + eapply PFiniteResidualStep; [apply FIStop|apply FITau, FIStop|].
      apply sem_lift_ret. unfold pfinite_guard, observe. cbn. constructor. reflexivity.
Qed.

Theorem reflexive_symmetric_residual_upto_is_unsound :
  Reflexive symmetric_edges /\ Symmetric symmetric_edges /\
  (forall t u, symmetric_edges t u -> step symmetric_closed t u) /\
  ~ (forall t u, symmetric_edges t u -> PE t u).
Proof.
  split; [apply symmetric_edges_reflexive|].
  split; [apply symmetric_edges_symmetric|].
  split; [apply symmetric_edges_upto_postfixed|]. intro Hsound.
  apply (proj2 residual_equivalence_upto_is_unsound).
  intros t u H. apply Hsound. right. left. exact H.
Qed.
