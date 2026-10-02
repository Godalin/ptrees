(** Frontier iteration conservatively extends ordinary absorbing Kleisli
    iteration. Return-only is a local step certificate, not an empty effect
    signature. Finite frontiers start one round ahead of bottom iteration. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder KleisliIteration.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Interp Require Import FrontierIteration.
Set Implicit Arguments.
Unset Strict Implicit.

Section ReturnIteration.
Context {E MN MF : Type → Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}.
Context {I A : Type} (step : I → ptree E MN (I+A)).

Definition iteration_return_map (out : MF A) : MF (stable_head E MN A) :=
  sem_bind out (fun a => sem_ret (FHRet a)).
Definition iteration_return_front (K : I → MF (I+A)) i :=
  sem_bind (K i) (fun v => sem_ret (FHRet v : stable_head E MN (I+A))).

Theorem iteration_summary_round_return_only (K : I → MF (I+A)) n i :
  sem_eq (iteration_summary_round step (iteration_return_front K) n i)
    (iteration_return_map (sem_iter_approx K (S n) i)).
Proof.
  revert i; induction n as [|n IH]; intro i.
  all: eapply sem_eq_trans; [apply (iteration_summary_round_unfold step (FC := FC) (FB := FB))|].
  all: unfold iteration_return_front;
    eapply sem_eq_trans; [apply sem_bind_assoc|].
  all: unfold iteration_return_map; cbn [sem_iter_approx sem_iter_step];
    eapply sem_eq_trans; [|apply sem_eq_sym; apply sem_bind_assoc].
  all: apply sem_bind_ae_proper; eapply sem_ae_mono; [|apply sem_ae_true].
  all: intros [j|a] _.
  all: eapply sem_eq_trans; [apply sem_bind_ret_l|].
  - apply sem_eq_sym. apply sem_bind_zero_eq.
  - apply sem_eq_sym. exact (sem_bind_ret_l a (fun a => sem_ret (FHRet a : stable_head E MN A))).
  - apply IH.
  - apply sem_eq_sym. exact (sem_bind_ret_l a (fun a => sem_ret (FHRet a : stable_head E MN A))).
Qed.

Theorem iteration_summary_return_only (K : I → MF (I+A)) i summary_out out :
  iteration_summary step (iteration_return_front K) i summary_out →
  sem_iter K i out →
  sem_eq summary_out (iteration_return_map out).
Proof.
  intros Hsummary Hiter.
  eapply sem_lub_proper.
  - intro n. apply iteration_summary_round_return_only.
  - exact Hsummary.
  - apply sem_bind_lub.
    + intro n. apply sem_iter_approx_increasing; typeclasses eauto.
    + apply (proj1 (sem_iter_lub_shift K i out)). exact Hiter.
Qed.

(** No separate native/frontier coherence premise is left to the program
    client: the generalized complete-step theorem constructs the witness. *)
Theorem ptree_iter_return_only
    `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
    `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
    `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
    (K : I → MF (I+A))
    (Hstep : ∀ i, ptree_stable_hitting (MF := MF)
      (observe (step i)) (iteration_return_front K i)) i out :
  sem_iter K i out → ∃ summary_out,
    ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) summary_out ∧
    sem_eq summary_out (iteration_return_map out).
Proof.
  intro Hiter.
  destruct (iteration_summary_exists (step := step) Hstep i) as [hs [Hsummary Hhit]].
  exists hs; split; [exact Hhit|].
  eapply iteration_summary_return_only; eassumption.
Qed.

Section Native.
Context `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Variable transition : I → MN (I+A).
Definition iteration_native_front i :=
  mixed_bind (transition i) (fun v => sem_ret (FHRet v : stable_head E MN (I+A))).

Lemma iteration_mixed_approx_increasing i :
  sem_increasing (fun n => mixed_iter_approx (MF := MF) n transition i).
Proof.
  intro n; revert i; induction n as [|n IH]; intro i; [apply sem_zero_le|].
  apply mixed_bind_le_k. intros [j|a]; [apply IH|apply sem_le_refl].
Qed.

Theorem iteration_summary_round_mixed_iter n i :
  sem_eq (iteration_summary_round step iteration_native_front n i)
    (iteration_return_map (mixed_iter_approx (MF := MF) (S n) transition i)).
Proof.
  revert i; induction n as [|n IH]; intro i.
  all: eapply sem_eq_trans; [apply (iteration_summary_round_unfold step (FC := FC) (FB := FB))|].
  all: unfold iteration_native_front;
    eapply sem_eq_trans; [apply mixed_bind_assoc|].
  all: unfold iteration_return_map; cbn [mixed_iter_approx];
    eapply sem_eq_trans; [|apply sem_eq_sym; apply mixed_bind_assoc].
  all: apply mixed_bind_ae_proper; eapply sem_ae_mono; [|apply sem_ae_true].
  all: intros [j|a] _.
  all: eapply sem_eq_trans; [apply sem_bind_ret_l|].
  - apply sem_eq_sym. apply sem_bind_zero_eq.
  - apply sem_eq_sym. exact (sem_bind_ret_l a (fun a => sem_ret (FHRet a : stable_head E MN A))).
  - apply IH.
  - apply sem_eq_sym. exact (sem_bind_ret_l a (fun a => sem_ret (FHRet a : stable_head E MN A))).
Qed.

Theorem iteration_summary_mixed_iter i summary_out out :
  iteration_summary step iteration_native_front i summary_out →
  mixed_iter (MF := MF) transition i out →
  sem_eq summary_out (iteration_return_map out).
Proof.
  intros Hsummary Hiter.
  eapply sem_lub_proper.
  - intro n. apply iteration_summary_round_mixed_iter.
  - exact Hsummary.
  - apply sem_bind_lub.
    + intro n. apply iteration_mixed_approx_increasing.
    + apply (proj2 (sem_lub_zero_prefix _ _)).
      eapply sem_lub_chain_proper; [|exact Hiter].
      intro n; destruct n; apply sem_eq_refl.
Qed.

Theorem ptree_iter_mixed_iter
    `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
    `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
    (Hstep : ∀ i, ptree_stable_hitting (MF := MF)
      (observe (step i)) (iteration_native_front i)) i out :
  mixed_iter (MF := MF) transition i out → ∃ summary_out,
    ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) summary_out ∧
    sem_eq summary_out (iteration_return_map out).
Proof.
  intro Hiter.
  destruct (iteration_summary_exists (step := step) Hstep i) as [hs [Hsummary Hhit]].
  exists hs; split; [exact Hhit|].
  eapply iteration_summary_mixed_iter; eassumption.
Qed.
End Native.
End ReturnIteration.
