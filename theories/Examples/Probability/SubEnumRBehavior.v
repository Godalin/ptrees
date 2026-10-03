(** Role: finite probability/coupling/backend example. *)
(** The finite-real native backend is a small client of the existing generic
    completion and PTree theory. No FreeOmega proof is reimplemented here. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Subprobability AE Coupling Omega Mixed.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PStruct PStrong PEutt UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.FreeOmega Require Import Relation Bind Algebra Iter Hitting.
From PTree.Interp.FreeOmega Require Import AbsorbingIteration.

Fail Check PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Completion.
Variable R : realType.
Local Notation MN := (SubEnumR R).
Local Notation NI := (SubEnumR_SemanticMeasure R).
Local Notation NO := (SubEnumR_SemanticOmega R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

(** Native finite support is deliberately not claimed to be complete. *)
Fail Definition real_native_omega_complete : @SemanticOmegaLaws MN NI NO := _.

Definition real_completion_core : @SemanticMeasureCoreLaws MF FI := _.
Section GenericTrees.
Context {E : Type → Type}.
Local Notation W A B RR := (@peutt E MN MF FI real_completion_core FreeOmegaMixedMeasure FO A B RR).

Example real_complete_step_summary {I A} (step : I → ptree E MN (I+A))
    (front : I → MF (stable_head E MN (I+A)))
    (Hfront : ∀ i, ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (step i)) (front i)) i :
  ptree_stable_hitting (FI := FI) (FO := FO) (observe (PTree.iter step i))
    (complete_iteration_frontier step front i).
Proof. apply complete_iteration_hitting. exact Hfront. Qed.

Example real_hitting_exists {A} (t : ptree E MN A) :
  ∃ out, @stable_hitting MF FI FO _ _
    (@ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure A) (observe t) out.
Proof. apply stable_hitting_exists. Qed.

(** Native non-diagonal coupling is consumed by PStrong, then promoted
    through the existing generic theorem to canonical peutt. *)
Example real_crossed_sample_strong (mu : MN bool) :
  @pstrong E MN NI (SubEnumR_SemanticMeasureCoreLaws R) bool bool eq
    (Prob mu (λ b, Ret b))
    (Prob (subenumR_map negb mu) (λ b, Ret (negb b))).
Proof.
  apply pstrong_prob_intro; eapply sem_lift_mono; [|exact (subenumR_lift_map negb mu)].
  intros x y Hxy; apply pstrong_ret_intro.
  rewrite -Hxy negbK; reflexivity.
Qed.
Example real_crossed_sample_peutt (mu : MN bool) :
  W bool bool eq (Prob mu (λ b, Ret b))
    (Prob (subenumR_map negb mu) (λ b, Ret (negb b))).
Proof. apply peutt_of_pstrong; exact: real_crossed_sample_strong. Qed.
End GenericTrees.

Variant real_serviceE : Type → Type := RealReply : bool → real_serviceE unit.
Definition sqrt_weight : R := Num.sqrt (1 / 2).
Lemma sqrt_weight_valid : 0 <= sqrt_weight ∧ sqrt_weight <= 1.
Proof.
  split; first exact: sqrtr_ge0.
  have Hhalf : (1 : R) / 2 <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
  have H := ler_wsqrtr Hhalf; by rewrite sqrtr1 in H.
Qed.
Definition sqrt_coin := subenumR_coin (proj1 sqrt_weight_valid) (proj2 sqrt_weight_valid).
CoFixpoint real_service (b : bool) : ptree real_serviceE MN unit :=
  Vis (RealReply b) (λ _, Prob sqrt_coin (λ c, Tau (real_service c))).

Example real_crossed_infinite_service :
  @peutt real_serviceE MN MF FI real_completion_core FreeOmegaMixedMeasure FO unit unit eq
    (PTree.bind (Prob sqrt_coin (λ b, Ret b)) real_service)
    (PTree.bind (Prob (subenumR_map negb sqrt_coin) (λ b, Ret (negb b))) real_service).
Proof.
  eapply (PTree.Eq.Bind.peutt_bind (MF := MF) (FI := FI) (FO := FO)) with (RR := eq).
  - apply real_crossed_sample_peutt.
  - intros x y ->; apply peutt_refl; intro z; reflexivity.
Qed.
End Completion.
