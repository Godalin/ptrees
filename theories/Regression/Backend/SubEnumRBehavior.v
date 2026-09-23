(** The finite-real native backend is a small client of the existing generic
    completion and PTree theory. No FreeOmega proof is reimplemented here. *)
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
Definition real_completion_bind : @SemanticMeasureBindLaws MF FI := _.
Definition real_completion_kleisli : @SemanticMeasureAEKleisliLaws MF FI := _.
Definition real_completion_countable : @SemanticMeasureCountableAELaws MF FI := _.
Definition real_completion_coupling : @SemanticMeasureCouplingAELaws MF FI := _.
Definition real_completion_order : @SemanticMeasureOrderLaws MF FI FO := _.
Definition real_completion_omega : @SemanticOmegaLaws MF FI FO := _.
Definition real_completion_total : @SemanticTotalProperLaws MF FI FO := _.
Definition real_completion_cofinal : @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition real_completion_omega_ae : @SemanticOmegaAELaws MF FI FO := _.
Definition real_completion_diagonal : @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition real_completion_fubini : @SemanticOmegaFubiniLaws MF FI FO := _.
Definition real_completion_mixed : @MixedMeasure MN MF := FreeOmegaMixedMeasure.
Definition real_completion_mixed_bind : @MixedMeasureLaws MN MF NI FI real_completion_mixed := _.
Definition real_completion_mixed_unit : @MixedMeasureUnitLaws MN MF NI FI real_completion_mixed := _.
Definition real_completion_mixed_node_bind : @MixedMeasureNodeBindLaws MN MF NI FI real_completion_mixed := _.
Definition real_completion_mixed_omega : @MixedMeasureOmegaLaws MN MF NI FI real_completion_mixed FO := _.

Section GenericTrees.
Context {E : Type -> Type}.
Local Notation W A B RR := (@peutt E MN MF FI real_completion_core FreeOmegaMixedMeasure FO A B RR).

Example real_pstruct_peutt {A B} (RR : A -> B -> Prop) (t : ptree E MN A) (u : ptree E MN B) :
  pstruct RR t u -> W A B RR t u.
Proof. exact: peutt_of_pstruct. Qed.
Example real_pstrong_peutt {A B} (RR : A -> B -> Prop) (t : ptree E MN A) (u : ptree E MN B) :
  pstrong RR t u -> W A B RR t u.
Proof. exact: peutt_of_pstrong. Qed.

Example real_hitting_exists {A} (t : ptree E MN A) :
  exists out, @stable_hitting MF FI FO _ _
    (@ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure A) (observe t) out.
Proof. apply stable_hitting_exists. Qed.

Example real_behavioral_bind {A B C} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B)
    (k : A -> ptree E MN C) (h : B -> ptree E MN C) :
  W A B RR t u -> (forall x y, RR x y -> W C C eq (k x) (h y)) ->
  W C C eq (PTree.bind t k) (PTree.bind u h).
Proof.
  intros Ht Hk.
  eapply (PTree.Eq.Bind.peutt_bind (MF := MF) (FI := FI) (FO := FO)); eassumption.
Qed.

Example real_behavioral_iter {I A} (step : I -> ptree E MN (I+A)) i :
  W A A eq (PTree.iter step i)
    (PTree.bind (step i) (fun r => match r with
      | inl j => Tau (PTree.iter step j) | inr a => Ret a end)).
Proof. exact: peutt_iter_unfold. Qed.

(** Native non-diagonal coupling is consumed by PStrong, then promoted
    through the existing generic theorem to canonical peutt. *)
Example real_crossed_sample_strong (mu : MN bool) :
  @pstrong E MN NI (SubEnumR_SemanticMeasureCoreLaws R) bool bool eq
    (Prob mu (fun b => Ret b))
    (Prob (subenumR_map negb mu) (fun b => Ret (negb b))).
Proof.
  apply pstrong_prob_intro; eapply sem_lift_mono; [|exact (subenumR_lift_map negb mu)].
  intros x y Hxy; apply pstrong_ret_intro.
  rewrite -Hxy negbK; reflexivity.
Qed.
Example real_crossed_sample_peutt (mu : MN bool) :
  W bool bool eq (Prob mu (fun b => Ret b))
    (Prob (subenumR_map negb mu) (fun b => Ret (negb b))).
Proof. apply real_pstrong_peutt; exact: real_crossed_sample_strong. Qed.
End GenericTrees.

Variant real_serviceE : Type -> Type := RealReply : bool -> real_serviceE unit.
Definition sqrt_weight : R := Num.sqrt (1 / 2).
Lemma sqrt_weight_valid : 0 <= sqrt_weight /\ sqrt_weight <= 1.
Proof.
  split; first exact: sqrtr_ge0.
  have Hhalf : (1 : R) / 2 <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
  have H := ler_wsqrtr Hhalf; by rewrite sqrtr1 in H.
Qed.
Definition sqrt_coin := subenumR_coin (proj1 sqrt_weight_valid) (proj2 sqrt_weight_valid).
CoFixpoint real_service (b : bool) : ptree real_serviceE MN unit :=
  Vis (RealReply b) (fun _ => Prob sqrt_coin (fun c => Tau (real_service c))).

Example real_infinite_service_tau b :
  @peutt real_serviceE MN MF FI real_completion_core FreeOmegaMixedMeasure FO unit unit eq
    (Tau (real_service b)) (real_service b).
Proof. apply peutt_tau_l. Qed.
Example real_infinite_service_hitting b :
  exists out, @stable_hitting MF FI FO _ _
    (@ptree_primitive_kernel real_serviceE MN MF FI FreeOmegaMixedMeasure unit)
    (observe (real_service b)) out.
Proof. apply stable_hitting_exists. Qed.

Example real_crossed_infinite_service :
  @peutt real_serviceE MN MF FI real_completion_core FreeOmegaMixedMeasure FO unit unit eq
    (PTree.bind (Prob sqrt_coin (fun b => Ret b)) real_service)
    (PTree.bind (Prob (subenumR_map negb sqrt_coin) (fun b => Ret (negb b))) real_service).
Proof.
  eapply real_behavioral_bind with (RR := eq).
  - apply real_crossed_sample_peutt.
  - intros x y ->; apply peutt_refl; intro z; reflexivity.
Qed.
End Completion.
