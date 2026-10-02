(** Iteration analysis through native round kernels.  Reuses generic
    behavioral iteration and the existing primitive-loop cofinality proof;
    no client schedule, empty event signature, or totality premise is needed.
    This owner is in Interp because iteration congruence consumes the direct
    interpreter machine. Eq must not import it backwards. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Approximation Observation
  StructuralMeasure SupportLift Quotient Measure BindOrder RelationalLimit.
From PTree.Eq Require Import PStruct PEutt PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.FreeOmega Require Import Bind Hitting.
From PTree.Interp Require Import IterationUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Summary.
Context {E MN : Type → Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (peutt (FI := FI) (FO := FO)).
Context {I A : Type}.
Variable transition : I → MN (I + A).

Definition iteration_frontier_round n i :=
  @ptree_iter_round_approx E MN MF FI FreeOmegaMixedMeasure FO I A n transition i.
Definition iteration_frontier i := FOLub (fun n => iteration_frontier_round n i).

Lemma iteration_frontier_returns i :
  free_omega_ae (fun h => ∃ a, h = FHRet a) (iteration_frontier i).
Proof.
  constructor. intro n. unfold iteration_frontier_round, ptree_iter_round_approx.
  apply free_omega_ae_bind with (P := fun _ => True).
  - apply (sem_ae_true (SI := FI)).
  - intros a _. constructor. exists a. reflexivity.
Qed.

Lemma primitive_iteration_frontier i :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (PTree.iter (primitive_iter_step transition) i)) (iteration_frontier i).
Proof.
  apply (proj2 (primitive_iter_cofinal transition i (iteration_frontier i))).
  apply free_omega_qlift_refl. intros x. reflexivity.
Qed.

(** The local certificate can be proved algebraically or from complete
    step hitting. It may hide unbounded internal computation and missing
    mass. Full iteration congruence handles those cases, not a finite bound. *)
Theorem iteration_frontier_summary
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCount : @SemanticMeasureCountableAELaws MN NI}
    (step : I → ptree E MN (I + A))
    (Hstep : ∀ i, W eq (step i) (Prob (transition i) (fun x => Ret x))) i :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (PTree.iter step i)) (iteration_frontier i).
Proof.
  eapply peutt_hitting_ret_only.
  - eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
      with (SI := eq); [|reflexivity].
    intros j k ->. eapply peutt_rel_mono; [|apply Hstep].
    intros x y ->. destruct y; constructor; reflexivity.
  - exact (primitive_iteration_frontier i).
  - exact (iteration_frontier_returns i).
Qed.

(** Equivalent local entry using a supplied complete step frontier. This
    avoids invoking general probability congruence to compile a finite step. *)
Theorem iteration_frontier_summary_hitting
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCount : @SemanticMeasureCountableAELaws MN NI}
    (step : I → ptree E MN (I + A))
    (Hstep : ∀ i, ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (step i)) (FOSample (transition i) (fun next => FORet (FHRet next)))) i :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (PTree.iter step i)) (iteration_frontier i).
Proof.
  eapply iteration_frontier_summary; try typeclasses eauto.
  intro j. eapply peutt_of_hitting_lift.
  - exact (Hstep j).
  - eapply stable_hitting_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. apply stable_hitting_ret.
  - apply FOQLStructural. eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor. constructor. reflexivity.
Qed.

(** Only the requested observable needs a native limit. The complete
    frontier remains in MF, so neither a finite joint result distribution
    nor a finite state space is required. *)
Fixpoint iteration_observation_round {O} (value : A → O) n i : MN O :=
  match n with
  | O => sem_zero
  | S m => sem_bind (transition i) (fun next =>
      match next with
      | inl j => iteration_observation_round value m j
      | inr a => sem_ret (value a)
      end)
  end.

Lemma iteration_frontier_round_observes {O} (obs : stable_head E MN A → O)
    (value : A → O) (Hobs : ∀ a, obs (FHRet a) = value a) n i :
  free_omega_observes obs (iteration_frontier_round n i)
    (iteration_observation_round value n i).
Proof.
  revert i. induction n as [|n IH]; intro i.
  - constructor.
  - cbn [iteration_frontier_round ptree_iter_round_approx mixed_iter_approx
      iteration_observation_round mixed_bind sem_bind sem_ret
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure free_omega_bind].
    constructor. intros [j|a]; [apply IH|].
    rewrite <- Hobs. constructor.
Qed.

Theorem iteration_frontier_observes {O} (obs : stable_head E MN A → O)
    (value : A → O) (Hobs : ∀ a, obs (FHRet a) = value a) i out :
  sem_lub (fun n => iteration_observation_round value n i) out →
  free_omega_observes obs (iteration_frontier i) out.
Proof.
  intro Hlim. eapply FOOObserveLub.
  - intro n. exact (iteration_frontier_round_observes Hobs n i).
  - exact Hlim.
  - intro n. apply ptree_iter_round_increasing.
Qed.
End Summary.
