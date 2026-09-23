From PTree.Prob.FreeOmega Require Import RelationalLimit.
From PTree.Eq Require Export Iter.
(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Eq Require Import StableHittingRelation.
From Coq.Logic Require Import ClassicalChoice.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt PStruct.
From PTree.Eq.FreeOmega Require Import Relation Bind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Iteration equations and fusion principles for the maintained FreeOmega
    backend. *)
Section FreeOmegaIter.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Theorem peutt_iter_unfold {I R}
    (step : I -> ptree E MN (I + R)) (i : I) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq
    (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof.
  apply (Iter.peutt_iter_unfold
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_iter_structural {I R}
    (step1 step2 : I -> ptree E MN (I + R)) (i : I) :
  (forall j, pstruct eq (step1 j) (step2 j)) ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq
    (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  apply (Iter.peutt_iter_structural
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_iter_rel
    {I1 I2 R1 R2}
    (SI : I1 -> I2 -> Prop) (RR : R1 -> R2 -> Prop)
    (f : I1 -> ptree E MN (I1 + R1))
    (g : I2 -> ptree E MN (I2 + R2))
    (Hstep : forall i1 i2, SI i1 i2 ->
      pstruct (pstruct_iter_sum_rel SI RR) (f i1) (g i2))
    i1 i2 :
  SI i1 i2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR
    (PTree.iter f i1) (PTree.iter g i2).
Proof.
  apply (Iter.peutt_iter_rel
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
  exact Hstep.
Qed.

(** Parameter identity / naturality.  Post-processing the result of a loop
    is equivalent to pushing that Kleisli continuation into every successful
    step result.  The proof is structural and therefore supports visible
    events, probability, divergence, and unbounded iteration uniformly. *)
Theorem peutt_iter_natural {I A B}
    (step : I -> ptree E MN (I + A))
    (k : A -> ptree E MN B) (i : I) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega B B eq
    (PTree.bind (PTree.iter step i) k)
    (PTree.iter (pstruct_iter_natural_step step k) i).
Proof.
  apply (Iter.peutt_iter_natural
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

(** Double-dagger / codiagonal identity.  Nested retries at either sum layer
    are flattened into retries of one loop. *)
Theorem peutt_iter_codiagonal {I R}
    (step : I -> ptree E MN (I + (I + R))) (i : I) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R R eq
    (PTree.iter (fun j => PTree.iter step j) i)
    (PTree.iter (pstruct_iter_codiagonal_flat_step step) i).
Proof.
  apply (Iter.peutt_iter_codiagonal
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Section EventlessBehavioralIterationFusion.
Context {I1 I2 R1 R2 : Type}.
Context `{NCAEIterFusion : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIterFusion : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

Definition iter_behavioral_sum_rel
    (x1 : I1 + R1) (x2 : I2 + R2) : Prop :=
  match x1, x2 with
  | inl i1, inl i2 => SI i1 i2
  | inr r1, inr r2 => RR r1 r2
  | _, _ => False
  end.

Variable step_out1 : I1 -> MF (stable_head E MN (I1 + R1)).
Variable step_out2 : I2 -> MF (stable_head E MN (I2 + R2)).
Hypothesis Hstep_out1 : forall i1,
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega (I1 + R1)
    (observe (step1 i1)) (step_out1 i1).
Hypothesis Hstep_out2 : forall i2,
  @ptree_stable_hitting E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega (I2 + R2)
    (observe (step2 i2)) (step_out2 i2).
Hypothesis Hstep_lift : forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      iter_behavioral_sum_rel
      (@peutt_state E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega
        (I1 + R1) (I2 + R2) iter_behavioral_sum_rel))
    (step_out1 i1) (step_out2 i2).

Lemma iter_complete_rows_behavioral_lift rounds :
  forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN R1 R2 RR
      (@peutt_state E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega R1 R2 RR))
    (iter_complete_rows no_event step_out1 rounds i1)
    (iter_complete_rows no_event step_out2 rounds i2).
Proof.
  induction rounds as [|rounds IH]; intros i1 i2 Hij.
  - constructor. constructor.
  - cbn [iter_complete_rows].
    eapply FOQLBind; [exact (Hstep_lift Hij)|].
    intros h1 h2 Hhead. dependent destruction Hhead.
    + destruct r1 as [j1|v1], r2 as [j2|v2];
        cbn [iter_head_next] in H |- *.
      * apply IH. exact H.
      * contradiction.
      * contradiction.
      * constructor. constructor. constructor. exact H.
    + exfalso. exact (no_event e).
Qed.

Theorem peutt_iter_behavioral_rel_of_outputs i1 i2 :
  SI i1 i2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  let rows1 := constr:(fun rounds =>
    iter_complete_rows no_event step_out1 rounds i1) in
  let rows2 := constr:(fun rounds =>
    iter_complete_rows no_event step_out2 rounds i2) in
  eapply peutt_of_hitting_lift
    with (out1 := FOLub rows1) (out2 := FOLub rows2).
  - eapply ptree_stable_hitting_iter_of_unbounded_steps
      with (step_out := step_out1).
    + exact Hstep_out1.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - eapply ptree_stable_hitting_iter_of_unbounded_steps
      with (step_out := step_out2).
    + exact Hstep_out2.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - apply FOQLLub. intro rounds.
    apply iter_complete_rows_behavioral_lift. exact Hij.
Qed.

End EventlessBehavioralIterationFusion.

Section EventlessBehavioralIterationCongruence.
Context {I1 I2 R1 R2 : Type}.
Context `{NCAEIterCong : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIterCong : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

(** Heterogeneous behavioral fusion for eventless unbounded loops. *)
Theorem peutt_iter_behavioral_rel
    (Hstep : forall i1 i2, SI i1 i2 ->
      @peutt E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega
        (I1 + R1) (I2 + R2)
        (iter_behavioral_sum_rel SI RR)
        (step1 i1) (step2 i2))
    i1 i2 :
  SI i1 i2 ->
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  assert (Hexists1 : forall j1, exists out,
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega (I1 + R1)
        (observe (step1 j1)) out).
  { intro j1. apply stable_hitting_exists. }
  assert (Hexists2 : forall j2, exists out,
      @ptree_stable_hitting E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega (I2 + R2)
        (observe (step2 j2)) out).
  { intro j2. apply stable_hitting_exists. }
  destruct (choice _ Hexists1) as [out1 Hout1].
  destruct (choice _ Hexists2) as [out2 Hout2].
  eapply peutt_iter_behavioral_rel_of_outputs
    with (step_out1 := out1) (step_out2 := out2)
         (SI := SI) (RR := RR); try eassumption.
  intros j1 j2 Hrel.
  change (@sem_lift MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    _ _
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      (iter_behavioral_sum_rel SI RR)
      (@peutt_state E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega
        (I1 + R1) (I2 + R2) (iter_behavioral_sum_rel SI RR)))
    (out1 j1) (out2 j2)).
  eapply peutt_hitting_lift;
    [exact (Hstep j1 j2 Hrel)|exact (Hout1 j1)|exact (Hout2 j2)].
Qed.

End EventlessBehavioralIterationCongruence.



End FreeOmegaIter.
