Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Logic.ClassicalChoice Program.Equality.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew UnifiedFrontier PrimitiveStableHitting
  OperationalProbabilisticPTS ProbabilisticEutt PStrong
  OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Iteration equations and fusion principles for the maintained FreeOmega
    backend.  Operational grids and productivity certificates will be
    colocated here as they are extracted from the compatibility Base. *)
Section FreeOmegaIter.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).

Theorem free_probabilistic_eutt_iter_unfold {I R}
    (step : I -> ptree E MN (I + R)) (i : I) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural.
  exact (observing_observe (unfold_aloop_ step i)).
Qed.

Theorem free_probabilistic_eutt_iter_structural {I R}
    (step1 step2 : I -> ptree E MN (I + R)) (i : I) :
  (forall j, pstructural eq (step1 j) (step2 j)) ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  intro Hstep. apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_iter. exact Hstep.
Qed.

Theorem free_probabilistic_eutt_iter_rel
    {I1 I2 R1 R2}
    (SI : I1 -> I2 -> Prop) (RR : R1 -> R2 -> Prop)
    (f : I1 -> ptree E MN (I1 + R1))
    (g : I2 -> ptree E MN (I2 + R2))
    (Hstep : forall i1 i2, SI i1 i2 ->
      pstructural (pstructural_iter_sum_rel SI RR) (f i1) (g i2))
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter f i1) (PTree.iter g i2).
Proof.
  intro Hij. apply free_probabilistic_eutt_of_pstructural.
  eapply pstructural_iter_rel; eauto.
Qed.

(** Parameter identity / naturality.  Post-processing the result of a loop
    is equivalent to pushing that Kleisli continuation into every successful
    step result.  The proof is structural and therefore supports visible
    events, probability, divergence, and unbounded iteration uniformly. *)
Theorem free_probabilistic_eutt_iter_natural {I A B}
    (step : I -> ptree E MN (I + A))
    (k : A -> ptree E MN B) (i : I) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B B eq
    (PTree.bind (PTree.iter step i) k)
    (PTree.iter (pstructural_iter_natural_step step k) i).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_iter_natural.
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

Definition free_iter_behavioral_sum_rel
    (x1 : I1 + R1) (x2 : I2 + R2) : Prop :=
  match x1, x2 with
  | inl i1, inl i2 => SI i1 i2
  | inr r1, inr r2 => RR r1 r2
  | _, _ => False
  end.

Variable step_out1 : I1 -> MF (frontier_head E MN (I1 + R1)).
Variable step_out2 : I2 -> MF (frontier_head E MN (I2 + R2)).
Hypothesis Hstep_out1 : forall i1,
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (I1 + R1)
    (observe (step1 i1)) (step_out1 i1).
Hypothesis Hstep_out2 : forall i2,
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (I2 + R2)
    (observe (step2 i2)) (step_out2 i2).
Hypothesis Hstep_lift : forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      free_iter_behavioral_sum_rel
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2) free_iter_behavioral_sum_rel))
    (step_out1 i1) (step_out2 i2).

Lemma free_iter_complete_rows_behavioral_lift rounds :
  forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN R1 R2 RR
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface R1 R2 RR))
    (free_iter_complete_rows no_event step_out1 rounds i1)
    (free_iter_complete_rows no_event step_out2 rounds i2).
Proof.
  induction rounds as [|rounds IH]; intros i1 i2 Hij.
  - constructor. constructor.
  - cbn [free_iter_complete_rows].
    eapply FOQLBind; [exact (Hstep_lift Hij)|].
    intros h1 h2 Hhead. dependent destruction Hhead.
    + destruct r1 as [j1|v1], r2 as [j2|v2];
        cbn [free_iter_head_next] in H |- *.
      * apply IH. exact H.
      * contradiction.
      * contradiction.
      * constructor. constructor. constructor. exact H.
    + exfalso. exact (no_event e).
Qed.

Theorem free_probabilistic_eutt_iter_behavioral_rel_of_outputs i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  let rows1 := constr:(fun rounds =>
    free_iter_complete_rows no_event step_out1 rounds i1) in
  let rows2 := constr:(fun rounds =>
    free_iter_complete_rows no_event step_out2 rounds i2) in
  eapply probabilistic_eutt_of_hitting_lift
    with (out1 := FOLub rows1) (out2 := FOLub rows2).
  - eapply free_operational_weak_iter_of_unbounded_steps
      with (step_out := step_out1).
    + exact Hstep_out1.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - eapply free_operational_weak_iter_of_unbounded_steps
      with (step_out := step_out2).
    + exact Hstep_out2.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - apply FOQLLub. intro rounds.
    apply free_iter_complete_rows_behavioral_lift. exact Hij.
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
Theorem free_probabilistic_eutt_iter_behavioral_rel
    (Hstep : forall i1 i2, SI i1 i2 ->
      @probabilistic_eutt E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2)
        (free_iter_behavioral_sum_rel SI RR)
        (step1 i1) (step2 i2))
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  assert (Hexists1 : forall j1, exists out,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I1 + R1)
        (observe (step1 j1)) out).
  { intro j1. apply stable_hitting_weak_exists. }
  assert (Hexists2 : forall j2, exists out,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I2 + R2)
        (observe (step2 j2)) out).
  { intro j2. apply stable_hitting_weak_exists. }
  destruct (choice _ Hexists1) as [out1 Hout1].
  destruct (choice _ Hexists2) as [out2 Hout2].
  eapply free_probabilistic_eutt_iter_behavioral_rel_of_outputs
    with (step_out1 := out1) (step_out2 := out2)
         (SI := SI) (RR := RR); try eassumption.
  intros j1 j2 Hrel.
  change (@sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      (free_iter_behavioral_sum_rel SI RR)
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2) (free_iter_behavioral_sum_rel SI RR)))
    (out1 j1) (out2 j2)).
  eapply probabilistic_eutt_hitting_lift;
    [exact (Hstep j1 j2 Hrel)|exact (Hout1 j1)|exact (Hout2 j2)].
Qed.

End EventlessBehavioralIterationCongruence.

Section EventfulBehavioralIterationClosure.
Context {I1 I2 R1 R2 : Type}.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

(** Native coinduction candidate for eventful behavioral fusion.  Unlike the
    eventless grid theorem, it does not erase visible heads: their
    continuations must re-enter this candidate. *)
Definition free_iter_eventful_bisim_candidate
    (s1 : ptree' E MN R1) (s2 : ptree' E MN R2) : Prop :=
  exists i1 i2,
    SI i1 i2 /\
    s1 = observe (PTree.iter step1 i1) /\
    s2 = observe (PTree.iter step2 i2).

(** Exact generator-level obligation for eventful behavioral iteration.
    This is deliberately independent of finite schedules and of the
    eventless complete-row construction. *)
Definition free_iter_eventful_generator_closed : Prop :=
  forall i1 i2, SI i1 i2 ->
    @stable_hitting_match MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface
      (ptree' E MN R1) (ptree' E MN R2)
      (frontier_head E MN R1) (frontier_head E MN R2)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R1)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R2)
      (@ptree_stable_head_rel E MN R1 R2 RR)
      free_iter_eventful_bisim_candidate
      (observe (PTree.iter step1 i1))
      (observe (PTree.iter step2 i2)).

Theorem free_probabilistic_eutt_iter_eventful_of_generator_closed
    (Hclosed : free_iter_eventful_generator_closed) :
  forall i1 i2, SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intros i1 i2 Hij.
  eapply probabilistic_eutt_coinduction with
      (sim := free_iter_eventful_bisim_candidate).
  - intros s1 s2 [j1 [j2 [Hj [-> ->]]]]. exact (Hclosed j1 j2 Hj).
  - exists i1, i2. repeat split; try reflexivity. exact Hij.
Qed.

End EventfulBehavioralIterationClosure.

End FreeOmegaIter.
