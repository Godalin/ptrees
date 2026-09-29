(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel PEutt.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.

Local Notation MF := (FreeOmega EnumQ).

Definition ptree_reg_nested_heads :
    MF (stable_head regE EnumQ nat) :=
  FOSample reg_fair (fun side =>
    FOSample (reg_inner side) (fun outcome => FORet (FHRet outcome))).

Definition ptree_reg_merged_heads :
    MF (stable_head regE EnumQ nat) :=
  FOSample reg_merged_three (fun outcome => FORet (FHRet outcome)).

Lemma ptree_reg_ret_weak (n : nat) :
  @ptree_stable_hitting regE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    nat (observe (Ret n)) (FORet (FHRet n)).
Proof.
  assert (Hobs : observe (Ret n : ptree regE EnumQ nat) = RetF n) by reflexivity.
  rewrite Hobs. apply (ptree_stable_hitting_ret
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure) (E := regE)).
Qed.

Lemma ptree_reg_nested_weak :
  @ptree_stable_hitting regE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    nat (observe reg_nested_program) ptree_reg_nested_heads.
Proof.
  assert (Hobs : observe reg_nested_program =
    ProbF reg_fair (fun side =>
      Prob (reg_inner side) (fun outcome => Ret outcome))) by reflexivity.
  rewrite Hobs.
  unfold ptree_reg_nested_heads.
  eapply (ptree_stable_hitting_prob
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure) (E := regE)
    (mu := reg_fair)
    (k := fun side => Prob (reg_inner side) (fun outcome => Ret outcome))
    (front := fun side => FOSample (reg_inner side)
      (fun outcome => FORet (FHRet outcome)))
    (Good := fun _ => True)).
  - apply sem_ae_true.
  - intros side _. eapply (ptree_stable_hitting_prob
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (MX := FreeOmegaMixedMeasure) (E := regE)
      (mu := reg_inner side)
      (k := fun outcome => Ret outcome)
      (front := fun outcome => FORet (FHRet outcome))
      (Good := fun _ => True)).
    + apply sem_ae_true.
    + intros outcome _. exact (ptree_reg_ret_weak outcome).
Qed.

Lemma ptree_reg_merged_weak :
  @ptree_stable_hitting regE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    nat (observe reg_merged_program) ptree_reg_merged_heads.
Proof.
  assert (Hobs : observe reg_merged_program =
    ProbF reg_merged_three (fun outcome => Ret outcome)) by reflexivity.
  rewrite Hobs.
  unfold ptree_reg_merged_heads.
  eapply (ptree_stable_hitting_prob
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure) (E := regE)
    (mu := reg_merged_three)
    (k := fun outcome => Ret outcome)
    (front := fun outcome => FORet (FHRet outcome))
    (Good := fun _ => True)).
  - apply sem_ae_true.
  - intros outcome _. exact (ptree_reg_ret_weak outcome).
Qed.

Definition reg_head_value (h : stable_head regE EnumQ nat) : nat :=
  match h with
  | FHRet n => n
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition ptree_reg_nested_observation : EnumQ nat :=
  @sem_bind EnumQ EnumQ_SemanticMeasure _ _ reg_fair
    (fun side => @sem_bind EnumQ EnumQ_SemanticMeasure _ _
      (reg_inner side) (fun outcome => sem_ret outcome)).

Definition ptree_reg_merged_observation : EnumQ nat :=
  @sem_bind EnumQ EnumQ_SemanticMeasure _ _ reg_merged_three
    (fun outcome => sem_ret outcome).

Lemma ptree_reg_nested_observes :
  free_omega_observes reg_head_value ptree_reg_nested_heads
    ptree_reg_nested_observation.
Proof.
  unfold ptree_reg_nested_heads, ptree_reg_nested_observation.
  eapply FOOObserveSample.
  intro side. eapply FOOObserveSample. intro outcome. constructor.
Qed.

Lemma ptree_reg_merged_observes :
  free_omega_observes reg_head_value ptree_reg_merged_heads
    ptree_reg_merged_observation.
Proof.
  unfold ptree_reg_merged_heads, ptree_reg_merged_observation.
  eapply FOOObserveSample.
  intro outcome. constructor.
Qed.

Lemma ptree_reg_nested_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    (FreeOmegaObservableSemanticOmega
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _
    ptree_reg_nested_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists nat, reg_head_value, ptree_reg_nested_observation.
  split; first exact ptree_reg_nested_observes.
  vm_compute. reflexivity.
Qed.

Lemma ptree_reg_merged_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    (FreeOmegaObservableSemanticOmega
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _
    ptree_reg_merged_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists nat, reg_head_value, ptree_reg_merged_observation.
  split; first exact ptree_reg_merged_observes.
  vm_compute. reflexivity.
Qed.

Lemma ptree_reg_nested_ast :
  @ptree_stable_hitting_ast regE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega nat
    (observe reg_nested_program) ptree_reg_nested_heads.
Proof. split; [exact ptree_reg_nested_weak|exact ptree_reg_nested_total]. Qed.

Corollary ptree_reg_nested_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega
    (ptree' regE EnumQ nat) (stable_head regE EnumQ nat)
    (@ptree_primitive_kernel regE EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure nat)
    (observe reg_nested_program) ptree_reg_nested_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe reg_nested_program) ptree_reg_nested_heads)).
  exact ptree_reg_nested_ast.
Qed.

Lemma ptree_reg_nested_merged_lift
    (sim : ptree regE EnumQ nat -> ptree regE EnumQ nat -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    (stable_head_rel eq sim)
    ptree_reg_nested_heads ptree_reg_merged_heads.
Proof.
  (** Flatten using the existing two-level algebra, then use the native
      equality of the concrete finite distributions. No atom-by-atom support
      reconstruction and no equality-lifting reflection assumption is needed. *)
  eapply sem_lift_mono with
    (R := fun h1 h2 => exists mid, h1 = mid /\ stable_head_rel eq sim mid h2).
  - intros h1 h2 [mid [Heq Hrel]]. subst mid. exact Hrel.
  - eapply sem_lift_comp.
    + apply (mixed_bind_node_assoc (NI := EnumQ_SemanticMeasure)
        (FI := FreeOmegaObservableSemanticMeasure)
        (MX := FreeOmegaMixedMeasure) reg_fair reg_inner
        (fun n => FORet (FHRet n))).
    + eapply (mixed_lift_bind (NI := EnumQ_SemanticMeasure)
        (FI := FreeOmegaObservableSemanticMeasure)
        (MX := FreeOmegaMixedMeasure)) with (R := eq).
      * eapply sem_lift_proper_l with (mu := reg_merged_three).
        -- apply sem_eq_sym. exact (enumQ_meas_eq_of_eqenum reg_nested_outcomes_eqenum).
        -- apply sem_lift_refl. intro n. reflexivity.
      * intros x y ->.
        apply (sem_lift_ret (SI := FreeOmegaObservableSemanticMeasure)).
        constructor. reflexivity.
Qed.

Theorem peutt_reg_nested_merged :
  @peutt regE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega nat nat eq
    reg_nested_program reg_merged_program.
Proof.
  eapply peutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact ptree_reg_nested_weak.
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact ptree_reg_merged_weak.
  - exact (ptree_reg_nested_merged_lift _).
Qed.
