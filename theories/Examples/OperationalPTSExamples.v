Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.Equality.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  TwoLevelMeasure TwoLevelMeasureEnum FreeOmegaMeasure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier UnifiedPWeak
  OperationalProbabilisticPTS.
From PTree.Examples Require Import EnumMeasureRegression
  UnifiedPWeakEnumExamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Local Notation MF := (FreeOmega Enum).

Definition operational_reg_nested_heads :
    MF (frontier_head regE Enum nat) :=
  FOSample reg_fair (fun side =>
    FOSample (reg_inner side) (fun outcome => FORet (FHRet outcome))).

Definition operational_reg_merged_heads :
    MF (frontier_head regE Enum nat) :=
  FOSample reg_merged_three (fun outcome => FORet (FHRet outcome)).

Lemma operational_reg_ret_weak (n : nat) :
  @operational_weak regE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    nat (observe (Ret n)) (FORet (FHRet n)).
Proof.
  assert (Hobs : observe (Ret n : ptree regE Enum nat) = RetF n) by reflexivity.
  rewrite Hobs. apply (operational_weak_ret
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface) (E := regE)).
Qed.

Lemma operational_reg_nested_weak :
  @operational_weak regE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    nat (observe reg_nested_program) operational_reg_nested_heads.
Proof.
  assert (Hobs : observe reg_nested_program =
    ProbF reg_fair (fun side =>
      Prob (reg_inner side) (fun outcome => Ret outcome))) by reflexivity.
  rewrite Hobs.
  unfold operational_reg_nested_heads.
  eapply (operational_weak_prob
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface) (E := regE)
    (mu := reg_fair)
    (k := fun side => Prob (reg_inner side) (fun outcome => Ret outcome))
    (front := fun side => FOSample (reg_inner side)
      (fun outcome => FORet (FHRet outcome)))
    (Good := fun _ => True)).
  - apply sem_ae_true.
  - intros side _. eapply (operational_weak_prob
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (MX := FreeOmegaMixedMeasureInterface) (E := regE)
      (mu := reg_inner side)
      (k := fun outcome => Ret outcome)
      (front := fun outcome => FORet (FHRet outcome))
      (Good := fun _ => True)).
    + apply sem_ae_true.
    + intros outcome _. exact (operational_reg_ret_weak outcome).
Qed.

Lemma operational_reg_merged_weak :
  @operational_weak regE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    nat (observe reg_merged_program) operational_reg_merged_heads.
Proof.
  assert (Hobs : observe reg_merged_program =
    ProbF reg_merged_three (fun outcome => Ret outcome)) by reflexivity.
  rewrite Hobs.
  unfold operational_reg_merged_heads.
  eapply (operational_weak_prob
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface) (E := regE)
    (mu := reg_merged_three)
    (k := fun outcome => Ret outcome)
    (front := fun outcome => FORet (FHRet outcome))
    (Good := fun _ => True)).
  - apply sem_ae_true.
  - intros outcome _. exact (operational_reg_ret_weak outcome).
Qed.

Definition reg_head_value (h : frontier_head regE Enum nat) : nat :=
  match h with
  | FHRet n => n
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition operational_reg_nested_observation : Enum nat :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _ reg_fair
    (fun side => @sem_bind Enum Enum_SemanticMeasureInterface _ _
      (reg_inner side) (fun outcome => sem_ret outcome)).

Definition operational_reg_merged_observation : Enum nat :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _ reg_merged_three
    (fun outcome => sem_ret outcome).

Lemma operational_reg_nested_observes :
  free_omega_observes reg_head_value operational_reg_nested_heads
    operational_reg_nested_observation.
Proof.
  unfold operational_reg_nested_heads, operational_reg_nested_observation.
  eapply FOOObserveSample.
  intro side. eapply FOOObserveSample. intro outcome. constructor.
Qed.

Lemma operational_reg_merged_observes :
  free_omega_observes reg_head_value operational_reg_merged_heads
    operational_reg_merged_observation.
Proof.
  unfold operational_reg_merged_heads, operational_reg_merged_observation.
  eapply FOOObserveSample.
  intro outcome. constructor.
Qed.

Lemma operational_reg_nested_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _
    operational_reg_nested_heads.
Proof.
  exists nat, reg_head_value, operational_reg_nested_observation.
  split; first exact operational_reg_nested_observes.
  vm_compute. reflexivity.
Qed.

Lemma operational_reg_merged_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _
    operational_reg_merged_heads.
Proof.
  exists nat, reg_head_value, operational_reg_merged_observation.
  split; first exact operational_reg_merged_observes.
  vm_compute. reflexivity.
Qed.

Lemma operational_reg_nested_ast :
  @operational_ast_weak regE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface nat
    (observe reg_nested_program) operational_reg_nested_heads.
Proof. split; [exact operational_reg_nested_weak|exact operational_reg_nested_total]. Qed.

Corollary operational_reg_nested_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' regE Enum nat) (frontier_head regE Enum nat)
    (@ptree_primitive_kernel regE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface nat)
    (observe reg_nested_program) operational_reg_nested_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe reg_nested_program) operational_reg_nested_heads)).
  exact operational_reg_nested_ast.
Qed.

Lemma operational_reg_nested_merged_lift
    (sim : ptree regE Enum nat -> ptree regE Enum nat -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
    operational_reg_nested_heads operational_reg_merged_heads.
Proof.
  eapply FOQLObserve with
    (obsA := reg_head_value) (obsB := reg_head_value)
    (outA := operational_reg_nested_observation)
    (outB := operational_reg_merged_observation)
    (S := eq).
  - exact operational_reg_nested_observes.
  - exact operational_reg_merged_observes.
  - eapply sem_lift_proper_l with
      (mu := operational_reg_merged_observation).
    + apply sem_eq_sym. unfold operational_reg_nested_observation,
        operational_reg_merged_observation.
      change (sem_eq
        (sem_bind reg_fair
          (fun side => sem_bind (reg_inner side) (fun x => sem_ret x)))
        (sem_bind reg_merged_three (fun x => sem_ret x))).
      eapply sem_eq_trans.
      * apply sem_eq_sym. apply sem_bind_assoc.
      * change (@meas_eq Enum Enum_MeasureInterface nat
          (meas_bind (bind_Enum reg_fair reg_inner) meas_ret)
          (meas_bind reg_merged_three meas_ret)).
        apply meas_bind_proper.
        -- exact (enum_meas_eq_of_eqenum reg_nested_outcomes_eqenum).
        -- intros x. apply meas_eq_refl.
    + apply sem_lift_refl. intros x. reflexivity.
  - intros h1 h2 Hvalue. destruct h1 as [n1|X e1 c1];
      destruct h2 as [n2|Y e2 c2]; try destruct e1; try destruct e2.
    cbn in Hvalue. subst n2. constructor. reflexivity.
  - unfold free_omega_support_lift, operational_reg_nested_heads,
      operational_reg_merged_heads. split.
    + intros P HP.
      pose proof (free_omega_ae_sample_inv HP) as Houter.
      assert (Hfalse : free_omega_ae P
          (FOSample (reg_inner false)
            (fun outcome => FORet (FHRet outcome)))).
      { apply Houter with (p := reg_half).
        - cbn. auto.
        - cbn. discriminate. }
      assert (Htrue : free_omega_ae P
          (FOSample (reg_inner true)
            (fun outcome => FORet (FHRet outcome)))).
      { apply Houter with (p := reg_half).
        - cbn. auto.
        - cbn. discriminate. }
      pose proof (free_omega_ae_sample_inv Hfalse) as Hfin.
      pose proof (free_omega_ae_sample_inv Htrue) as Htin.
      assert (HP0 : P (FHRet 0)).
      { specialize (Hfin reg_half 0). cbn in Hfin.
        pose proof (Hfin (or_introl eq_refl) ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      assert (HP1 : P (FHRet 1)).
      { specialize (Hfin reg_half 1). cbn in Hfin.
        pose proof (Hfin (or_intror (or_introl eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      assert (HP2 : P (FHRet 2)).
      { specialize (Htin reg_half 2). cbn in Htin.
        pose proof (Htin (or_intror (or_introl eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      eapply FOAESample with (Good := fun n => P (FHRet n)).
      * intros p n Hin Hnz. cbn in Hin.
        destruct Hin as [Hin|[Hin|[Hin|[]]]]; inversion Hin; subst;
          assumption.
      * intros n Hn. constructor. exists (FHRet n). split.
        -- constructor. reflexivity.
        -- exact Hn.
    + intros Q HQ.
      pose proof (free_omega_ae_sample_inv HQ) as Hmerged.
      assert (HQ0 : Q (FHRet 0)).
      { specialize (Hmerged reg_half 0). cbn in Hmerged.
        pose proof (Hmerged (or_introl eq_refl)
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      assert (HQ1 : Q (FHRet 1)).
      { specialize (Hmerged reg_quarter 1). cbn in Hmerged.
        pose proof (Hmerged (or_intror (or_introl eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      assert (HQ2 : Q (FHRet 2)).
      { specialize (Hmerged reg_quarter 2). cbn in Hmerged.
        pose proof (Hmerged (or_intror (or_intror (or_introl eq_refl)))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. assumption. }
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros side _. eapply FOAESample with (Good := fun n =>
          match n with 0 => True | 1 => side = false | 2 => side = true
          | _ => False end).
        -- intros p n Hin Hnz. destruct side; cbn in Hin |- *;
             destruct Hin as [Hin|[Hin|[]]]; inversion Hin; subst; auto.
        -- intros n Hn. constructor. exists (FHRet n). split.
           ++ constructor. reflexivity.
           ++ destruct side, n as [|[|[|n]]]; cbn in Hn |- *;
                try contradiction; assumption.
Qed.

Theorem operational_reg_nested_merged_bisim :
  @operational_bisim regE Enum MF
    Enum_SemanticMeasureInterface
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    Enum_SemanticMeasureCoreLaws
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface nat nat eq
    reg_nested_program reg_merged_program.
Proof.
  apply operational_bisim_fold. eapply OPBStable.
  - split; [exact operational_reg_nested_weak|exact operational_reg_nested_total].
  - split; [exact operational_reg_merged_weak|exact operational_reg_merged_total].
  - exact (operational_reg_nested_merged_lift _).
Qed.

Theorem primitive_reg_nested_merged_bisim :
  @primitive_ptree_bisim regE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface nat nat eq
    reg_nested_program reg_merged_program.
Proof.
  eapply primitive_ptree_bisim_of_ast_lift.
  - exact operational_reg_nested_ast.
  - split; [exact operational_reg_merged_weak|exact operational_reg_merged_total].
  - exact (operational_reg_nested_merged_lift _).
Qed.
