Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  TwoLevelMeasure TwoLevelMeasureEnum.
From PTree.Eq Require Import UnifiedFrontier UnifiedPWeak
  UnifiedPWeakEnumFacts.
From PTree.Examples Require Import VonNeumannUnbounded BernoulliFactory.
From PTree.Examples Require Import EnumMeasureRegression.

Import Enum.

(** A genuinely finite regression for the unified relation.  The left tree
    has two probability nodes and duplicated mass for outcome zero; the
    right tree has one three-point node.  This proof uses the new frontier
    directly rather than transporting a legacy [apweak] derivation. *)
Definition unified_reg_nested_heads :
    Enum (frontier_head regE Enum nat) :=
  mixed_bind reg_fair (fun side =>
    mixed_bind (reg_inner side) (fun outcome => sem_ret (FHRet outcome))).

Definition unified_reg_merged_heads :
    Enum (frontier_head regE Enum nat) :=
  mixed_bind reg_merged_three (fun outcome => sem_ret (FHRet outcome)).

Lemma unified_reg_nested_frontier :
  frontier (observe reg_nested_program) unified_reg_nested_heads.
Proof.
  unfold reg_nested_program, unified_reg_nested_heads.
  eapply UFProb with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros side _. eapply UFProb with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros outcome _. constructor.
Qed.

Lemma unified_reg_merged_frontier :
  frontier (observe reg_merged_program) unified_reg_merged_heads.
Proof.
  unfold reg_merged_program, unified_reg_merged_heads.
  eapply UFProb with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros outcome _. constructor.
Qed.

Lemma unified_reg_nested_merged_eq :
  sem_eq unified_reg_nested_heads unified_reg_merged_heads.
Proof.
  unfold unified_reg_nested_heads, unified_reg_merged_heads.
  change (sem_eq
    (sem_bind reg_fair (fun side =>
      sem_bind (reg_inner side) (fun outcome =>
        sem_ret (FHRet outcome : frontier_head regE Enum nat))))
    (sem_bind reg_merged_three (fun outcome =>
      sem_ret (FHRet outcome : frontier_head regE Enum nat)))).
  eapply sem_eq_trans.
  - apply sem_eq_sym. apply sem_bind_assoc.
  - change (@meas_eq Enum Enum_MeasureInterface _
      (meas_bind (bind_Enum reg_fair reg_inner)
        (fun outcome => meas_ret
          (FHRet outcome : frontier_head regE Enum nat)))
      (meas_bind reg_merged_three
        (fun outcome => meas_ret
          (FHRet outcome : frontier_head regE Enum nat)))).
    apply meas_bind_proper.
    + exact (enum_meas_eq_of_eqenum reg_nested_outcomes_eqenum).
    + intros outcome. apply meas_eq_refl.
Qed.

Lemma unified_reg_nested_merged_lift sim :
  sem_lift (frontier_head_rel eq sim)
    unified_reg_nested_heads unified_reg_merged_heads.
Proof.
  eapply sem_lift_mono.
  - intros h1 h2 ->. destruct h2 as [outcome|X e k].
    + constructor. reflexivity.
    + destruct e.
  - eapply sem_lift_proper_l with (mu := unified_reg_merged_heads).
    + apply sem_eq_sym. exact unified_reg_nested_merged_eq.
    + apply sem_lift_refl. intros h. reflexivity.
Qed.

Theorem unified_reg_nested_merged_weak_bisim :
  @weak_bisim regE Enum Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    nat nat eq reg_nested_program reg_merged_program.
Proof.
  apply weak_bisim_fold. eapply UWBFrontier.
  - exact unified_reg_nested_frontier.
  - exact unified_reg_merged_frontier.
  - exact (unified_reg_nested_merged_lift _).
Qed.

(** An unbounded almost-surely terminating sampler is weakly bisimilar, in
    the new single-frontier semantics, to one terminating fair sample. *)
Theorem unified_von_neumann_third_equivalent_to_fair :
  @weak_bisim vnE Enum.Enum Enum.Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    bool bool eq von_neumann_third direct_fair.
Proof.
  apply auweak_to_weak_bisim.
  exact von_neumann_third_equivalent_to_fair.
Qed.

(** Closed p-to-q Bernoulli factory example: repeated samples from a [1/3]
    coin implement a direct [2/5] coin, including both unbounded loops. *)
Theorem unified_third_coin_simulates_two_fifths :
  @weak_bisim factoryE Enum.Enum Enum.Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    bool bool eq third_to_two_fifths direct_two_fifths.
Proof.
  apply auweak_to_weak_bisim.
  exact (proj2 (proj2 third_coin_simulates_two_fifths_correct)).
Qed.
