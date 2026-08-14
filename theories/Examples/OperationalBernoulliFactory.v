Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

From mathcomp Require Import ssralg rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew PStrong
  OperationalProbabilisticPTS OperationalProbabilisticPTSFreeOmega.
From PTree.Examples Require Import BernoulliFactory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Local Notation MF := (FreeOmega Enum).

Definition factoryE_no_event : forall X, factoryE X -> False :=
  fun X e => match e with end.

Section FactoryOperationalNormalization.
Variables pfalse ptrue : nnQ.

Definition operational_factory_pair_sample :
    ptree factoryE Enum (bool * bool) :=
  Prob (factory_biased_coin pfalse ptrue) (fun b1 =>
    Prob (factory_biased_coin pfalse ptrue) (fun b2 => Ret (b1, b2))).

Definition operational_factory_pair_round
    (_ : unit) (pair : bool * bool) : unit + bool :=
  let '(b1, b2) := pair in vn_round_result b1 b2.

Definition operational_factory_pair_step (_ : unit) :
    ptree factoryE Enum (unit + bool) :=
  PTree.bind operational_factory_pair_sample (fun pair =>
    Ret (operational_factory_pair_round tt pair)).

Definition operational_factory_pair_fair : ptree factoryE Enum bool :=
  PTree.iter operational_factory_pair_step tt.

Lemma factory_vn_step_pair_structural :
  pstructural eq (factory_vn_step pfalse ptrue tt)
    (operational_factory_pair_step tt).
Proof.
  unfold factory_vn_step, operational_factory_pair_step,
    operational_factory_pair_sample.
  apply pstructural_fold. rewrite observe_bind. cbn.
  constructor=> b1.
  apply pstructural_fold. rewrite observe_bind. cbn.
  constructor=> b2.
  apply observe_eq_pstructural. rewrite observe_bind. reflexivity.
Qed.

Theorem factory_fair_coin_pair_structural :
  pstructural eq (factory_fair_coin pfalse ptrue)
    operational_factory_pair_fair.
Proof.
  unfold factory_fair_coin, operational_factory_pair_fair.
  apply pstructural_iter. intros [].
  apply factory_vn_step_pair_structural.
Qed.

Lemma factory_fair_coin_pair_hitting fuel :
  free_omega_lift eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (factory_fair_coin pfalse ptrue)))
    (operational_hitting_approx (MF := MF) fuel
      (observe operational_factory_pair_fair)).
Proof.
  apply free_operational_hitting_pstructural_no_event.
  - exact factoryE_no_event.
  - apply factory_fair_coin_pair_structural.
Qed.

Local Notation factory_head A := (frontier_head factoryE Enum A).

Definition operational_factory_pair_heads : MF (factory_head (bool * bool)) :=
  @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool _
    (factory_biased_coin pfalse ptrue) (fun b1 =>
      @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool _
        (factory_biased_coin pfalse ptrue) (fun b2 =>
          FORet (FHRet (b1, b2)))).

Lemma operational_factory_pair_sample_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (bool * bool)
    (observe operational_factory_pair_sample)
    operational_factory_pair_heads.
Proof.
  unfold operational_factory_pair_sample, operational_factory_pair_heads.
  eapply operational_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b1 _. eapply operational_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros b2 _. apply operational_weak_ret.
Qed.

Definition operational_factory_fair_row (outer : nat) :
    MF (factory_head bool) :=
  free_nested_row_out factoryE_no_event operational_factory_pair_round
    operational_factory_pair_heads outer tt.

Definition operational_factory_fair_heads : MF (factory_head bool) :=
  FOLub operational_factory_fair_row.

Lemma operational_factory_pair_fair_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe operational_factory_pair_fair)
    operational_factory_fair_heads.
Proof.
  unfold operational_factory_pair_fair, operational_factory_pair_step.
  eapply free_operational_weak_of_canonical_nested
    with (sample_out := operational_factory_pair_heads).
  - exact operational_factory_pair_sample_weak.
  - unfold operational_factory_fair_heads, operational_factory_fair_row.
    apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

Theorem operational_factory_fair_coin_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (factory_fair_coin pfalse ptrue))
    operational_factory_fair_heads.
Proof.
  apply (proj2 (free_operational_weak_pstructural_no_event
    factoryE_no_event factory_fair_coin_pair_structural
    operational_factory_fair_heads)).
  exact operational_factory_pair_fair_weak.
Qed.

End FactoryOperationalNormalization.
