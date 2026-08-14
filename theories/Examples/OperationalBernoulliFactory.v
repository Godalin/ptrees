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

Definition operational_factory_pair_measure : Enum (bool * bool) :=
  bind_Enum (factory_biased_coin pfalse ptrue) (fun b1 =>
    bind_Enum (factory_biased_coin pfalse ptrue) (fun b2 =>
      ret_Enum (b1, b2))).

Definition operational_factory_head_value {X}
    (h : factory_head X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (factoryE_no_event e)
  end.

Lemma operational_factory_pair_heads_observes :
  free_omega_observes operational_factory_head_value
    operational_factory_pair_heads operational_factory_pair_measure.
Proof.
  unfold operational_factory_pair_heads, operational_factory_pair_measure.
  eapply FOOObserveSample. intro b1.
  eapply FOOObserveSample. intro b2. constructor.
Qed.

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

Lemma operational_factory_fair_row_observes outer :
  free_omega_observes operational_factory_head_value
    (operational_factory_fair_row outer)
    (meas_iter_approx outer
      (fun _ : unit => factory_round_measure pfalse ptrue) tt).
Proof.
  induction outer as [|outer IH].
  - constructor.
  - unfold operational_factory_fair_row.
    cbn [free_nested_row_out operational_factory_pair_heads
      operational_factory_pair_round free_no_event_head_value
      free_omega_bind mixed_bind FreeOmegaMixedMeasureInterface
      meas_iter_approx].
    unfold factory_round_measure.
    change (free_omega_observes operational_factory_head_value
      (FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
        FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => operational_factory_fair_row outer
          | inr b => FORet (FHRet b)
          end)))
      (bind_Enum (factory_biased_coin pfalse ptrue) (fun b1 =>
        bind_Enum (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => meas_iter_approx outer
              (fun _ : unit => factory_round_measure pfalse ptrue) tt
          | inr b => ret_Enum b
          end)))).
    eapply FOOObserveSample. intro b1.
    eapply FOOObserveSample. intro b2.
    destruct (vn_round_result b1 b2) as [u|b].
    + destruct u. exact IH.
    + constructor.
Qed.

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

Lemma operational_factory_fair_heads_observes
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : 0 < Qval pfalse * Qval ptrue) :
  free_omega_observes operational_factory_head_value
    operational_factory_fair_heads vn_fair.
Proof.
  unfold operational_factory_fair_heads. eapply FOOObserveLub.
  - exact operational_factory_fair_row_observes.
  - rewrite (factory_round_is_param_round pfalse ptrue).
    exact (param_iteration_converges_of_normalized_bias
      (p := pfalse) (q := ptrue) pnormalized pnontrivial).
Qed.

Lemma operational_factory_fair_heads_total
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : 0 < Qval pfalse * Qval ptrue) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _
    operational_factory_fair_heads.
Proof.
  exists bool, operational_factory_head_value, vn_fair.
  split.
  - exact (operational_factory_fair_heads_observes
      pnormalized pnontrivial).
  - exact vn_fair_total.
Qed.

Theorem operational_factory_fair_coin_ast
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : 0 < Qval pfalse * Qval ptrue) :
  @operational_ast_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (factory_fair_coin pfalse ptrue))
    operational_factory_fair_heads.
Proof.
  split.
  - exact operational_factory_fair_coin_weak.
  - exact (operational_factory_fair_heads_total
      pnormalized pnontrivial).
Qed.

Section RationalTarget.
Variable q : rat.

Definition operational_factory_q_row (outer : nat) :
    MF (factory_head bool) :=
  free_nested_row_out factoryE_no_event binary_round_result
    operational_factory_fair_heads outer q.

Definition operational_factory_q_heads : MF (factory_head bool) :=
  FOLub operational_factory_q_row.

Theorem operational_biased_to_rational_coin_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (biased_to_rational_coin pfalse ptrue q))
    operational_factory_q_heads.
Proof.
  unfold biased_to_rational_coin, factory_binary_step.
  eapply free_operational_weak_of_canonical_nested
    with (sample_out := operational_factory_fair_heads).
  - exact operational_factory_fair_coin_weak.
  - unfold operational_factory_q_heads, operational_factory_q_row.
    apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

End RationalTarget.

End FactoryOperationalNormalization.

Definition operational_third_to_two_fifths_heads :
    MF (factory_head bool) :=
  operational_factory_q_heads vn_one_third vn_two_thirds (2 / 5).

Theorem operational_third_to_two_fifths_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe third_to_two_fifths)
    operational_third_to_two_fifths_heads.
Proof.
  exact (operational_biased_to_rational_coin_weak
    vn_one_third vn_two_thirds (2 / 5)).
Qed.
