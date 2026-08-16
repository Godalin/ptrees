Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

From Coq Require Import FunctionalExtensionality Program.Equality.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts
  MeasureIteration MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure EnumMap.
From PTree.Eq Require Import ShallowNew UnifiedFrontier
  PrimitiveStableHitting OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega ProbabilisticEutt.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli
  BernoulliFactory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
Import GRing.Theory.
Import RatSubTypes.NonnegQNotations.
Local Open Scope ring_scope.

Local Notation MF := (FreeOmega Enum).

Definition factoryE_no_event : forall X, factoryE X -> False :=
  fun X e => match e with end.

Section FactoryOperationalNormalization.
Variables pfalse ptrue : nnQ.

Local Notation factory_head A := (frontier_head factoryE Enum A).

Polymorphic Definition operational_factory_head_value {X}
    (h : factory_head X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (factoryE_no_event e)
  end.

Fixpoint operational_factory_fair_measure_row (outer : nat) : Enum bool :=
  match outer with
  | O => nil
  | S outer' =>
      bind_Enum (factory_biased_coin pfalse ptrue) (fun b1 =>
        bind_Enum (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => operational_factory_fair_measure_row outer'
          | inr b => ret_Enum b
          end))
  end.

Lemma scale_Enum_one {X} (mu : Enum X) : scale_Enum 1 mu = mu.
Proof.
  induction mu as [|[w x] mu IH]; first reflexivity.
  simpl scale_Enum. rewrite mul1r IH. reflexivity.
Qed.

Lemma enum_cat_nil {X} (mu : Enum X) : (mu ++ nil)%list = mu.
Proof.
  induction mu as [|x mu IH]; first reflexivity.
  simpl. rewrite IH. reflexivity.
Qed.

Lemma operational_factory_fair_measure_row_eq outer :
  operational_factory_fair_measure_row outer =
    meas_iter_approx outer
      (fun _ : unit => factory_round_measure pfalse ptrue) tt.
Proof.
  induction outer as [|outer IH]; first reflexivity.
  cbn [operational_factory_fair_measure_row meas_iter_approx].
  unfold factory_round_measure.
  cbn [FrontierLift.meas_bind FrontierLift.meas_ret
    FrontierLiftEnum.Enum_MeasureInterface].
  rewrite bind_Enum_assoc. apply bind_Enum_ext=> b1.
  rewrite bind_Enum_assoc. apply bind_Enum_ext=> b2.
  destruct (vn_round_result b1 b2) as [[]|b].
  - rewrite IH. cbn [ret_Enum bind_Enum scale_Enum].
    fold (factory_round_measure pfalse ptrue).
    rewrite /ret_Enum /bind_Enum /=.
    rewrite scale_Enum_one.
    symmetry. apply enum_cat_nil.
  - rewrite /ret_Enum /bind_Enum /=.
    change (ret_Enum b = (scale_Enum 1 (ret_Enum b) ++ nil)%list).
    rewrite scale_Enum_one. symmetry. apply enum_cat_nil.
Qed.

Definition operational_factory_raw_after (next : unit + bool) :
    ptree factoryE Enum bool :=
  match next with
  | inl u => Tau (PTree.iter (factory_vn_step pfalse ptrue) u)
  | inr b => Ret b
  end.

Definition operational_factory_raw_second (b1 : bool) :
    ptree factoryE Enum bool :=
  PTree.bind
    (Prob (factory_biased_coin pfalse ptrue) (fun b2 =>
      Ret (vn_round_result b1 b2)))
    operational_factory_raw_after.

Lemma operational_factory_raw_observe :
  observe (factory_fair_coin pfalse ptrue) =
  ProbF (factory_biased_coin pfalse ptrue)
    operational_factory_raw_second.
Proof.
  unfold factory_fair_coin.
  pose proof (unfold_aloop_ (factory_vn_step pfalse ptrue) tt) as Hunfold.
  rewrite (observing_observe Hunfold). rewrite observe_bind.
  assert (Hstep : observe (factory_vn_step pfalse ptrue tt) =
    ProbF (factory_biased_coin pfalse ptrue) (fun b1 =>
      Prob (factory_biased_coin pfalse ptrue) (fun b2 =>
        Ret (vn_round_result b1 b2)))) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma operational_factory_raw_second_observe b1 :
  observe (operational_factory_raw_second b1) =
  ProbF (factory_biased_coin pfalse ptrue) (fun b2 =>
    PTree.bind (Ret (vn_round_result b1 b2))
      operational_factory_raw_after).
Proof.
  unfold operational_factory_raw_second. rewrite observe_bind. reflexivity.
Qed.

Definition operational_factory_raw_hitting (fuel : nat) : MF (factory_head bool) :=
  operational_hitting_approx (MF := MF) fuel
    (observe (factory_fair_coin pfalse ptrue)).

Lemma operational_factory_raw_hitting_three fuel :
  operational_factory_raw_hitting
    (Datatypes.S (Datatypes.S (Datatypes.S fuel))) =
  FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
    FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
      match vn_round_result b1 b2 with
      | inl _ => operational_factory_raw_hitting fuel
      | inr b => FORet (FHRet b)
      end)).
Proof.
  unfold operational_factory_raw_hitting.
  rewrite operational_factory_raw_observe.
  cbn [operational_hitting_approx operational_kernel operational_target_approx
    stable_hitting_approx stable_target_approx ptree_primitive_kernel
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality=> b1.
  rewrite operational_factory_raw_second_observe.
  cbn [operational_kernel operational_target_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret
    mixed_bind free_omega_bind FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality=> b2. rewrite observe_bind.
  destruct (vn_round_result b1 b2) as [[]|b]; reflexivity.
Qed.

Fixpoint operational_factory_raw_schedule (rounds : nat) : nat :=
  match rounds with
  | O => O
  | S rounds' => S (S (S (operational_factory_raw_schedule rounds')))
  end.

Lemma operational_factory_raw_hitting_zero_observes :
  free_omega_observes operational_factory_head_value
    (operational_factory_raw_hitting 0) (nil : Enum bool).
Proof.
  unfold operational_factory_raw_hitting.
  rewrite operational_factory_raw_observe.
  change (free_omega_observes operational_factory_head_value
    (FOSample (factory_biased_coin pfalse ptrue) (fun _ => FOZero))
    (nil : Enum bool)).
  rewrite <- (enum_bind_nil (A := bool) bool
    (factory_biased_coin pfalse ptrue)).
  constructor. intro b. constructor.
Qed.

Lemma operational_factory_raw_hitting_rounds_observes rounds :
  free_omega_observes operational_factory_head_value
    (operational_factory_raw_hitting
      (operational_factory_raw_schedule rounds))
    (operational_factory_fair_measure_row rounds).
Proof.
  induction rounds as [|rounds IH].
  - exact operational_factory_raw_hitting_zero_observes.
  - cbn [operational_factory_raw_schedule
      operational_factory_fair_measure_row].
    rewrite operational_factory_raw_hitting_three.
    change (free_omega_observes operational_factory_head_value
      (FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
        FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => operational_factory_raw_hitting
              (operational_factory_raw_schedule rounds)
          | inr b => FORet (FHRet b)
          end)))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _
        (factory_biased_coin pfalse ptrue) (fun b1 =>
          @sem_bind Enum Enum_SemanticMeasureInterface _ _
            (factory_biased_coin pfalse ptrue) (fun b2 =>
              match vn_round_result b1 b2 with
              | inl _ => operational_factory_fair_measure_row rounds
              | inr b => @sem_ret Enum Enum_SemanticMeasureInterface _ b
              end)))).
    constructor=> b1. constructor=> b2.
    destruct (vn_round_result b1 b2) as [[]|b]; [exact IH|constructor].
Qed.

Lemma operational_factory_raw_schedule_ge rounds :
  Peano.le rounds (operational_factory_raw_schedule rounds).
Proof.
  induction rounds as [|rounds IH]; [apply le_n|].
  cbn. apply le_n_S. apply le_S, le_S. exact IH.
Qed.

Lemma operational_factory_raw_chains_cofinal :
  free_omega_chains_cofinal eq operational_factory_raw_hitting
    (fun rounds => operational_factory_raw_hitting
      (operational_factory_raw_schedule rounds)).
Proof.
  split.
  - intro fuel. exists fuel. apply free_operational_hitting_mono.
    exact (operational_factory_raw_schedule_ge fuel).
  - intro rounds. exists (operational_factory_raw_schedule rounds).
    apply free_omega_approx_refl. intro h. reflexivity.
Qed.

Definition operational_factory_raw_heads : MF (factory_head bool) :=
  FOLub (fun rounds => operational_factory_raw_hitting
    (operational_factory_raw_schedule rounds)).

Theorem operational_factory_fair_coin_weak :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (factory_fair_coin pfalse ptrue))
    operational_factory_raw_heads.
Proof.
  unfold operational_weak, operational_factory_raw_heads,
    operational_factory_raw_hitting.
  cbn. apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal. exact operational_factory_raw_chains_cofinal.
  - intros x y ->. reflexivity.
Qed.

Lemma operational_factory_fair_heads_observes
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  free_omega_observes operational_factory_head_value
    operational_factory_raw_heads vn_fair.
Proof.
  unfold operational_factory_raw_heads. eapply FOOObserveLub.
  - exact operational_factory_raw_hitting_rounds_observes.
  - assert (Hrows : operational_factory_fair_measure_row =
      fun outer => meas_iter_approx outer
        (fun _ : unit => param_round_measure pfalse ptrue) tt).
    { apply functional_extensionality=> outer.
      rewrite operational_factory_fair_measure_row_eq.
      rewrite (factory_round_is_param_round pfalse ptrue). reflexivity. }
    rewrite Hrows.
    exact (param_iteration_converges_of_normalized_bias
      (p := pfalse) (q := ptrue) pnormalized pnontrivial).
Qed.

Lemma operational_factory_fair_heads_total
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _
    operational_factory_raw_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_factory_head_value, vn_fair.
  split.
  - exact (operational_factory_fair_heads_observes
      pnormalized pnontrivial).
  - exact vn_fair_total.
Qed.

Theorem operational_factory_fair_coin_ast
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  @operational_ast_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (factory_fair_coin pfalse ptrue))
    operational_factory_raw_heads.
Proof.
  split.
  - exact operational_factory_fair_coin_weak.
  - exact (operational_factory_fair_heads_total
      pnormalized pnontrivial).
Qed.

Section RationalTarget.
Variable q : rat.

Fixpoint operational_factory_binary_measure_row
    (rounds : nat) (x : rat) : Enum (rat + bool) :=
  match rounds with
  | O => nil
  | S rounds' =>
      bind_Enum (factory_biased_coin pfalse ptrue) (fun b1 =>
        bind_Enum (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => operational_factory_binary_measure_row rounds' x
          | inr b => ret_Enum (binary_round_result x b)
          end))
  end.

Lemma operational_factory_binary_measure_row_eq rounds x :
  operational_factory_binary_measure_row rounds x =
  bind_Enum (operational_factory_fair_measure_row rounds)
    (fun b => ret_Enum (binary_round_result x b)).
Proof.
  induction rounds as [|rounds IH]; first reflexivity.
  cbn [operational_factory_binary_measure_row
    operational_factory_fair_measure_row].
  rewrite bind_Enum_assoc. apply bind_Enum_ext=> b1.
  rewrite bind_Enum_assoc. apply bind_Enum_ext=> b2.
  destruct (vn_round_result b1 b2) as [[]|b].
  - exact IH.
  - rewrite /ret_Enum /bind_Enum /=.
    change (ret_Enum (binary_round_result x b) =
      (scale_Enum 1 (ret_Enum (binary_round_result x b)) ++ nil)%list).
    rewrite scale_Enum_one. symmetry. apply enum_cat_nil.
Qed.

Lemma enum_converges_bind_ret_map {A B}
    (chain : nat -> Enum A) out (f : A -> B) :
  enum_converges chain out ->
  enum_converges
    (fun n => bind_Enum (chain n) (fun a => ret_Enum (f a)))
    (bind_Enum out (fun a => ret_Enum (f a))).
Proof.
  intros H P eps Heps.
  destruct (H (fun a => P (f a)) eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite !enum_expect_bind.
  assert (Hret :
    (fun a : A => enum_expect (fun b : B =>
      if P b then (1 : rat) else 0) (ret_Enum (f a))) =
    (fun a : A => if P (f a) then (1 : rat) else 0)).
  { apply functional_extensionality=> a. apply enum_expect_ret. }
  rewrite Hret. exact HN.
Qed.

Lemma operational_factory_raw_hitting_rounds_observes_binary rounds x :
  free_omega_observes
    (fun h => binary_round_result x (operational_factory_head_value h))
    (operational_factory_raw_hitting
      (operational_factory_raw_schedule rounds))
    (operational_factory_binary_measure_row rounds x).
Proof.
  induction rounds as [|rounds IH].
  - unfold operational_factory_raw_hitting.
    rewrite operational_factory_raw_observe.
    change (free_omega_observes
      (fun h => binary_round_result x (operational_factory_head_value h))
      (FOSample (factory_biased_coin pfalse ptrue) (fun _ => FOZero))
      (nil : Enum (rat + bool))).
    rewrite <- (enum_bind_nil (A := bool) (rat + bool)
      (factory_biased_coin pfalse ptrue)).
    constructor=> b. constructor.
  - cbn [operational_factory_raw_schedule
      operational_factory_binary_measure_row].
    rewrite operational_factory_raw_hitting_three.
    change (free_omega_observes
      (fun h => binary_round_result x (operational_factory_head_value h))
      (FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
        FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => operational_factory_raw_hitting
              (operational_factory_raw_schedule rounds)
          | inr b => FORet (FHRet b)
          end)))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _
        (factory_biased_coin pfalse ptrue) (fun b1 =>
          @sem_bind Enum Enum_SemanticMeasureInterface _ _
            (factory_biased_coin pfalse ptrue) (fun b2 =>
              match vn_round_result b1 b2 with
              | inl _ => operational_factory_binary_measure_row rounds x
              | inr b => @sem_ret Enum Enum_SemanticMeasureInterface _
                  (binary_round_result x b)
              end)))).
    constructor=> b1. constructor=> b2.
    destruct (vn_round_result b1 b2) as [[]|b]; [exact IH|constructor].
Qed.

Lemma operational_factory_raw_heads_observes_binary
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) x :
  free_omega_observes
    (fun h => binary_round_result x (operational_factory_head_value h))
    operational_factory_raw_heads (binary_coin_transition x).
Proof.
  unfold operational_factory_raw_heads. eapply FOOObserveLub.
  - intro rounds.
    exact (operational_factory_raw_hitting_rounds_observes_binary rounds x).
  - assert (Hfair : enum_converges operational_factory_fair_measure_row
        vn_fair).
    { assert (Hrows : operational_factory_fair_measure_row =
        fun rounds => meas_iter_approx rounds
          (fun _ : unit => param_round_measure pfalse ptrue) tt).
      { apply functional_extensionality=> rounds.
        rewrite operational_factory_fair_measure_row_eq.
        rewrite (factory_round_is_param_round pfalse ptrue). reflexivity. }
      rewrite Hrows. exact (param_iteration_converges_of_normalized_bias
        (p := pfalse) (q := ptrue) pnormalized pnontrivial). }
    pose proof (@enum_converges_bind_ret_map bool (rat + bool)
      operational_factory_fair_measure_row vn_fair
      (fun b => binary_round_result x b) Hfair)
      as Hmap.
    assert (Hchain : (fun rounds =>
        operational_factory_binary_measure_row rounds x) =
      fun rounds => bind_Enum (operational_factory_fair_measure_row rounds)
        (fun b => ret_Enum (binary_round_result x b))).
    { apply functional_extensionality=> rounds.
      apply operational_factory_binary_measure_row_eq. }
    rewrite Hchain. rewrite <- fair_binary_round_measure. exact Hmap.
Qed.

Definition operational_factory_binary_step_heads (x : rat) :
    MF (factory_head (rat + bool)) :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    operational_factory_raw_heads
    (frontier_head_bind_front
      (fun b => Ret (binary_round_result x b) : ptree factoryE Enum _)
      (fun b => FORet (FHRet (binary_round_result x b)))).

Lemma operational_factory_binary_ret_weak (next : rat + bool) :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (rat + bool)
    (observe (Ret next)) (FORet (FHRet next)).
Proof.
  assert (Hobserve : observe
    (Ret next : ptree factoryE Enum (rat + bool)) = RetF next)
    by reflexivity.
  rewrite Hobserve. apply (operational_weak_ret
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface) (E := factoryE)).
Qed.

Lemma operational_factory_binary_step_weak x :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (rat + bool)
    (observe (factory_binary_step pfalse ptrue x))
    (operational_factory_binary_step_heads x).
Proof.
  unfold factory_binary_step, operational_factory_binary_step_heads.
  eapply (operational_weak_bind
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface)).
  - apply free_operational_bind_cofinal_no_event. exact factoryE_no_event.
  - exact operational_factory_fair_coin_weak.
  - intro b. apply operational_factory_binary_ret_weak.
Qed.

Lemma operational_factory_binary_step_heads_observes
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) x :
  free_omega_observes
    (free_iter_head_next factoryE_no_event)
    (operational_factory_binary_step_heads x)
    (binary_coin_transition x).
Proof.
  unfold operational_factory_binary_step_heads.
  assert (Hfront :
    frontier_head_bind_front
      (fun b => Ret (binary_round_result x b) : ptree factoryE Enum _)
      (fun b => FORet (FHRet (binary_round_result x b))) =
    (fun h => FORet (FHRet (binary_round_result x
      (operational_factory_head_value h))))).
  { apply functional_extensionality=> h.
    destruct h as [b|X e k]; [reflexivity|destruct e]. }
  rewrite Hfront.
  eapply free_omega_observes_bind_ret
    with (obsA := fun h => binary_round_result x
      (operational_factory_head_value h)).
  - exact (operational_factory_raw_heads_observes_binary
      pnormalized pnontrivial x).
  - intro h. destruct h as [b|X e k]; [reflexivity|destruct e].
Qed.

(** The target of the implementation proof is the standard one-step
    distribution, embedded once into the free omega completion.  This is
    deliberately independent of the implementation's unbounded raw-coin
    schedule. *)
Definition operational_factory_standard_step_heads (x : rat) :
    MF (factory_head (rat + bool)) :=
  FOSample (binary_coin_transition x) (fun next => FORet (FHRet next)).

Lemma operational_factory_standard_step_heads_observes x :
  free_omega_observes
    (free_iter_head_next factoryE_no_event)
    (operational_factory_standard_step_heads x)
    (@sem_bind Enum Enum_SemanticMeasureInterface _ _
      (binary_coin_transition x) (fun next =>
        @sem_ret Enum Enum_SemanticMeasureInterface _ next)).
Proof.
  unfold operational_factory_standard_step_heads.
  eapply FOOObserveSample with
    (front := fun next : rat + bool =>
      @sem_ret Enum Enum_SemanticMeasureInterface _ next).
  intro next. constructor.
Qed.

Class OperationalFactoryStepSupportLaws := {
  operational_factory_binary_step_support : forall
      (pnormalized : Qval pfalse + Qval ptrue = 1)
      (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) x,
    free_omega_support_lift eq
      (operational_factory_binary_step_heads x)
      (operational_factory_standard_step_heads x)
}.

Context `{FactoryStepSupport : OperationalFactoryStepSupportLaws}.

Lemma operational_factory_binary_step_heads_lift
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) x :
  free_omega_qlift eq
    (operational_factory_binary_step_heads x)
    (operational_factory_standard_step_heads x).
Proof.
  eapply FOQLObserve with
    (obsA := free_iter_head_next factoryE_no_event)
    (obsB := free_iter_head_next factoryE_no_event)
    (outA := binary_coin_transition x)
    (outB := @sem_bind Enum Enum_SemanticMeasureInterface _ _
      (binary_coin_transition x) (fun next =>
        @sem_ret Enum Enum_SemanticMeasureInterface _ next)) (S := eq).
  - exact (operational_factory_binary_step_heads_observes
      pnormalized pnontrivial x).
  - exact (operational_factory_standard_step_heads_observes x).
  - cbn [sem_bind sem_ret Enum_SemanticMeasureInterface
      FrontierLift.meas_bind FrontierLift.meas_ret
      FrontierLiftEnum.Enum_MeasureInterface].
    rewrite bind_ret_emap emap_id.
    apply sem_lift_refl. intros next. reflexivity.
  - intros h1 h2 Hnext.
    destruct h1 as [next1|X e1 k1];
      destruct h2 as [next2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hnext. subst next2. reflexivity.
  - exact (operational_factory_binary_step_support
      pnormalized pnontrivial x).
Qed.

Fixpoint operational_factory_standard_q_row
    (outer : nat) (x : rat) : MF (factory_head bool) :=
  match outer with
  | O => FOZero
  | S outer' =>
      free_omega_bind (operational_factory_standard_step_heads x) (fun h =>
        match free_iter_head_next factoryE_no_event h with
        | inl x' => operational_factory_standard_q_row outer' x'
        | inr b => FORet (FHRet b)
        end)
  end.

Definition operational_factory_standard_q_heads : MF (factory_head bool) :=
  FOLub (fun outer => operational_factory_standard_q_row outer q).

Lemma operational_factory_q_row_lift
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  forall outer x,
    free_omega_qlift eq
      (free_iter_complete_rows factoryE_no_event
        operational_factory_binary_step_heads outer x)
      (operational_factory_standard_q_row outer x).
Proof.
  induction outer as [|outer IH]; intro x.
  - apply free_omega_qlift_refl. intros h. reflexivity.
  - cbn [free_iter_complete_rows operational_factory_standard_q_row].
    eapply FOQLBind with (T := eq).
    + exact (operational_factory_binary_step_heads_lift
        pnormalized pnontrivial x).
    + intros h1 h2 ->. destruct (free_iter_head_next factoryE_no_event h2)
        as [x'|b].
      * apply IH.
      * apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

Definition operational_factory_q_row (outer : nat) :
    MF (factory_head bool) :=
  free_iter_complete_rows factoryE_no_event
    operational_factory_binary_step_heads outer q.

Definition operational_factory_q_heads : MF (factory_head bool) :=
  FOLub operational_factory_q_row.

Lemma operational_factory_q_heads_lift_standard
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  free_omega_qlift eq operational_factory_q_heads
    operational_factory_standard_q_heads.
Proof.
  unfold operational_factory_q_heads, operational_factory_q_row,
    operational_factory_standard_q_heads.
  apply FOQLLub. intro outer.
  exact (operational_factory_q_row_lift pnormalized pnontrivial outer q).
Qed.

Lemma operational_factory_standard_q_row_observes : forall outer x,
  free_omega_observes operational_factory_head_value
    (operational_factory_standard_q_row outer x)
    (meas_iter_approx outer binary_coin_transition x).
Proof.
  induction outer as [|outer IH]; intro x.
  - constructor.
  - cbn [operational_factory_standard_q_row meas_iter_approx
      operational_factory_standard_step_heads free_omega_bind].
    change (free_omega_observes operational_factory_head_value
      (FOSample (binary_coin_transition x) (fun next : rat + bool =>
        match next with
        | inl x' => operational_factory_standard_q_row outer x'
        | inr b => FORet (FHRet b)
        end))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _
        (binary_coin_transition x) (fun next : rat + bool =>
          match next with
          | inl x' => meas_iter_approx outer binary_coin_transition x'
          | inr b => @sem_ret Enum Enum_SemanticMeasureInterface _ b
          end))).
    eapply FOOObserveSample with (front := fun next : rat + bool =>
      match next with
      | inl x' => meas_iter_approx outer binary_coin_transition x'
      | inr b => ret_Enum b
      end).
    intros [x'|b].
    + apply IH.
    + constructor.
Qed.

Lemma operational_factory_standard_q_heads_observes
    (q0 : 0 <= q) (q1 : q <= 1) :
  free_omega_observes operational_factory_head_value
    operational_factory_standard_q_heads
    (rational_bernoulli_measure q0 q1).
Proof.
  unfold operational_factory_standard_q_heads.
  eapply FOOObserveLub.
  - intro outer. apply operational_factory_standard_q_row_observes.
  - exact (rational_binary_iteration_converges q0 q1).
Qed.

Lemma operational_factory_standard_q_heads_total
    (q0 : 0 <= q) (q1 : q <= 1) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _
    operational_factory_standard_q_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_factory_head_value,
    (rational_bernoulli_measure q0 q1).
  split.
  - exact (operational_factory_standard_q_heads_observes q0 q1).
  - exact (rational_bernoulli_total q0 q1).
Qed.

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
  unfold biased_to_rational_coin.
  eapply free_operational_weak_iter_of_unbounded_steps
    with (step_out := operational_factory_binary_step_heads).
  - exact operational_factory_binary_step_weak.
  - unfold operational_factory_q_heads, operational_factory_q_row.
    apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

Theorem operational_biased_to_rational_coin_weak_standard
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q) :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (biased_to_rational_coin pfalse ptrue q))
    operational_factory_standard_q_heads.
Proof.
  pose proof operational_biased_to_rational_coin_weak as Hweak.
  unfold operational_weak in Hweak |- *.
  eapply sem_eq_trans.
  - apply sem_eq_sym.
    exact (operational_factory_q_heads_lift_standard
      pnormalized pnontrivial).
  - exact Hweak.
Qed.

Theorem operational_biased_to_rational_coin_ast
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @operational_ast_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (biased_to_rational_coin pfalse ptrue q))
    operational_factory_standard_q_heads.
Proof.
  split.
  - exact (operational_biased_to_rational_coin_weak_standard
      pnormalized pnontrivial).
  - exact (operational_factory_standard_q_heads_total q0 q1).
Qed.

Corollary operational_biased_to_rational_coin_primitive_ast
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' factoryE Enum bool) (factory_head bool)
    (@ptree_primitive_kernel factoryE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface bool)
    (observe (biased_to_rational_coin pfalse ptrue q))
    operational_factory_standard_q_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe (biased_to_rational_coin pfalse ptrue q))
    operational_factory_standard_q_heads)).
  exact (operational_biased_to_rational_coin_ast
    pnormalized pnontrivial q0 q1).
Qed.

Definition operational_factory_direct_q_heads
    (q0 : 0 <= q) (q1 : q <= 1) : MF (factory_head bool) :=
  @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool _
    (rational_bernoulli_measure q0 q1)
    (fun b => FORet (FHRet b)).

Definition operational_factory_direct_q_observation
    (q0 : 0 <= q) (q1 : q <= 1) : Enum bool :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _
    (rational_bernoulli_measure q0 q1) (fun b =>
      @sem_ret Enum Enum_SemanticMeasureInterface _ b).

Lemma operational_factory_direct_q_heads_observes
    (q0 : 0 <= q) (q1 : q <= 1) :
  free_omega_observes operational_factory_head_value
    (operational_factory_direct_q_heads q0 q1)
    (operational_factory_direct_q_observation q0 q1).
Proof.
  unfold operational_factory_direct_q_heads,
    operational_factory_direct_q_observation.
  eapply FOOObserveSample with (front := fun b : bool => ret_Enum b).
  intro b. constructor.
Qed.

Lemma operational_factory_direct_q_observation_eq
    (q0 : 0 <= q) (q1 : q <= 1) :
  operational_factory_direct_q_observation q0 q1 =
    rational_bernoulli_measure q0 q1.
Proof.
  unfold operational_factory_direct_q_observation.
  cbn [sem_bind sem_ret Enum_SemanticMeasureInterface
    FrontierLift.meas_bind FrontierLift.meas_ret
    FrontierLiftEnum.Enum_MeasureInterface].
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma operational_factory_direct_q_heads_total
    (q0 : 0 <= q) (q1 : q <= 1) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _
    (operational_factory_direct_q_heads q0 q1).
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_factory_head_value,
    (operational_factory_direct_q_observation q0 q1).
  split; [apply operational_factory_direct_q_heads_observes|].
  rewrite operational_factory_direct_q_observation_eq.
  exact (rational_bernoulli_total q0 q1).
Qed.

Theorem operational_factory_direct_q_ast
    (q0 : 0 <= q) (q1 : q <= 1) :
  @operational_ast_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (factory_direct_q q0 q1))
    (operational_factory_direct_q_heads q0 q1).
Proof.
  assert (Hobserve : observe (factory_direct_q q0 q1) =
    ProbF (rational_bernoulli_measure q0 q1) (fun b => Ret b))
    by reflexivity.
  rewrite Hobserve.
  eapply operational_ast_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + assert (Hb : observe (Ret b : ptree factoryE Enum bool) = RetF b)
        by reflexivity.
      rewrite Hb. apply (operational_weak_ret
        (FI := FreeOmegaObservableSemanticMeasureInterface)
        (FO := FreeOmegaObservableSemanticOmegaInterface)
        (MX := FreeOmegaMixedMeasureInterface) (E := factoryE)).
    + apply free_omega_observable_total_intro.
      exists bool, operational_factory_head_value,
        (@sem_ret Enum Enum_SemanticMeasureInterface bool b).
      split; [constructor|].
      change (enum_expect (fun _ : bool => (1 : rat)) (ret_Enum b) = 1).
      rewrite enum_expect_ret. reflexivity.
  - exact (operational_factory_direct_q_heads_total q0 q1).
Qed.

Class OperationalFactoryRationalSupportLaws := {
  operational_factory_standard_q_support : forall
      (q0 : 0 <= q) (q1 : q <= 1)
      (sim : ptree factoryE Enum bool -> ptree factoryE Enum bool -> Prop),
    free_omega_support_lift (frontier_head_rel eq sim)
      operational_factory_standard_q_heads
      (operational_factory_direct_q_heads q0 q1)
}.

Context `{FactoryRationalSupport : OperationalFactoryRationalSupportLaws}.

Lemma operational_factory_standard_q_heads_lift_direct
    (q0 : 0 <= q) (q1 : q <= 1)
    (sim : ptree factoryE Enum bool -> ptree factoryE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
    operational_factory_standard_q_heads
    (operational_factory_direct_q_heads q0 q1).
Proof.
  eapply FOQLObserve with
    (obsA := operational_factory_head_value)
    (obsB := operational_factory_head_value)
    (outA := rational_bernoulli_measure q0 q1)
    (outB := operational_factory_direct_q_observation q0 q1)
    (S := eq).
  - exact (operational_factory_standard_q_heads_observes q0 q1).
  - exact (operational_factory_direct_q_heads_observes q0 q1).
  - rewrite operational_factory_direct_q_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - exact (operational_factory_standard_q_support q0 q1 sim).
Qed.

Theorem probabilistic_eutt_biased_to_rational_coin_direct
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : (0 < Qval pfalse * Qval ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @probabilistic_eutt factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface
    bool bool eq
    (biased_to_rational_coin pfalse ptrue q) (factory_direct_q q0 q1).
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 (operational_biased_to_rational_coin_ast
      pnormalized pnontrivial q0 q1)).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 (operational_factory_direct_q_ast q0 q1)).
  - exact (operational_factory_standard_q_heads_lift_direct q0 q1 _).
Qed.

End RationalTarget.

End FactoryOperationalNormalization.

Definition operational_third_to_two_fifths_heads :
    MF (frontier_head factoryE Enum bool) :=
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

Theorem probabilistic_eutt_third_to_two_fifths_direct
    `{OperationalFactoryStepSupportLaws vn_one_third vn_two_thirds}
    `{OperationalFactoryRationalSupportLaws (2 / 5)} :
  @probabilistic_eutt factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface
    bool bool eq third_to_two_fifths direct_two_fifths.
Proof.
  exact (probabilistic_eutt_biased_to_rational_coin_direct
    (pfalse := vn_one_third) (ptrue := vn_two_thirds) (q := 2 / 5)
    third_bias_normalized third_bias_nontrivial
    two_fifths_nonnegative two_fifths_at_most_one).
Qed.
