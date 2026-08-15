Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

From Coq Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts
  MeasureIteration MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew PStrong
  UnifiedFrontier PrimitiveStableHitting OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli
  BernoulliFactory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory.
Import RatSubTypes.NonnegQNotations.
Local Open Scope ring_scope.

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

Polymorphic Definition operational_factory_head_value {X}
    (h : factory_head X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (factoryE_no_event e)
  end.

Lemma operational_factory_pair_ret_weak (x : bool * bool) :
  @operational_weak factoryE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (bool * bool)
    (observe (Ret x)) (FORet (FHRet x)).
Proof.
  assert (Hobserve : observe
    (Ret x : ptree factoryE Enum (bool * bool)) = RetF x)
    by reflexivity.
  rewrite Hobserve. apply (operational_weak_ret
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface) (E := factoryE)).
Qed.

Lemma operational_factory_pair_heads_observes :
  free_omega_observes operational_factory_head_value
    operational_factory_pair_heads operational_factory_pair_measure.
Proof.
  unfold operational_factory_pair_heads, operational_factory_pair_measure.
  change (free_omega_observes operational_factory_head_value
    (FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
      FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
        FORet (FHRet (b1, b2)))))
    (@sem_bind Enum Enum_SemanticMeasureInterface _ _
      (factory_biased_coin pfalse ptrue) (fun b1 =>
        @sem_bind Enum Enum_SemanticMeasureInterface _ _
          (factory_biased_coin pfalse ptrue) (fun b2 =>
            @sem_ret Enum Enum_SemanticMeasureInterface _ (b1, b2))))).
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
    + intros b2 _. apply operational_factory_pair_ret_weak.
Qed.

Definition operational_factory_fair_row (outer : nat) :
    MF (factory_head bool) :=
  free_nested_row_out factoryE_no_event operational_factory_pair_round
    operational_factory_pair_heads outer tt.

Definition operational_factory_fair_heads : MF (factory_head bool) :=
  FOLub operational_factory_fair_row.

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

Lemma operational_factory_fair_row_observes outer :
  free_omega_observes operational_factory_head_value
    (operational_factory_fair_row outer)
    (operational_factory_fair_measure_row outer).
Proof.
  induction outer as [|outer IH].
  - constructor.
  - unfold operational_factory_fair_row.
    cbn [free_nested_row_out operational_factory_pair_heads
      operational_factory_pair_round free_no_event_head_value
      free_no_event_head_value_for
      free_omega_bind mixed_bind FreeOmegaMixedMeasureInterface
      meas_iter_approx].
    cbn [operational_factory_fair_measure_row
      operational_factory_pair_round operational_factory_head_value
      free_no_event_head_value].
    change (free_omega_observes operational_factory_head_value
      (FOSample (factory_biased_coin pfalse ptrue) (fun b1 =>
        FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl i' => free_nested_row_out factoryE_no_event
              operational_factory_pair_round operational_factory_pair_heads
              outer i'
          | inr b => FORet (FHRet b)
          end)))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _
        (factory_biased_coin pfalse ptrue) (fun b1 =>
          @sem_bind Enum Enum_SemanticMeasureInterface _ _
            (factory_biased_coin pfalse ptrue) (fun b2 =>
              match vn_round_result b1 b2 with
              | inl _ => operational_factory_fair_measure_row outer
              | inr b => @sem_ret Enum Enum_SemanticMeasureInterface _ b
              end)))).
    eapply FOOObserveSample. intro b1.
    eapply FOOObserveSample. intro b2.
    destruct (vn_round_result b1 b2) as [u|b].
    + destruct u. exact IH.
    + constructor.
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
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality=> b1.
  rewrite operational_factory_raw_second_observe.
  cbn [operational_kernel operational_target_approx sem_bind sem_ret
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

Definition operational_factory_q_row (outer : nat) :
    MF (factory_head bool) :=
  free_iter_complete_rows factoryE_no_event
    operational_factory_binary_step_heads outer q.

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
  unfold biased_to_rational_coin.
  eapply free_operational_weak_iter_of_unbounded_steps
    with (step_out := operational_factory_binary_step_heads).
  - exact operational_factory_binary_step_weak.
  - unfold operational_factory_q_heads, operational_factory_q_row.
    apply free_omega_qlift_refl. intros h. reflexivity.
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
