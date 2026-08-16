Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import FunctionalExtensionality Program.Equality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order
  rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration MeasureIterationEnum
  EnumMap.
From PTree.Eq Require Import ShallowNew PrimitiveStableHitting
  OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega UnifiedFrontier
  ProbabilisticEutt.
From PTree.Examples Require Import RationalBernoulli.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Local Notation MF := (FreeOmega Enum).
Local Notation rational_head :=
  (frontier_head rational_coinE Enum bool).

Section OperationalRationalCoin.
Variable q : rat.
Hypothesis q0 : 0 <= q.
Hypothesis q1 : q <= 1.

Definition operational_rational_iter_approx (fuel : nat) : MF bool :=
  @mixed_iter_approx Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface rat bool fuel
    binary_coin_transition q.

Definition operational_rational_head_approx (fuel : nat) : MF rational_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (operational_rational_iter_approx fuel)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) rational_head (FHRet b)).

Definition operational_rational_limit : MF bool :=
  FOLub operational_rational_iter_approx.

Lemma operational_rational_increasing :
  @sem_increasing MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface bool
    operational_rational_iter_approx.
Proof.
  intro fuel. unfold operational_rational_iter_approx.
  clear q0 q1. revert q. induction fuel as [|fuel IH]; intro x.
  - cbn [mixed_iter_approx]. constructor.
  - cbn [mixed_iter_approx].
    eapply FOApproxSample with (S := @eq (rat + bool)).
    + apply sem_lift_refl. intros next. reflexivity.
    + intros next next' ->. destruct next' as [x'|b].
      * apply IH.
      * apply free_omega_approx_refl. intros y. reflexivity.
Qed.

Lemma operational_rational_mixed_iter :
  @mixed_iter Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface rat bool
    binary_coin_transition q operational_rational_limit.
Proof.
  unfold mixed_iter, operational_rational_limit,
    operational_rational_iter_approx.
  apply free_omega_qlift_refl. intros b. reflexivity.
Qed.

Lemma operational_rational_approx_observes fuel : forall x,
  free_omega_observes (fun b : bool => b)
    (@mixed_iter_approx Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface rat bool fuel
      binary_coin_transition x)
    (meas_iter_approx fuel binary_coin_transition x).
Proof.
  induction fuel as [|fuel IH]; intro x.
  - constructor.
  - cbn [mixed_iter_approx meas_iter_approx mixed_bind
      FreeOmegaMixedMeasureInterface sem_bind
      Enum_SemanticMeasureInterface].
    change (free_omega_observes (fun b : bool => b)
      (FOSample (binary_coin_transition x)
        (fun next : rat + bool =>
          match next with
          | inl x' => @mixed_iter_approx Enum MF
              (FreeOmegaObservableSemanticMeasureInterface
                (NI := Enum_SemanticMeasureInterface)
                (NO := Enum_SemanticOmegaInterface))
              FreeOmegaMixedMeasureInterface
              FreeOmegaObservableSemanticOmegaInterface rat bool fuel
              binary_coin_transition x'
          | inr b => FORet b
          end))
      (@sem_bind Enum Enum_SemanticMeasureInterface _ _
        (binary_coin_transition x)
        (fun next : rat + bool =>
          match next with
          | inl x' => meas_iter_approx fuel binary_coin_transition x'
          | inr b => @sem_ret Enum Enum_SemanticMeasureInterface bool b
          end))).
    eapply FOOObserveSample with
      (front := fun next : rat + bool =>
        match next with
        | inl x' => meas_iter_approx fuel binary_coin_transition x'
        | inr b => @sem_ret Enum Enum_SemanticMeasureInterface bool b
        end).
    intros [x'|b].
    + apply IH.
    + constructor.
Qed.

Lemma operational_rational_limit_observes :
  free_omega_observes (fun b : bool => b)
    operational_rational_limit (rational_bernoulli_measure q0 q1).
Proof.
  unfold operational_rational_limit. eapply FOOObserveLub.
  - intro fuel. exact (operational_rational_approx_observes fuel q).
  - exact (rational_binary_iteration_converges q0 q1).
Qed.

Definition operational_rational_heads : MF rational_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    operational_rational_limit
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) rational_head (FHRet b)).

Definition operational_rational_direct : ptree rational_coinE Enum bool :=
  Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).

Definition operational_rational_direct_heads : MF rational_head :=
  @mixed_bind Enum MF FreeOmegaMixedMeasureInterface bool rational_head
    (rational_bernoulli_measure q0 q1)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface)) rational_head (FHRet b)).

Definition operational_rational_head_value (h : rational_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition operational_rational_direct_observation : Enum bool :=
  @sem_bind Enum Enum_SemanticMeasureInterface _ _
    (rational_bernoulli_measure q0 q1)
    (fun b => @sem_ret Enum Enum_SemanticMeasureInterface bool b).

(** The implementation and specification already differ at finite fuel.
    One unit of primitive fuel exposes exactly one binary-algorithm round on
    the left, whereas it exposes the complete direct sample on the right.
    Their bisimulation below therefore arises only after the left-hand
    omega limit; it is not lockstep equality of two copied schedules. *)
Lemma operational_rational_coin_hitting_one :
  operational_hitting_approx (MF := MF) 1
      (observe (binary_rational_coin q)) =
    operational_rational_head_approx 1.
Proof.
  unfold binary_rational_coin.
  change (free_primitive_iter_hitting
      (E := rational_coinE) binary_coin_transition 1 q =
    operational_rational_head_approx 1).
  rewrite free_primitive_iter_hitting_succ.
  unfold operational_rational_head_approx,
    operational_rational_iter_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind sem_ret free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intros [x|b]; reflexivity.
Qed.

Lemma operational_rational_direct_hitting_one :
  operational_hitting_approx (MF := MF) 1
      (observe operational_rational_direct) =
    operational_rational_direct_heads.
Proof. reflexivity. Qed.

Lemma operational_rational_first_round_mass :
  enum_expect (fun _ : bool => (1 : rat))
    (meas_iter_approx 1 binary_coin_transition q) = 1 / 2.
Proof.
  rewrite /meas_iter_approx /binary_coin_transition.
  case: (q < 1 / 2); rewrite /= !mulr1 !addr0; reflexivity.
Qed.

(** In particular, the first implementation prefix is a strict
    subdistribution, while the direct specification is already total. *)
Lemma operational_rational_first_round_not_direct :
  meas_iter_approx 1 binary_coin_transition q <>
    rational_bernoulli_measure q0 q1.
Proof.
  intro Heq.
  pose proof (rational_bernoulli_total q0 q1) as Htotal.
  change (enum_expect (fun _ : bool => (1 : rat))
    (rational_bernoulli_measure q0 q1) = 1) in Htotal.
  rewrite <- Heq, operational_rational_first_round_mass in Htotal.
  have Hlt : (1 / 2 : rat) < 1.
  { apply ltr_pdivrMr. exact (@ltr0Sn rat 1). }
  rewrite Htotal ltxx in Hlt. discriminate Hlt.
Qed.

Lemma operational_rational_heads_observes :
  free_omega_observes operational_rational_head_value
    operational_rational_heads (rational_bernoulli_measure q0 q1).
Proof.
  unfold operational_rational_heads.
  eapply free_omega_observes_bind_ret
    with (obsA := fun b : bool => b).
  - exact operational_rational_limit_observes.
  - intros b. reflexivity.
Qed.

Lemma operational_rational_direct_heads_observes :
  free_omega_observes operational_rational_head_value
    operational_rational_direct_heads
    operational_rational_direct_observation.
Proof.
  unfold operational_rational_direct_heads,
    operational_rational_direct_observation.
  eapply FOOObserveSample. intro b. constructor.
Qed.

Lemma operational_rational_direct_observation_eq :
  operational_rational_direct_observation =
    rational_bernoulli_measure q0 q1.
Proof.
  unfold operational_rational_direct_observation.
  change (bind_Enum (rational_bernoulli_measure q0 q1)
    (fun b => ret_Enum b) = rational_bernoulli_measure q0 q1).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma operational_rational_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _ operational_rational_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_rational_head_value,
    (rational_bernoulli_measure q0 q1).
  split; [exact operational_rational_heads_observes|].
  exact (rational_bernoulli_total q0 q1).
Qed.

Lemma operational_rational_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface _
    operational_rational_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_rational_head_value,
    operational_rational_direct_observation.
  split; [exact operational_rational_direct_heads_observes|].
  rewrite operational_rational_direct_observation_eq.
  exact (rational_bernoulli_total q0 q1).
Qed.

Theorem operational_rational_coin_ast :
  @operational_ast_weak rational_coinE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe (binary_rational_coin q)) operational_rational_heads.
Proof.
  unfold binary_rational_coin, operational_rational_heads.
  eapply operational_ast_weak_iter.
  - exact operational_rational_increasing.
  - change (@operational_iter_cofinal rational_coinE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface rat bool
      (free_primitive_iter_step binary_coin_transition)
      binary_coin_transition q).
    apply free_primitive_iter_cofinal.
  - exact operational_rational_mixed_iter.
  - exact operational_rational_heads_total.
Qed.

Corollary operational_rational_coin_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' rational_coinE Enum bool) rational_head
    (@ptree_primitive_kernel rational_coinE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface bool)
    (observe (binary_rational_coin q)) operational_rational_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe (binary_rational_coin q)) operational_rational_heads)).
  exact operational_rational_coin_ast.
Qed.

Theorem operational_rational_direct_ast :
  @operational_ast_weak rational_coinE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool
    (observe operational_rational_direct)
    operational_rational_direct_heads.
Proof.
  assert (Hobserve : observe operational_rational_direct =
    ProbF (rational_bernoulli_measure q0 q1)
      (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply operational_ast_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply operational_weak_ret.
    + apply free_omega_observable_total_intro.
      exists bool, operational_rational_head_value,
        (@sem_ret Enum Enum_SemanticMeasureInterface bool b).
      split; [constructor|].
      change (enum_expect (fun _ : bool => (1 : rat)) (ret_Enum b) =
        (1 : rat)).
      rewrite enum_expect_ret. reflexivity.
  - exact operational_rational_direct_heads_total.
Qed.

Corollary operational_rational_direct_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' rational_coinE Enum bool) rational_head
    (@ptree_primitive_kernel rational_coinE Enum MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := Enum_SemanticMeasureInterface)
        (NO := Enum_SemanticOmegaInterface))
      FreeOmegaMixedMeasureInterface bool)
    (observe operational_rational_direct) operational_rational_direct_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe operational_rational_direct)
    operational_rational_direct_heads)).
  exact operational_rational_direct_ast.
Qed.

Lemma operational_rational_heads_lift
    (Hsupport : free_omega_support_lift eq operational_rational_limit
      (FOSample (rational_bernoulli_measure q0 q1)
        (fun b => FORet b)))
    (sim : ptree rational_coinE Enum bool ->
      ptree rational_coinE Enum bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface)) _ _
    (frontier_head_rel eq sim)
    operational_rational_heads operational_rational_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := operational_rational_head_value)
    (obsB := operational_rational_head_value)
    (outA := rational_bernoulli_measure q0 q1)
    (outB := operational_rational_direct_observation)
    (S := eq).
  - exact operational_rational_heads_observes.
  - exact operational_rational_direct_heads_observes.
  - rewrite operational_rational_direct_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold operational_rational_heads, operational_rational_direct_heads.
    change (free_omega_support_lift (frontier_head_rel eq sim)
      (free_omega_bind operational_rational_limit
        (fun b => FORet (FHRet b)))
      (free_omega_bind
        (FOSample (rational_bernoulli_measure q0 q1)
          (fun b => FORet b))
        (fun b => FORet (FHRet b)))).
    eapply free_omega_support_lift_bind with (T := eq).
    + exact Hsupport.
    + intros b1 b2 ->. split.
      * intros P HP. dependent destruction HP. apply FOAERet.
        exists (FHRet b2). split; [constructor; reflexivity|assumption].
      * intros P HP. dependent destruction HP. apply FOAERet.
        exists (FHRet b2). split; [constructor; reflexivity|assumption].
Qed.

Theorem probabilistic_eutt_binary_rational_coin_direct :
  free_omega_support_lift eq operational_rational_limit
    (FOSample (rational_bernoulli_measure q0 q1) (fun b => FORet b)) ->
  @probabilistic_eutt rational_coinE Enum MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := Enum_SemanticMeasureInterface)
      (NO := Enum_SemanticOmegaInterface))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface bool bool eq
    (binary_rational_coin q) operational_rational_direct.
Proof.
  intro Hsupport. eapply probabilistic_eutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_rational_coin_ast).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_rational_direct_ast).
  - exact (operational_rational_heads_lift Hsupport _).
Qed.

End OperationalRationalCoin.
