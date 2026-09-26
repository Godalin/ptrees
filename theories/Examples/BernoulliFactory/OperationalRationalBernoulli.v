(** Case role: shared analysis.
    Proof mode: analysis-dominated.
    Reading entry: peutt_binary_rational_coin_direct.
    Scope: EnumQ / FreeOmega; semantic endpoint consumed by program algebra.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import FunctionalExtensionality.
From PTree.Prob.Backend.Common Require Import FiniteRecordExtensionality.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Map.
From PTree.Eq Require Import Shallow PrimitiveStableHitting PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Eq Require Import UnifiedFrontier PEutt.
From PTree.Examples.BernoulliFactory Require Import RationalBernoulli.

Set Implicit Arguments.
#[local] Existing Instance FreeOmegaSemanticMeasure.
#[local] Existing Instance FreeOmegaSemanticOmega.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ PTree.Prob.Backend.EnumQ.Map.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Local Notation MF := (FreeOmega EnumQ).
Local Notation rational_head :=
  (stable_head rational_coinE EnumQ bool).

Section OperationalRationalCoin.
Variable q : rat.
Hypothesis q0 : 0 <= q.
Hypothesis q1 : q <= 1.

Definition ptree_rational_iter_approx (fuel : nat) : MF bool :=
  @mixed_iter_approx EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega rat bool fuel
    binary_coin_transition q.

Definition ptree_rational_head_approx (fuel : nat) : MF rational_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    (ptree_rational_iter_approx fuel)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega)) rational_head (FHRet b)).

Definition ptree_rational_limit : MF bool :=
  FOLub ptree_rational_iter_approx.

Lemma ptree_rational_increasing :
  @sem_increasing MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega bool
    ptree_rational_iter_approx.
Proof.
  intro fuel. unfold ptree_rational_iter_approx.
  clear q0 q1. revert q. induction fuel as [|fuel IH]; intro x.
  - cbn [mixed_iter_approx]. constructor.
  - cbn [mixed_iter_approx].
    eapply FOApproxSample with (S := @eq (rat + bool)).
    + apply sem_lift_refl. intros next. reflexivity.
    + intros next next' ->. destruct next' as [x'|b].
      * apply IH.
      * apply free_omega_approx_refl. intros y. reflexivity.
Qed.

Lemma ptree_rational_mixed_iter :
  @mixed_iter EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega rat bool
    binary_coin_transition q ptree_rational_limit.
Proof.
  unfold mixed_iter, ptree_rational_limit,
    ptree_rational_iter_approx.
  apply free_omega_qlift_refl. intros b. reflexivity.
Qed.

Lemma ptree_rational_approx_observes fuel : forall x,
  free_omega_observes (fun b : bool => b)
    (@mixed_iter_approx EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega rat bool fuel
      binary_coin_transition x)
    (meas_iter_approx fuel binary_coin_transition x).
Proof.
  induction fuel as [|fuel IH]; intro x.
  - constructor.
  - cbn [mixed_iter_approx meas_iter_approx mixed_bind
      FreeOmegaMixedMeasure sem_bind
      EnumQ_SemanticMeasure].
    change (free_omega_observes (fun b : bool => b)
      (FOSample (binary_coin_transition x)
        (fun next : rat + bool =>
          match next with
          | inl x' => @mixed_iter_approx EnumQ MF
              (FreeOmegaObservableSemanticMeasure
                (NI := EnumQ_SemanticMeasure)
                (NO := EnumQ_SemanticOmega))
              FreeOmegaMixedMeasure
              FreeOmegaObservableSemanticOmega rat bool fuel
              binary_coin_transition x'
          | inr b => FORet b
          end))
      (@sem_bind EnumQ EnumQ_SemanticMeasure _ _
        (binary_coin_transition x)
        (fun next : rat + bool =>
          match next with
          | inl x' => meas_iter_approx fuel binary_coin_transition x'
          | inr b => @sem_ret EnumQ EnumQ_SemanticMeasure bool b
          end))).
    eapply FOOObserveSample with
      (front := fun next : rat + bool =>
        match next with
        | inl x' => meas_iter_approx fuel binary_coin_transition x'
        | inr b => @sem_ret EnumQ EnumQ_SemanticMeasure bool b
        end).
    intros [x'|b].
    + apply IH.
    + constructor.
Qed.

Lemma ptree_rational_limit_observes :
  free_omega_observes (fun b : bool => b)
    ptree_rational_limit (rational_bernoulli_measure q0 q1).
Proof.
  unfold ptree_rational_limit. eapply FOOObserveLub.
  - intro fuel. exact (ptree_rational_approx_observes fuel q).
  - exact (rational_binary_iteration_converges q0 q1).
  - apply ptree_rational_increasing.
Qed.

Definition ptree_rational_heads : MF rational_head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    ptree_rational_limit
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega)) rational_head (FHRet b)).

Definition ptree_rational_direct : ptree rational_coinE EnumQ bool :=
  Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).

Definition ptree_rational_direct_heads : MF rational_head :=
  @mixed_bind EnumQ MF FreeOmegaMixedMeasure bool rational_head
    (rational_bernoulli_measure q0 q1)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega)) rational_head (FHRet b)).

Definition ptree_rational_head_value (h : rational_head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Definition ptree_rational_direct_observation : EnumQ bool :=
  @sem_bind EnumQ EnumQ_SemanticMeasure _ _
    (rational_bernoulli_measure q0 q1)
    (fun b => @sem_ret EnumQ EnumQ_SemanticMeasure bool b).

(** The implementation and specification already differ at finite fuel.
    One unit of primitive fuel exposes exactly one binary-algorithm round on
    the left, whereas it exposes the complete direct sample on the right.
    Their bisimulation below therefore arises only after the left-hand
    omega limit; it is not lockstep equality of two copied schedules. *)
Lemma ptree_rational_coin_hitting_one :
  ptree_hitting_approx (MF := MF) 1
      (observe (binary_rational_coin q)) =
    ptree_rational_head_approx 1.
Proof.
  unfold binary_rational_coin.
  change (primitive_iter_hitting
      (E := rational_coinE) binary_coin_transition 1 q =
    ptree_rational_head_approx 1).
  rewrite primitive_iter_hitting_succ.
  unfold ptree_rational_head_approx,
    ptree_rational_iter_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind sem_ret free_omega_bind
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality. intros [x|b]; reflexivity.
Qed.

Lemma ptree_rational_direct_hitting_one :
  ptree_hitting_approx (MF := MF) 1
      (observe ptree_rational_direct) =
    ptree_rational_direct_heads.
Proof. reflexivity. Qed.

Lemma ptree_rational_first_round_mass :
  enumQ_expect (fun _ : bool => (1 : rat))
    (meas_iter_approx 1 binary_coin_transition q) = 1 / 2.
Proof.
  rewrite /meas_iter_approx /binary_coin_transition.
  case: (q < 1 / 2); rewrite enumQ_expect_bind enumQ_expect_unif2 /one_div_two /= enumQ_expect_ret.
  - change ((1/2 : rat)*0+((1/2)*1+0)=1/2); by rewrite mulr0 mulr1 addr0 add0r.
  - change ((1/2 : rat)*1+((1/2)*0+0)=1/2); by rewrite mulr0 mulr1 !addr0.
Qed.

(** In particular, the first implementation prefix is a strict
    subdistribution, while the direct specification is already total. *)
Lemma ptree_rational_first_round_not_direct :
  meas_iter_approx 1 binary_coin_transition q <>
    rational_bernoulli_measure q0 q1.
Proof.
  intro Heq.
  pose proof (rational_bernoulli_total q0 q1) as Htotal.
  change (enumQ_expect (fun _ : bool => (1 : rat))
    (rational_bernoulli_measure q0 q1) = 1) in Htotal.
  rewrite <- Heq, ptree_rational_first_round_mass in Htotal.
  have Hlt : (1 / 2 : rat) < 1.
  { apply ltr_pdivrMr. exact (@ltr0Sn rat 1). }
  rewrite Htotal ltxx in Hlt. discriminate Hlt.
Qed.

Lemma ptree_rational_heads_observes :
  free_omega_observes ptree_rational_head_value
    ptree_rational_heads (rational_bernoulli_measure q0 q1).
Proof.
  unfold ptree_rational_heads.
  eapply free_omega_observes_bind_ret
    with (obsA := fun b : bool => b).
  - exact ptree_rational_limit_observes.
  - intros b. reflexivity.
Qed.

Lemma ptree_rational_direct_heads_observes :
  free_omega_observes ptree_rational_head_value
    ptree_rational_direct_heads
    ptree_rational_direct_observation.
Proof.
  unfold ptree_rational_direct_heads,
    ptree_rational_direct_observation.
  eapply FOOObserveSample. intro b. constructor.
Qed.

Lemma ptree_rational_direct_observation_eq :
  ptree_rational_direct_observation =
    rational_bernoulli_measure q0 q1.
Proof.
  unfold ptree_rational_direct_observation.
  apply finite_enum_raw_eq.
  change (enumQ_raw (bind_EnumQ (rational_bernoulli_measure q0 q1)
    (fun b => ret_EnumQ b)) = enumQ_raw (rational_bernoulli_measure q0 q1)).
  rewrite bind_ret_emap. apply emap_id.
Qed.

Lemma ptree_rational_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega _ ptree_rational_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_rational_head_value,
    (rational_bernoulli_measure q0 q1).
  split; [exact ptree_rational_heads_observes|].
  exact (rational_bernoulli_total q0 q1).
Qed.

Lemma ptree_rational_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega _
    ptree_rational_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_rational_head_value,
    ptree_rational_direct_observation.
  split; [exact ptree_rational_direct_heads_observes|].
  rewrite ptree_rational_direct_observation_eq.
  exact (rational_bernoulli_total q0 q1).
Qed.

Theorem ptree_rational_coin_ast :
  @ptree_stable_hitting_ast rational_coinE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (binary_rational_coin q)) ptree_rational_heads.
Proof.
  unfold binary_rational_coin, ptree_rational_heads.
  eapply ptree_stable_hitting_ast_iter.
  - exact ptree_rational_increasing.
  - change (@PTreeKernel.ptree_iter_cofinal rational_coinE EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega rat bool
      (primitive_iter_step binary_coin_transition)
      binary_coin_transition q).
    apply primitive_iter_cofinal.
  - exact ptree_rational_mixed_iter.
  - exact ptree_rational_heads_total.
Qed.

Corollary ptree_rational_coin_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega
    (ptree' rational_coinE EnumQ bool) rational_head
    (@ptree_primitive_kernel rational_coinE EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure bool)
    (observe (binary_rational_coin q)) ptree_rational_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe (binary_rational_coin q)) ptree_rational_heads)).
  exact ptree_rational_coin_ast.
Qed.

Theorem ptree_rational_direct_ast :
  @ptree_stable_hitting_ast rational_coinE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe ptree_rational_direct)
    ptree_rational_direct_heads.
Proof.
  assert (Hobserve : observe ptree_rational_direct =
    ProbF (rational_bernoulli_measure q0 q1)
      (fun b => Ret b)) by reflexivity.
  rewrite Hobserve.
  eapply ptree_stable_hitting_ast_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + apply ptree_stable_hitting_ret.
    + apply free_omega_observable_total_intro.
      exists bool, ptree_rational_head_value,
        (@sem_ret EnumQ EnumQ_SemanticMeasure bool b).
      split; [constructor|].
      change (enumQ_expect (fun _ : bool => (1 : rat)) (ret_EnumQ b) =
        (1 : rat)).
      rewrite enumQ_expect_ret. reflexivity.
  - exact ptree_rational_direct_heads_total.
Qed.

Corollary ptree_rational_direct_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega
    (ptree' rational_coinE EnumQ bool) rational_head
    (@ptree_primitive_kernel rational_coinE EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure bool)
    (observe ptree_rational_direct) ptree_rational_direct_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe ptree_rational_direct)
    ptree_rational_direct_heads)).
  exact ptree_rational_direct_ast.
Qed.

Lemma ptree_rational_heads_lift
    (Hsupport : free_omega_support_lift eq ptree_rational_limit
      (FOSample (rational_bernoulli_measure q0 q1)
        (fun b => FORet b)))
    (sim : ptree rational_coinE EnumQ bool ->
      ptree rational_coinE EnumQ bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    (stable_head_rel eq sim)
    ptree_rational_heads ptree_rational_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := ptree_rational_head_value)
    (obsB := ptree_rational_head_value)
    (outA := rational_bernoulli_measure q0 q1)
    (outB := ptree_rational_direct_observation)
    (S := eq).
  - exact ptree_rational_heads_observes.
  - exact ptree_rational_direct_heads_observes.
  - rewrite ptree_rational_direct_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold ptree_rational_heads, ptree_rational_direct_heads.
    change (free_omega_support_lift (stable_head_rel eq sim)
      (free_omega_bind ptree_rational_limit
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

Theorem peutt_binary_rational_coin_direct :
  free_omega_support_lift eq ptree_rational_limit
    (FOSample (rational_bernoulli_measure q0 q1) (fun b => FORet b)) ->
  @peutt rational_coinE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    (binary_rational_coin q) ptree_rational_direct.
Proof.
  intro Hsupport. eapply peutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact (proj1 ptree_rational_coin_ast).
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact (proj1 ptree_rational_direct_ast).
  - exact (ptree_rational_heads_lift Hsupport _).
Qed.

End OperationalRationalCoin.
