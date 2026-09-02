Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.

Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum reals.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import MathCompMeasure FreeOmegaMeasure
  TwoLevelMeasure TwoLevelMeasureMathComp.
From PTree.Eq Require Import PrimitiveStableHitting OperationalProbabilisticPTS
  OperationalProbabilisticPTSFreeOmega UnifiedFrontier ProbabilisticEutt.
From PTree.Examples Require Import RealBernoulliOracle RealBernoulliMathComp
  UnifiedRealBernoulliMathCompCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section OperationalRealOracle.
Context (R : realType).
Context `{MathCompCouplingGluing R}.
Context `{MathCompOracleSupportLaws R}.

Local Notation MN := (MathCompKernelMeasure R).
Local Notation MF := (MathCompBehaviorMeasure R).
Local Notation Head :=
  (frontier_head real_mathcomp_coinE MN bool).

Variable qbit : binary_oracle.
Variable q : R.
Hypothesis q01 : (0 <= q <= 1)%R.
Hypothesis Hrep : mathcomp_oracle_represents qbit q.

Lemma operational_mathcomp_oracle_increasing :
  @sem_increasing MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) bool
    (fun fuel => unified_mathcomp_oracle_approx R Head qbit fuel 0).
Proof.
  intro fuel. unfold unified_mathcomp_oracle_approx.
  generalize (0 : nat). induction fuel as [|fuel IH]; intro n.
  - cbn [mixed_iter_approx]. constructor.
  - cbn [mixed_iter_approx].
    eapply FOApproxSample with (S := @eq (nat + bool)).
    + apply mathcomp_kernel_lift_refl. intros next. reflexivity.
    + intros next next' ->. destruct next' as [n'|b].
      * apply IH.
      * apply free_omega_approx_refl. intros y. reflexivity.
Qed.

Lemma operational_mathcomp_oracle_out_observes :
  @free_omega_observes MN
    (MathCompNodeSemanticMeasureInterface R)
    (MathCompNodeSemanticOmegaInterface R)
    bool bool id (unified_mathcomp_oracle_out R Head qbit)
    (mathcomp_bernoulli q).
Proof.
  apply FOOObserveLub with
    (outs := fun fuel => mathcomp_oracle_result_approx R qbit fuel 0).
  - intro fuel. exact: unified_mathcomp_oracle_approx_observes.
  - exact: mathcomp_binary_oracle_lub q01 Hrep.
Qed.

Definition operational_mathcomp_oracle_heads : MF Head :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R)) _ _
    (unified_mathcomp_oracle_out R Head qbit)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := MathCompNodeSemanticMeasureInterface R)) Head (FHRet b)).

Definition operational_mathcomp_direct_heads : MF Head :=
  @mixed_bind MN MF FreeOmegaMixedMeasureInterface bool Head
    (mathcomp_bernoulli q)
    (fun b => @sem_ret MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := MathCompNodeSemanticMeasureInterface R)) Head (FHRet b)).

Definition operational_mathcomp_direct_observation : MN bool :=
  sem_bind (mathcomp_bernoulli q) (fun b => sem_ret b).

Definition operational_mathcomp_head_value (h : Head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Lemma operational_mathcomp_oracle_heads_observes :
  free_omega_observes operational_mathcomp_head_value
    operational_mathcomp_oracle_heads (mathcomp_bernoulli q).
Proof.
  unfold operational_mathcomp_oracle_heads.
  eapply free_omega_observes_bind_ret with (obsA := id).
  - exact operational_mathcomp_oracle_out_observes.
  - intros b. reflexivity.
Qed.

Lemma operational_mathcomp_direct_heads_observes :
  free_omega_observes operational_mathcomp_head_value
    operational_mathcomp_direct_heads
    operational_mathcomp_direct_observation.
Proof.
  unfold operational_mathcomp_direct_heads,
    operational_mathcomp_direct_observation.
  eapply FOOObserveSample. intro b. constructor.
Qed.

Lemma operational_mathcomp_oracle_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) _
    operational_mathcomp_oracle_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_mathcomp_head_value, (mathcomp_bernoulli q).
  split; [exact operational_mathcomp_oracle_heads_observes|].
  exact: mathcomp_bernoulli_total.
Qed.

Lemma operational_mathcomp_direct_heads_total :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) _
    operational_mathcomp_direct_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, operational_mathcomp_head_value,
    operational_mathcomp_direct_observation.
  split; [exact operational_mathcomp_direct_heads_observes|].
  unfold operational_mathcomp_direct_observation.
  assert (Heq : mathcomp_kernel_eq (mathcomp_bernoulli q)
      (sem_bind (mathcomp_bernoulli q) (fun b => sem_ret b))).
  { apply mathcomp_kernel_eq_sym. exact: mathcomp_kernel_bind_ret_r. }
  apply (proj1 (mathcomp_kernel_total_proper Heq)).
  exact: mathcomp_bernoulli_total.
Qed.

Theorem operational_mathcomp_oracle_ast :
  @operational_ast_weak real_mathcomp_coinE MN MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) bool
    (observe (mathcomp_binary_oracle_coin R qbit))
    operational_mathcomp_oracle_heads.
Proof.
  unfold mathcomp_binary_oracle_coin,
    operational_mathcomp_oracle_heads.
  eapply operational_ast_weak_iter.
  - exact operational_mathcomp_oracle_increasing.
  - change (@operational_iter_cofinal real_mathcomp_coinE MN MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := MathCompNodeSemanticMeasureInterface R))
      FreeOmegaMixedMeasureInterface
      (FreeOmegaObservableSemanticOmegaInterface
        (NI := MathCompNodeSemanticMeasureInterface R)
        (NO := MathCompNodeSemanticOmegaInterface R)) nat bool
      (free_primitive_iter_step
        (mathcomp_oracle_transition R qbit))
      (mathcomp_oracle_transition R qbit) 0).
    apply free_primitive_iter_cofinal.
  - exact: unified_mathcomp_oracle_mixed_iter.
  - exact operational_mathcomp_oracle_heads_total.
Qed.

Corollary operational_mathcomp_oracle_primitive_ast :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    (ptree' real_mathcomp_coinE MN bool) Head
    (@ptree_primitive_kernel real_mathcomp_coinE MN MF
      (FreeOmegaObservableSemanticMeasureInterface
        (NI := MathCompNodeSemanticMeasureInterface R))
      FreeOmegaMixedMeasureInterface bool)
    (observe (mathcomp_binary_oracle_coin R qbit))
    operational_mathcomp_oracle_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe (mathcomp_binary_oracle_coin R qbit))
    operational_mathcomp_oracle_heads)).
  exact operational_mathcomp_oracle_ast.
Qed.

Theorem operational_mathcomp_direct_ast :
  @operational_ast_weak real_mathcomp_coinE MN MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) bool
    (observe (mathcomp_direct_bernoulli (R := R) q))
    operational_mathcomp_direct_heads.
Proof.
  split.
  - assert (Hobserve : observe (mathcomp_direct_bernoulli (R := R) q) =
      ProbF (mathcomp_bernoulli q) (fun b => Ret b)) by reflexivity.
    rewrite Hobserve. unfold operational_mathcomp_direct_heads.
    eapply operational_weak_prob with (Good := fun _ => True).
    + exact: mathcomp_kernel_ae_true.
    + intros b _. apply operational_weak_ret.
  - exact operational_mathcomp_direct_heads_total.
Qed.

Lemma operational_mathcomp_oracle_heads_lift
    (sim : ptree real_mathcomp_coinE MN bool ->
      ptree real_mathcomp_coinE MN bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R)) _ _
    (frontier_head_rel eq sim)
    operational_mathcomp_oracle_heads operational_mathcomp_direct_heads.
Proof.
  eapply FOQLObserve with
    (obsA := operational_mathcomp_head_value)
    (obsB := operational_mathcomp_head_value)
    (outA := mathcomp_bernoulli q)
    (outB := operational_mathcomp_direct_observation)
    (S := eq).
  - exact operational_mathcomp_oracle_heads_observes.
  - exact operational_mathcomp_direct_heads_observes.
  - unfold operational_mathcomp_direct_observation.
    eapply sem_lift_proper_r.
    + apply mathcomp_kernel_eq_sym.
      exact: mathcomp_kernel_bind_ret_r.
    + apply mathcomp_kernel_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - unfold operational_mathcomp_oracle_heads,
      operational_mathcomp_direct_heads.
    change (free_omega_support_lift (frontier_head_rel eq sim)
      (free_omega_bind (unified_mathcomp_oracle_out R Head qbit)
        (fun b => FORet (FHRet b)))
      (free_omega_bind
        (FOSample (mathcomp_bernoulli q) (fun b => FORet b))
        (fun b => FORet (FHRet b)))).
    eapply free_omega_support_lift_bind with (T := eq).
    + exact (mathcomp_oracle_support Head
        (qbit := qbit) (q := q) q01 Hrep).
    + intros b1 b2 ->. split.
      * intros P HP. dependent destruction HP. apply FOAERet.
        exists (FHRet b2). split; [apply FHRRet; reflexivity|assumption].
      * intros P HP. dependent destruction HP. apply FOAERet.
        exists (FHRet b2). split; [apply FHRRet; reflexivity|assumption].
Qed.

Theorem probabilistic_eutt_mathcomp_binary_oracle_direct :
  @probabilistic_eutt real_mathcomp_coinE MN MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticMeasureCoreLaws
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R)) bool bool eq
    (mathcomp_binary_oracle_coin R qbit)
    (mathcomp_direct_bernoulli (R := R) q).
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_mathcomp_oracle_ast).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 operational_mathcomp_direct_ast).
  - exact (operational_mathcomp_oracle_heads_lift _).
Qed.

End OperationalRealOracle.
