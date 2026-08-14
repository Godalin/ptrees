Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum reals.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import MathCompMeasure FreeOmegaMeasure
  TwoLevelMeasure TwoLevelMeasureMathComp.
From PTree.Eq Require Import UnifiedFrontier UnifiedPWeak
  UnifiedProbabilisticPTS.
From PTree.Examples Require Import RealBernoulliOracle RealBernoulliMathComp
  UnifiedMathCompFrontier UnifiedRealBernoulliMathCompCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section UnifiedRealOracle.
Context (R : realType).

Local Notation MN := (MathCompKernelMeasure R).
Local Notation MF := (MathCompBehaviorMeasure R).
Local Notation Head :=
  (frontier_head real_mathcomp_coinE MN bool).

Definition real_mathcomp_head_value (h : Head) : bool :=
  match h with
  | FHRet b => b
  | @FHVis _ _ _ X e _ => match e with end
  end.

Lemma unified_mathcomp_oracle_out_observes (qbit : binary_oracle) (q : R)
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents qbit q ->
  @free_omega_observes MN
    (MathCompNodeSemanticMeasureInterface R)
    (MathCompNodeSemanticOmegaInterface R)
    bool bool id (unified_mathcomp_oracle_out R Head qbit)
    (mathcomp_bernoulli q).
Proof.
  intro Hrep. apply FOOObserveLub with
    (outs := fun fuel => mathcomp_oracle_result_approx R qbit fuel 0).
  - intro fuel. exact: unified_mathcomp_oracle_approx_observes.
  - exact: mathcomp_binary_oracle_lub q01 Hrep.
Qed.

Lemma unified_mathcomp_oracle_total (qbit : binary_oracle) (q : R)
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents qbit q ->
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    bool (unified_mathcomp_oracle_out R Head qbit).
Proof.
  intro Hrep. exists bool, id, (mathcomp_bernoulli q). split.
  - exact: unified_mathcomp_oracle_out_observes.
  - exact: mathcomp_bernoulli_total.
Qed.

Definition unified_mathcomp_binary_oracle_frontier
    (qbit : binary_oracle) (q : R)
    (q01 : (0 <= q <= 1)%R)
    (Hrep : mathcomp_oracle_represents qbit q) :=
  @frontier_iter_intro real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    bool nat (mathcomp_oracle_step R qbit)
    (mathcomp_oracle_transition R qbit) 0
    (unified_mathcomp_oracle_out R Head qbit)
    (unified_mathcomp_oracle_step_frontier R qbit)
    (unified_mathcomp_oracle_mixed_iter R Head qbit)
    (unified_mathcomp_oracle_total q01 Hrep).

Definition unified_mathcomp_real_direct_heads (q : R) : MF Head :=
  FOSample (mathcomp_bernoulli q) (fun b => FORet (FHRet b)).

Lemma unified_mathcomp_real_direct_frontier (q : R) :
  @frontier real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    bool (observe (mathcomp_direct_bernoulli (R := R) q))
    (unified_mathcomp_real_direct_heads q).
Proof.
  unfold mathcomp_direct_bernoulli, unified_mathcomp_real_direct_heads.
  cbn. rewrite -free_omega_mixed_bindE.
  eapply UFProb with (Good := fun _ => True).
  - exact: mathcomp_kernel_ae_true.
  - intros b _. rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.

Lemma unified_mathcomp_oracle_heads_lift
    `{MathCompCouplingGluing R}
    (qbit : binary_oracle) (q : R) (q01 : (0 <= q <= 1)%R)
    (Hrep : mathcomp_oracle_represents qbit q)
    (sim : ptree real_mathcomp_coinE MN bool ->
      ptree real_mathcomp_coinE MN bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    Head Head (frontier_head_rel eq sim)
    (free_omega_bind (unified_mathcomp_oracle_out R Head qbit)
      (fun b => FORet (FHRet b)))
    (unified_mathcomp_real_direct_heads q).
Proof.
  eapply FOQLObserve with
    (obsA := real_mathcomp_head_value)
    (obsB := real_mathcomp_head_value)
    (outA := mathcomp_bernoulli q)
    (outB := sem_bind (mathcomp_bernoulli q) (fun b => sem_ret b))
    (S := eq).
  - eapply free_omega_observes_bind_ret.
    + exact (unified_mathcomp_oracle_out_observes q01 Hrep).
    + intros b. reflexivity.
  - unfold unified_mathcomp_real_direct_heads.
    apply FOOObserveSample with (front := fun b => sem_ret b).
    intros b. constructor.
  - eapply sem_lift_proper_r.
    + apply mathcomp_kernel_eq_sym.
      exact (mathcomp_kernel_bind_ret_r (mathcomp_bernoulli q)).
    + apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hh.
    destruct h1 as [b1|X1 e1 k1]; [|destruct e1].
    destruct h2 as [b2|X2 e2 k2]; [|destruct e2].
    constructor. exact Hh.
Qed.

Theorem unified_mathcomp_binary_oracle_weak_bisim_direct
    `{MathCompCouplingGluing R}
    (qbit : binary_oracle) (q : R) (q01 : (0 <= q <= 1)%R)
    (Hrep : mathcomp_oracle_represents qbit q) :
  @weak_bisim real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (@MathCompNodeSemanticMeasureCoreLaws R H)
    (FreeOmegaObservableSemanticMeasureCoreLaws
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    bool bool eq (@mathcomp_binary_oracle_coin R qbit)
    (mathcomp_direct_bernoulli (R := R) q).
Proof.
  apply weak_bisim_fold.
  eapply UWBFrontier.
  - exact (unified_mathcomp_binary_oracle_frontier q01 Hrep).
  - exact (unified_mathcomp_real_direct_frontier q).
  - exact (unified_mathcomp_oracle_heads_lift q01 Hrep _).
Qed.

Corollary unified_mathcomp_binary_oracle_ppts_bisim_direct
    `{MathCompCouplingGluing R}
    (qbit : binary_oracle) (q : R) (q01 : (0 <= q <= 1)%R)
    (Hrep : mathcomp_oracle_represents qbit q) :
  @unified_ppts_bisim real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaObservableSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (@MathCompNodeSemanticMeasureCoreLaws R H)
    (FreeOmegaObservableSemanticMeasureCoreLaws
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaObservableSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    bool bool eq (@mathcomp_binary_oracle_coin R qbit)
    (mathcomp_direct_bernoulli (R := R) q).
Proof.
  apply weak_bisim_to_unified_ppts_bisim.
  exact (unified_mathcomp_binary_oracle_weak_bisim_direct q01 Hrep).
Qed.

End UnifiedRealOracle.
