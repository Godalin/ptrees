Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssralg ssrnum reals.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import MathCompMeasure FreeOmegaMeasure
  TwoLevelMeasure TwoLevelMeasureMathComp.
From PTree.Eq Require Import UnifiedFrontier ProbabilisticEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section DirectMathCompCoin.
Context (R : realType) (q : R).

Variant mc_freeE : Type -> Type := .

Definition unified_mathcomp_direct_coin :
    ptree mc_freeE (MathCompKernelMeasure R) bool :=
  Prob (mathcomp_bernoulli q) (fun b => Ret b).

Definition unified_mathcomp_coin_heads :
    MathCompBehaviorMeasure R
      (frontier_head mc_freeE (MathCompKernelMeasure R) bool) :=
  mixed_bind (mathcomp_bernoulli q) (fun b => sem_ret (FHRet b)).

(** This theorem is the positive universe regression missing from the old HB
    backend: a genuine MathComp probability node now produces a behavior
    measure whose carrier contains recursive PTree continuations. *)
Lemma unified_mathcomp_direct_coin_frontier :
  @frontier mc_freeE (MathCompKernelMeasure R) (MathCompBehaviorMeasure R)
    (MathCompNodeSemanticMeasure R)
    (FreeOmegaObservableSemanticMeasure
      (NI := MathCompNodeSemanticMeasure R))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := MathCompNodeSemanticMeasure R))
    bool (observe unified_mathcomp_direct_coin)
    unified_mathcomp_coin_heads.
Proof.
  unfold unified_mathcomp_direct_coin, unified_mathcomp_coin_heads.
  cbn.
  rewrite -free_omega_mixed_bindE.
  apply (@UFProb mc_freeE (MathCompKernelMeasure R)
    (MathCompBehaviorMeasure R)
    (MathCompNodeSemanticMeasure R)
    (FreeOmegaObservableSemanticMeasure
      (NI := MathCompNodeSemanticMeasure R))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := MathCompNodeSemanticMeasure R))
    bool bool (mathcomp_bernoulli q) (fun b => Ret b)
    (fun b => FORet (FHRet b)) (fun _ => True)).
  - exact: mathcomp_kernel_ae_true.
  - intros b _. rewrite -free_omega_observable_sem_retE. apply UFRet.
Qed.

Lemma unified_mathcomp_direct_coin_probabilistic_eutt_reflexive
    `{MathCompCouplingGluing R} :
  @probabilistic_eutt mc_freeE (MathCompKernelMeasure R)
    (MathCompBehaviorMeasure R)
    (FreeOmegaObservableSemanticMeasure
      (NI := MathCompNodeSemanticMeasure R))
    (FreeOmegaObservableSemanticMeasureCoreLaws
      (NI := MathCompNodeSemanticMeasure R))
    FreeOmegaMixedMeasure
    (FreeOmegaObservableSemanticOmega
      (NI := MathCompNodeSemanticMeasure R))
    bool bool eq unified_mathcomp_direct_coin unified_mathcomp_direct_coin.
Proof. apply probabilistic_eutt_refl. Qed.

End DirectMathCompCoin.
