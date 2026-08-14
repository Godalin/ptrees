Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum reals.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import MathCompMeasure FreeOmegaMeasure
  TwoLevelMeasure TwoLevelMeasureMathComp.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Examples Require Import RealBernoulliOracle RealBernoulliMathComp
  UnifiedRealBernoulliMathCompCore.

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

Lemma unified_mathcomp_oracle_total (qbit : binary_oracle) (q : R)
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents qbit q ->
  @sem_total MF
    (FreeOmegaSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    (FreeOmegaSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    bool (unified_mathcomp_oracle_out R Head qbit).
Proof.
  intro Hrep. exists bool, id, (mathcomp_bernoulli q). split.
  - apply FOOObserveLub with
      (outs := fun fuel => mathcomp_oracle_result_approx R qbit fuel 0).
    + intro fuel. exact: unified_mathcomp_oracle_approx_observes.
    + exact: mathcomp_binary_oracle_lub q01 Hrep.
  - exact: mathcomp_bernoulli_total.
Qed.

Definition unified_mathcomp_binary_oracle_frontier
    (qbit : binary_oracle) (q : R)
    (q01 : (0 <= q <= 1)%R)
    (Hrep : mathcomp_oracle_represents qbit q) :=
  @frontier_iter_intro real_mathcomp_coinE MN MF
    (MathCompNodeSemanticMeasureInterface R)
    (FreeOmegaSemanticMeasureInterface
      (NI := MathCompNodeSemanticMeasureInterface R))
    FreeOmegaMixedMeasureInterface
    (FreeOmegaSemanticOmegaInterface
      (NI := MathCompNodeSemanticMeasureInterface R)
      (NO := MathCompNodeSemanticOmegaInterface R))
    bool nat (mathcomp_oracle_step R qbit)
    (mathcomp_oracle_transition R qbit) 0
    (unified_mathcomp_oracle_out R Head qbit)
    (unified_mathcomp_oracle_step_frontier R qbit)
    (unified_mathcomp_oracle_mixed_iter R Head qbit)
    (unified_mathcomp_oracle_total q01 Hrep).

End UnifiedRealOracle.
