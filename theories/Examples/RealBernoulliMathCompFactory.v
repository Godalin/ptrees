Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration MathCompMeasure.
From PTree.Eq Require Import PWeakUnbounded.
From PTree.Examples Require Import RealBernoulliMathComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RealFactoryComposition.
Context (R : realType).
Local Notation M := (MathCompKernelMeasure R).

(** Replace the primitive fair draw used by the binary-oracle algorithm by
    an arbitrary implementation with the same total fair frontier.  A
    von-Neumann extractor for a non-trivial [p]-coin will instantiate
    [implemented_fair]. *)
Variable implemented_fair : ptree real_mathcomp_coinE M bool.

Definition implemented_fair_heads : M (aphead real_mathcomp_coinE M bool) :=
  meas_bind (mathcomp_half_coin R) (fun b => meas_ret (APHRet b)).

Hypothesis implemented_fair_frontier :
  aufrontier (observe implemented_fair) implemented_fair_heads.

Definition implemented_oracle_round (qbit : binary_oracle)
    (n : nat) (random : bool) : nat + bool :=
  if qbit n then
    if random then inl n.+1 else inr true
  else
    if random then inr false else inl n.+1.

Definition implemented_oracle_step (qbit : binary_oracle) (n : nat) :
    ptree real_mathcomp_coinE M (nat + bool) :=
  PTree.bind implemented_fair
    (fun random => Ret (implemented_oracle_round qbit n random)).

Definition implemented_binary_oracle_coin (qbit : binary_oracle) :
    ptree real_mathcomp_coinE M bool :=
  PTree.iter (implemented_oracle_step qbit) 0.

Lemma implemented_round_transition qbit n :
  meas_bind (mathcomp_half_coin R)
      (fun random => meas_ret (implemented_oracle_round qbit n random)) =
  mathcomp_oracle_transition R qbit n.
Proof. reflexivity. Qed.

Lemma implemented_oracle_step_frontier qbit n :
  aufrontier (observe (implemented_oracle_step qbit n))
    (meas_bind (mathcomp_oracle_transition R qbit n)
      (fun next => meas_ret
        (APHRet next : aphead real_mathcomp_coinE M (nat + bool)))).
Proof.
  unfold implemented_oracle_step.
  eapply AUFBind with
    (front := fun random =>
      meas_ret (APHRet (implemented_oracle_round qbit n random))).
  - exact implemented_fair_frontier.
  - move=> random. apply AUFFinite. constructor.
Qed.

Lemma implemented_binary_oracle_frontier qbit q
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents R qbit q ->
  aufrontier (observe (implemented_binary_oracle_coin qbit))
    (meas_bind (@mathcomp_bernoulli R q)
      (fun b => meas_ret
        (APHRet b : aphead real_mathcomp_coinE M bool))).
Proof.
  move=> Hrep. unfold implemented_binary_oracle_coin.
  eapply (AUFNestedIter
    (transition := mathcomp_oracle_transition R qbit)
    (out := @mathcomp_bernoulli R q)).
  - exact: implemented_oracle_step_frontier.
  - exact: mathcomp_binary_oracle_lub R q01 Hrep.
  - exact: mathcomp_bernoulli_total R q01.
Qed.

Theorem implemented_binary_oracle_auweak_direct qbit q
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents R qbit q ->
  auweak eq (implemented_binary_oracle_coin qbit)
    (mathcomp_direct_bernoulli R q).
Proof.
  move=> Hrep. apply auweak_of_common_frontier with
    (hs := meas_bind (@mathcomp_bernoulli R q)
      (fun b => meas_ret
        (APHRet b : aphead real_mathcomp_coinE M bool))).
  - exact: implemented_binary_oracle_frontier q01 Hrep.
  - apply AUFFinite.
    apply (APFProb
      (front := fun b => meas_ret
        (APHRet b : aphead real_mathcomp_coinE M bool))
      (Good := fun _ => True)); first apply meas_ae_true.
    move=> b _. constructor.
Qed.

End RealFactoryComposition.
