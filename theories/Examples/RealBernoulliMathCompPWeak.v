Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.

From PTree.Eq Require Import PWeakUnbounded.
From PTree.Examples Require Import RealBernoulliMathComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RealOraclePWeak.
Context (R : realType).

Local Notation M := (MathCompKernelMeasure R).

Lemma mathcomp_binary_oracle_auweak_direct qbit q
    (q01 : (0 <= q <= 1)%R) :
  mathcomp_oracle_represents R qbit q ->
  @auweak real_mathcomp_coinE M
    (MathCompKernelMeasureInterface R)
    (MathCompKernelMeasureCoreLaws R)
    (MathCompKernelMeasureOmegaInterface R)
    bool bool eq
    (mathcomp_binary_oracle_coin R qbit)
    (mathcomp_direct_bernoulli R q).
Proof.
  move=> Hrep.
  apply auweak_of_common_frontier with
    (hs := meas_bind (@mathcomp_bernoulli R q)
      (fun b => meas_ret (APHRet b))).
  - apply AUFIter with
      (transition := mathcomp_oracle_transition R qbit)
      (out := @mathcomp_bernoulli R q).
    + move=> n. apply (APFProb
        (front := fun next => meas_ret (APHRet next))
        (Good := fun _ => True)); first apply meas_ae_true.
      move=> next _. constructor.
    + exact: mathcomp_binary_oracle_lub R q01 Hrep.
    + exact: mathcomp_bernoulli_total R q01.
  - apply AUFFinite.
    apply (APFProb
      (front := fun b => meas_ret (APHRet b))
      (Good := fun _ => True)); first apply meas_ae_true.
    move=> b _. constructor.
Qed.

End RealOraclePWeak.
