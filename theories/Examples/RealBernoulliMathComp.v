Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum
  order rat reals normedtype.
From mathcomp.analysis Require Import topology sequences ereal.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration MathCompMeasure.
From PTree.Examples Require Import RealBernoulliOracle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.
#[local] Open Scope classical_set_scope.

Unset Automatic Proposition Inductives.
Variant real_mathcomp_coinE : Type -> Type := .

Section RealOracleBackend.
Context (R : realType).

Local Notation M := (MathCompKernelMeasure R).

Definition mathcomp_half_coin : M bool :=
  @mathcomp_bernoulli R (1 / 2 : R).

Definition mathcomp_oracle_transition
    (qbit : binary_oracle) (n : nat) : M (nat + bool) :=
  meas_bind mathcomp_half_coin (fun random =>
    if qbit n then
      if random then meas_ret (inl n.+1) else meas_ret (inr true)
    else
      if random then meas_ret (inr false) else meas_ret (inl n.+1)).

Definition mathcomp_oracle_step
    (qbit : binary_oracle) (n : nat) :
    ptree real_mathcomp_coinE M (nat + bool) :=
  Prob (mathcomp_oracle_transition qbit n)
    (fun next : nat + bool => Ret next).

Definition mathcomp_binary_oracle_coin (qbit : binary_oracle) :
    ptree real_mathcomp_coinE M bool :=
  PTree.iter (mathcomp_oracle_step qbit) 0.

(** The direct specification program samples from MathComp's genuine
    real-valued Bernoulli probability measure. *)
Definition mathcomp_direct_bernoulli (q : R) :
    ptree real_mathcomp_coinE M bool :=
  Prob (@mathcomp_bernoulli R q) (fun b : bool => Ret b).

(** Concrete interpretation of the abstract oracle representation from
    [RealBernoulliOracle]: rational binary prefixes converge in [R]. *)
Definition mathcomp_oracle_represents
    (qbit : binary_oracle) (q : R) : Prop :=
  (fun n => ratr (oracle_prefix qbit n)) @ \oo --> q.

End RealOracleBackend.
