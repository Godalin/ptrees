(** Explicit native Q-to-R bridge. No FreeOmega or external model is needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteScalarMap.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Embedding.
Variable R : realType.
Definition real_of_enumQ {A} (mu : EnumQ A) : list (R*A) :=
  finite_map_weights (ratr : {rmorphism rat -> R}) (enumQ_raw mu).
Lemma real_of_enumQ_expect {A} (mu : EnumQ A) f :
  real_enum_expect f (real_of_enumQ mu) = enumQ_real_expect f mu.
Proof. reflexivity. Qed.

Lemma rational_scalar_monotone (x y : rat) :
  x <= y -> (ratr x : R) <= ratr y.
Proof. by rewrite ler_rat. Qed.
Definition subenumQ_to_R {A} (mu : SubEnumQ A) : SubEnumR R A :=
  finite_subdist_map_weights rational_scalar_monotone mu.
Theorem subenumQ_to_R_expect {A} (mu : SubEnumQ A) (f : A -> R) :
  subenumR_expect (subenumQ_to_R mu) f = enumQ_real_expect f (subenumQ_raw mu).
Proof. exact: real_of_enumQ_expect. Qed.
Theorem subenumQ_to_R_ret {A} (x : A) :
  subenumR_eq (subenumQ_to_R (subenumQ_ret x)) (subenumR_ret R x).
Proof.
  intro f; rewrite subenumQ_to_R_expect.
  change (enumQ_real_expect f (ret_EnumQ x) = subenumR_expect (subenumR_ret R x) f).
  rewrite enumQ_real_expect_ret.
  by rewrite /subenumR_expect /subenumR_ret /= mul1r addr0.
Qed.
Theorem subenumQ_to_R_zero {A} :
  subenumR_eq (subenumQ_to_R (@subenumQ_zero A)) (subenumR_zero R).
Proof. intro f; reflexivity. Qed.
Theorem subenumQ_to_R_bind {A B} (mu : SubEnumQ A) (k : A -> SubEnumQ B) :
  subenumR_eq (subenumQ_to_R (subenumQ_bind mu k))
    (subenumR_bind (subenumQ_to_R mu) (fun x => subenumQ_to_R (k x))).
Proof.
  intro f; rewrite subenumR_expect_bind !subenumQ_to_R_expect.
  change (enumQ_real_expect f (bind_EnumQ (subenumQ_raw mu) (fun x => subenumQ_raw (k x))) =
    enumQ_real_expect (fun x => subenumR_expect (subenumQ_to_R (k x)) f) (subenumQ_raw mu)).
  rewrite enumQ_real_expect_bind.
  have He : (fun x => enumQ_real_expect f (subenumQ_raw (k x))) =
      (fun x => subenumR_expect (subenumQ_to_R (k x)) f).
  { apply functional_extensionality=> x; symmetry; exact: subenumQ_to_R_expect. }
  by rewrite He.
Qed.
End Embedding.
