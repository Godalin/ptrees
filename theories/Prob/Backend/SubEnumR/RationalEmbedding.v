(** Explicit native Q-to-R bridge. No FreeOmega or external model is needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import RatSubTypes EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Embedding.
Variable R : realType.
Definition real_of_enumQ {A} (mu : EnumQ A) : list (R*A) :=
  List.map (fun px => (ratr (Qval (fst px)), snd px)) mu.
Lemma real_of_enumQ_expect {A} (mu : EnumQ A) f :
  real_enum_expect f (real_of_enumQ mu) = enumQ_real_expect f mu.
Proof.
  induction mu as [|[p x] tl IH]; first reflexivity.
  change (real_enum_expect f ((ratr (Qval p),x)::real_of_enumQ tl) =
    ratr (Qval p) * f x + enumQ_real_expect f tl).
  by rewrite real_enum_expect_cons IH.
Qed.

Definition subenumQ_to_R {A} (mu : SubEnumQ A) : SubEnumR R A.
Proof.
  refine (@subenumR_of_list R A (real_of_enumQ (subenumQ_raw mu)) _ _).
  - intros p x Hin; apply List.in_map_iff in Hin; destruct Hin as [[q y] [He Hq]].
    cbn in He; inversion He; subst; rewrite ler0q; exact: Qval_nnQ_ge0.
  - rewrite real_of_enumQ_expect; apply subenumQ_real_expect_bound=> x; exact: lexx.
Defined.
Theorem subenumQ_to_R_expect {A} (mu : SubEnumQ A) (f : A -> R) :
  subenumR_expect (subenumQ_to_R mu) f = enumQ_real_expect f (subenumQ_raw mu).
Proof. exact: real_of_enumQ_expect. Qed.
Theorem subenumQ_to_R_ret {A} (x : A) :
  subenumR_eq (subenumQ_to_R (subenumQ_ret x)) (subenumR_ret R x).
Proof. intro f; rewrite subenumQ_to_R_expect; by rewrite /= /subenumR_expect /= rmorph1. Qed.
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
