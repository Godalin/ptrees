(** Explicit native Q-to-R bridge. No FreeOmega or external model is needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.Enum Require Import Representation.
From PTree.Prob.Backend.SubEnum Require Import Measure Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import RatSubTypes Enum GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Embedding.
Variable R : realType.
Definition real_of_enum {A} (mu : Enum A) : list (R*A) :=
  List.map (fun px => (ratr (Qval (fst px)), snd px)) mu.
Lemma real_of_enum_expect {A} (mu : Enum A) f :
  real_enum_expect f (real_of_enum mu) = enum_real_expect f mu.
Proof. induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite IH]. Qed.

Definition subenumQ_to_R {A} (mu : SubEnum A) : SubEnumR R A.
Proof.
  refine (@Build_SubEnumR R A (real_of_enum (subenum_raw mu)) _ _).
  - intros p x Hin; apply List.in_map_iff in Hin; destruct Hin as [[q y] [He Hq]].
    cbn in He; inversion He; subst; rewrite ler0q; exact: Qval_nnQ_ge0.
  - rewrite real_of_enum_expect; apply subenum_real_expect_bound=> x; exact: lexx.
Defined.
Theorem subenumQ_to_R_expect {A} (mu : SubEnum A) (f : A -> R) :
  subenumR_expect (subenumQ_to_R mu) f = enum_real_expect f (subenum_raw mu).
Proof. exact: real_of_enum_expect. Qed.
Theorem subenumQ_to_R_ret {A} (x : A) :
  subenumR_eq (subenumQ_to_R (subenum_ret x)) (subenumR_ret R x).
Proof. intro f; rewrite subenumQ_to_R_expect; by rewrite /= /subenumR_expect /= rmorph1. Qed.
Theorem subenumQ_to_R_zero {A} :
  subenumR_eq (subenumQ_to_R (@subenum_zero A)) (subenumR_zero R).
Proof. intro f; reflexivity. Qed.
Theorem subenumQ_to_R_bind {A B} (mu : SubEnum A) (k : A -> SubEnum B) :
  subenumR_eq (subenumQ_to_R (subenum_bind mu k))
    (subenumR_bind (subenumQ_to_R mu) (fun x => subenumQ_to_R (k x))).
Proof.
  intro f; rewrite subenumR_expect_bind !subenumQ_to_R_expect.
  change (enum_real_expect f (bind_Enum (subenum_raw mu) (fun x => subenum_raw (k x))) =
    enum_real_expect (fun x => subenumR_expect (subenumQ_to_R (k x)) f) (subenum_raw mu)).
  rewrite enum_real_expect_bind.
  have He : (fun x => enum_real_expect f (subenum_raw (k x))) =
      (fun x => subenumR_expect (subenumQ_to_R (k x)) f).
  { apply functional_extensionality=> x; symmetry; exact: subenumQ_to_R_expect. }
  by rewrite He.
Qed.
End Embedding.
