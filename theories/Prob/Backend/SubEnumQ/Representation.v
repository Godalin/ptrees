(** Rational subdistributions use the same container as finite-real sampling.
    No scalar subtype or conversion from a legacy list is involved. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Backend.EnumQ Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition enumQ_mass {A} (mu : EnumQ A) : rat := enumQ_expect (fun _ => 1) mu.
Definition enumQ_subprob {A} (mu : EnumQ A) : Prop := enumQ_mass mu <= 1.

Lemma enumQ_subprob_ret {A} (x : A) : enumQ_subprob (ret_EnumQ x).
Proof. by rewrite /enumQ_subprob /enumQ_mass enumQ_expect_ret. Qed.
Lemma enumQ_subprob_zero {A} : enumQ_subprob (@enumQ_zero A).
Proof. exact: ler01. Qed.
Lemma enumQ_expect_le_mass {A} (mu : EnumQ A) (f : A -> rat) :
  (forall p x, List.In (p,x) (enumQ_raw mu) -> f x <= 1) ->
  enumQ_expect f mu <= enumQ_mass mu.
Proof.
  move=> H; apply finite_expect_ae_mono; first exact (enumQ_nonnegative mu).
  move=> p x Hin _; exact (H p x Hin).
Qed.
Lemma enumQ_expect_nonnegative {A} (mu : EnumQ A) (f : A -> rat) :
  (forall p x, List.In (p,x) (enumQ_raw mu) -> 0 <= f x) ->
  0 <= enumQ_expect f mu.
Proof.
  move=> H; change (0 <= finite_expect f (enumQ_raw mu)).
  rewrite -(finite_expect_zero (enumQ_raw mu)).
  apply finite_expect_ae_mono; first exact (enumQ_nonnegative mu).
  move=> p x Hin _; exact (H p x Hin).
Qed.
Lemma enumQ_subprob_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_subprob mu -> (forall x, enumQ_subprob (k x)) ->
  enumQ_subprob (bind_EnumQ mu k).
Proof.
  move=> Hmu Hk; rewrite /enumQ_subprob /enumQ_mass enumQ_expect_bind.
  apply: le_trans Hmu; apply enumQ_expect_le_mass=> p x _; exact (Hk x).
Qed.

Definition SubEnumQ (A : Type) := FiniteSubdist rat_rat__canonical__Num_NumDomain A.
Definition subenumQ_raw {A} (mu : SubEnumQ A) : EnumQ A := finite_subdist_enum mu.
Definition subenumQ_data {A} (mu : SubEnumQ A) := enumQ_raw (subenumQ_raw mu).
Lemma subenumQ_bound {A} (mu : SubEnumQ A) : enumQ_subprob (subenumQ_raw mu).
Proof. exact: finite_subdist_mass_bound. Qed.
Definition subenumQ_ret {A} (x : A) : SubEnumQ A := finite_subdist_ret _ x.
Definition subenumQ_zero {A} : SubEnumQ A := finite_subdist_zero _.
Definition subenumQ_bind {A B} (mu : SubEnumQ A) (k : A -> SubEnumQ B) : SubEnumQ B :=
  finite_subdist_bind mu k.
Definition subenumQ_of_list {A} (mu : list (rat*A))
    (Hnn : finite_nonnegative mu) (Hmass : finite_expect (fun _ => 1) mu <= 1) : SubEnumQ A :=
  finite_subdist_of_list Hnn Hmass.
Definition enumQ_as_subprob {A} (mu : EnumQ A) (Hmu : enumQ_subprob mu) : SubEnumQ A :=
  @Build_FiniteSubdist rat_rat__canonical__Num_NumDomain A mu Hmu.
