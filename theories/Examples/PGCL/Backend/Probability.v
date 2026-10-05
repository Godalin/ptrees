(** Executable bounded probability parameters and their finite native coins.
    No completion, forward semantics or PTree proof layer is needed here. *)
From Coq Require Import Utf8 List.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Record probability (W : numDomainType) := Probability {
  bias : W;
  bias_nonnegative : 0 <= bias;
  bias_bounded : bias <= 1
}.

Definition bernoulli {W : numDomainType} (p : probability W) : FiniteSubdist W bool.
Proof.
  refine (finite_subdist_of_list
    (mu := [(bias p,true); (1-bias p,false)]) _ _).
  - intros q b [H|[H|[]]]; inversion H; subst.
    + exact (bias_nonnegative p).
    + by rewrite subr_ge0; apply bias_bounded.
  - cbn. by rewrite !mulr1 addr0 addrC subrK.
Defined.

Lemma bernoulli_expect {W : numDomainType} (p : probability W) (f : bool → W) :
  finite_subdist_expect (bernoulli p) f = bias p * f true + (1-bias p) * f false.
Proof. by rewrite /finite_subdist_expect /finite_enum_expect /= addr0. Qed.

Definition rational_probability := probability rat_rat__canonical__Num_NumDomain.
Definition rational_coin : rational_probability → SubEnumQ bool := @bernoulli _.
