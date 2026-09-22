(** Optional record extensionality for exact witness clients.
    The finite algebra itself compares raw data and does not import this file.
    Function extensionality plus decidable equality on bool suffices to identify
    the invariant proofs; no general proof-irrelevance axiom is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Bool Eqdep_dec FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FiniteListAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma finite_nonnegative_unique {R : numDomainType} {A} raw
    (H K : @finite_nonnegative R A raw) : H = K.
Proof.
  apply functional_extensionality_dep=> p.
  apply functional_extensionality_dep=> x.
  apply functional_extensionality_dep=> Hin.
  apply UIP_dec; exact Bool.bool_dec.
Qed.



Lemma finite_enum_raw_eq {R : numDomainType} {A} (mu nu : FiniteEnum R A) :
  finite_enum_raw mu = finite_enum_raw nu -> mu = nu.
Proof.
  destruct mu as [raw H], nu as [raw' K]; cbn=> He; subst raw'.
  rewrite (finite_nonnegative_unique H K); reflexivity.
Qed.

Lemma finite_subdist_raw_eq {R : numDomainType} {A} (mu nu : FiniteSubdist R A) :
  finite_enum_raw (finite_subdist_enum mu) =
  finite_enum_raw (finite_subdist_enum nu) -> mu = nu.
Proof.
  destruct mu as [e H], nu as [e' K]; cbn=> He.
  have Heq := finite_enum_raw_eq He; subst e'.
  have HK : H = K by apply UIP_dec; exact Bool.bool_dec.
  by rewrite HK.
Qed.

Section ExactAlgebra.
Context {R : numDomainType}.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma finite_enum_bind_assoc_eq {A B C} (mu : FiniteEnum R A)
    (k : A -> FiniteEnum R B) (h : B -> FiniteEnum R C) :
  finite_enum_bind (finite_enum_bind mu k) h =
  finite_enum_bind mu (fun x => finite_enum_bind (k x) h).
Proof. apply finite_enum_raw_eq; exact: finite_bind_assoc. Qed.

Lemma finite_enum_bind_ext_eq {A B} (mu : FiniteEnum R A)
    (k h : A -> FiniteEnum R B) :
  (forall x, k x = h x) -> finite_enum_bind mu k = finite_enum_bind mu h.
Proof. move=> H; apply finite_enum_raw_eq, finite_bind_ext=> x; by rewrite H. Qed.

Lemma finite_enum_bind_ret_eq {A B} (x : A) (k : A -> FiniteEnum R B) :
  finite_enum_bind (finite_enum_ret R x) k = k x.
Proof.
  apply finite_enum_raw_eq.
  change (finite_bind ((1,x)::nil) (fun a => finite_enum_raw (k a)) = finite_enum_raw (k x)).
  rewrite -finite_bind_with_numeric.
  exact (@finite_bind_with_left_unit R (fun p q => p*q) A B 1 x
    (fun a => finite_enum_raw (k a)) (fun p => mul1r p)).
Qed.

Lemma finite_enum_bind_right_unit_eq {A} (mu : FiniteEnum R A) :
  finite_enum_bind mu (fun x => finite_enum_ret R x) = mu.
Proof.
  apply finite_enum_raw_eq.
  change (finite_bind (finite_enum_raw mu) (fun x => cons (1,x) nil) = finite_enum_raw mu).
  rewrite -finite_bind_with_numeric.
  exact (@finite_bind_with_right_unit R (fun p q => p*q) A 1
    (finite_enum_raw mu) (fun p => mulr1 p)).
Qed.

Lemma finite_enum_bind_zero_eq {A B} (mu : FiniteEnum R A) :
  finite_enum_bind mu (fun _ => @finite_enum_zero R B) = @finite_enum_zero R B.
Proof.
  apply finite_enum_raw_eq.
  change (finite_bind (finite_enum_raw mu) (fun _ => @nil (R*B)) = nil).
  by elim: (finite_enum_raw mu)=> [|[p x] tl IH] //=.
Qed.
End ExactAlgebra.
