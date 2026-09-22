(** Atom mass for finite ordinary-scalar lists. These are algebraic identities,
    not a new equality or coupling relation. Repeated atoms are summed; the
    original representation is never rewritten into a deduplicated list. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq fintype bigop ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section FiniteAtoms.
Variable R : numDomainType.

Definition finite_atom {A : eqType} (x : A) (mu : list (R * A)) : R :=
  finite_expect (fun y => if y == x then 1 else 0) mu.

Lemma finite_atom_nil {A : eqType} (x : A) : finite_atom x [::] = 0.
Proof. reflexivity. Qed.

Lemma finite_atom_cons {A : eqType} (x y : A) p mu :
  finite_atom x ((p,y)::mu) = (if y == x then p else 0) + finite_atom x mu.
Proof. rewrite /finite_atom /=; by case: (y == x); rewrite ?mulr0 ?mulr1. Qed.

Lemma finite_atom_app {A : eqType} (x : A) mu nu :
  finite_atom x (mu ++ nu) = finite_atom x mu + finite_atom x nu.
Proof. exact: finite_expect_app. Qed.

Lemma finite_atom_scale {A : eqType} (x : A) p mu :
  finite_atom x (finite_weight_map p mu) = p * finite_atom x mu.
Proof. exact: finite_expect_weight_map. Qed.

Lemma finite_atom_bind {A} {B : eqType} (x : B) (mu : list (R * A)) k :
  finite_atom x (finite_bind mu k) = finite_expect (fun a => finite_atom x (k a)) mu.
Proof. exact: finite_expect_bind. Qed.

Lemma finite_atom_nonnegative {A : eqType} (x : A) mu :
  finite_nonnegative mu -> 0 <= finite_atom x mu.
Proof.
  move=> H; apply finite_expect_nonnegative; first exact H.
  move=> y; case: (y == x); [exact: ler01|exact: lexx].
Qed.

Lemma finite_expect_by_atoms {A : finType} (mu : list (R * A)) f :
  finite_expect f mu = \sum_x finite_atom x mu * f x.
Proof.
  elim: mu=> [|[p a] mu IH].
  - rewrite /= big1 // => x _. exact: mul0r.
  - rewrite /= IH. transitivity
      (\sum_x ((if a == x then p else 0) * f x + finite_atom x mu * f x)).
    + rewrite big_split. apply congr1 with (f := fun z => z + \sum_x finite_atom x mu * f x).
      transitivity (\sum_x (if a == x then p * f x else 0)).
      * by rewrite -big_mkcond (big_pred1 a).
      * apply eq_bigr=> x _. by case: (a == x); rewrite ?mul0r.
    + apply eq_bigr=> x _. by rewrite finite_atom_cons mulrDl.
Qed.

Lemma finite_mass_by_atoms {A : finType} (mu : FiniteEnum R A) :
  finite_mass mu = \sum_x finite_atom x (finite_enum_raw mu).
Proof.
  rewrite /finite_mass /finite_enum_expect finite_expect_by_atoms.
  apply eq_bigr=> x _; exact: mulr1.
Qed.

Lemma finite_expect_atoms_ext {A : finType} (mu nu : list (R * A)) f :
  (forall x, finite_atom x mu = finite_atom x nu) -> finite_expect f mu = finite_expect f nu.
Proof. move=> H; rewrite !finite_expect_by_atoms; apply eq_bigr=> x _; by rewrite H. Qed.
End FiniteAtoms.
