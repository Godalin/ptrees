Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg.

From PTree.Prob Require Import DiscreteMC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module EnumMap.
Import Enum.
Import RatSubTypes.NonnegQNotations.
Import GRing.Theory.
#[local] Open Scope subrat_scope.
#[local] Open Scope ring_scope.

Definition emap {A B} (f : A -> B) (mu : Enum A) : Enum B :=
  map (fun px => (fst px, f (snd px))) mu.

Lemma emap_id {A} (mu : Enum A) :
  emap id mu = mu.
Proof.
  elim: mu => [//|[p a] mu IH] //=.
  by rewrite IH.
Qed.

Lemma emap_comp {A B C} (f : A -> B) (g : B -> C) (mu : Enum A) :
  emap g (emap f mu) = emap (fun x => g (f x)) mu.
Proof.
  elim: mu => [//|[p a] mu IH] //=.
  by rewrite IH.
Qed.

Lemma acc_mass_emap {A : eqType} {B : eqType} (f : A -> B)
    (mu : Enum A) (b : B) :
  acc_mass b (emap f mu) =
  sumq [seq fst px | px <- mu & f (snd px) == b].
Proof.
  rewrite /acc_mass /emap /unzip1.
  elim: mu => [//|[p a] mu IH] //=.
  by case: (f a == b) => //=; rewrite IH.
Qed.

Lemma acc_mass_filter {A : eqType} (P : pred A) (mu : Enum A) (a : A) :
  acc_mass a [seq px <- mu | P (snd px)] =
  if P a then acc_mass a mu else sumq [::].
Proof.
  case Pa: (P a).
  - elim: mu => [//|[p x] mu IH].
    rewrite filter_cons.
    case Px: (P x).
    + rewrite /= !acc_mass_cons IH.
      reflexivity.
    + rewrite /= acc_mass_cons IH.
      have E : x != a.
        apply/eqP => Hxa.
        have HP := f_equal P Hxa.
        congruence.
      by rewrite /= (negbTE E) addr0.
  - elim: mu => [//|[p x] mu IH].
    rewrite filter_cons.
    case Px: (P x).
    + rewrite /= !acc_mass_cons IH.
      have E : x != a.
        apply/eqP => Hxa.
        have HP := f_equal P Hxa.
        congruence.
      rewrite /= (negbTE E).
      by rewrite addr0.
    + exact IH.
Qed.

Lemma enum_filter_proper {A : eqType} (P : pred A) :
  Proper (EqEnum ==> EqEnum)
    (fun mu : Enum A => [seq px <- mu | P (snd px)]).
Proof.
  move=> mu nu H a.
  rewrite !acc_mass_filter.
  by case: (P a); rewrite ?H.
Qed.

Lemma acc_mass_emap_total {A : eqType} {B : eqType} (f : A -> B)
    (mu : Enum A) (b : B) :
  acc_mass b (emap f mu) =
  mass [seq px <- mu | f (snd px) == b]
       (supp [seq px <- mu | f (snd px) == b]).
Proof.
  rewrite acc_mass_emap mass_supp_eq_sumq_fst /unzip1.
  by elim: mu => [//|[p a] mu IH] //=.
Qed.

Lemma emap_proper {A : eqType} {B : eqType} (f : A -> B) :
  Proper (EqEnum ==> EqEnum) (emap f).
Proof.
  move=> mu nu H b.
  set P := fun x : A => f x == b.
  have HF : [seq px <- mu | P (snd px)] ==Enum
            [seq px <- nu | P (snd px)].
    exact: enum_filter_proper H.
  rewrite !acc_mass_emap_total.
  transitivity
    (mass [seq px <- nu | P (snd px)]
          (supp [seq px <- mu | P (snd px)])).
  - exact: mass_eq1_of_enumeq HF.
  - apply mass_eq2_of_mem_eq.
    + exact: supp_enum_eq_mem_eq HF.
    + exact: supp_uniq _.
    + exact: supp_uniq _.
Qed.

End EnumMap.

Export EnumMap.
