(** Value maps of checked rational weightings. The result preserves raw
    list order and multiplicity; no proof-field equality is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import List Morphisms.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssralg ssrnum rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms.
From PTree.Prob.Backend.EnumQ Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module EnumQMap.
Import EnumQ GRing.Theory.
Local Open Scope ring_scope.

Definition emap {A B} (f : A -> B) (mu : EnumQ A) : EnumQ B := enumQ_map f mu.

Lemma emap_id {A} (mu : EnumQ A) : enumQ_raw (emap id mu) = enumQ_raw mu.
Proof.
  change (List.map (fun px => (px.1,px.2)) (enumQ_raw mu) = enumQ_raw mu).
  by elim: (enumQ_raw mu)=> [|[p x] tl IH] //=; rewrite IH.
Qed.
Lemma emap_comp {A B C} (f : A -> B) (g : B -> C) (mu : EnumQ A) :
  enumQ_raw (emap g (emap f mu)) = enumQ_raw (emap (fun x => g (f x)) mu).
Proof.
  change (List.map (fun px => (px.1,g px.2))
    (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)) =
    List.map (fun px => (px.1,g (f px.2))) (enumQ_raw mu)).
  rewrite List.map_map; apply List.map_ext=> [[p x]]; reflexivity.
Qed.
Lemma emap_scale {A B} (f : A -> B) p (Hp : 0 <= p) (mu : EnumQ A) :
  enumQ_raw (emap f (scale_EnumQ Hp mu)) = enumQ_raw (scale_EnumQ Hp (emap f mu)).
Proof.
  change (List.map (fun px => (px.1,f px.2))
    (finite_weight_map p (enumQ_raw mu)) =
    finite_weight_map p (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu))).
  rewrite /finite_weight_map !List.map_map; apply List.map_ext=> [[q x]]; reflexivity.
Qed.
Lemma emap_app {A B} (f : A -> B) (mu nu : EnumQ A) :
  enumQ_raw (emap f (enumQ_app mu nu)) = enumQ_raw (enumQ_app (emap f mu) (emap f nu)).
Proof. exact: List.map_app. Qed.
Lemma emap_bind {A B C} (f : B -> C) (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (emap f (bind_EnumQ mu k)) =
  enumQ_raw (bind_EnumQ mu (fun x => emap f (k x))).
Proof.
  change (List.map (fun px => (px.1,f px.2))
    (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x))) =
    finite_bind (enumQ_raw mu)
      (fun x => List.map (fun px => (px.1,f px.2)) (enumQ_raw (k x)))).
  elim: (enumQ_raw mu)=> [|[p x] tl IH] //=.
  rewrite List.map_app IH; congr (_ ++ _).
  rewrite /finite_weight_map !List.map_map; apply List.map_ext=> [[q y]]; reflexivity.
Qed.
Lemma bind_ret_emap {A B} (f : A -> B) (mu : EnumQ A) :
  enumQ_raw (bind_EnumQ mu (fun x => ret_EnumQ (f x))) = enumQ_raw (emap f mu).
Proof.
  change (finite_bind (enumQ_raw mu) (fun x => [:: (1,f x)]) =
    List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)).
  by elim: (enumQ_raw mu)=> [|[p x] tl IH] //=; rewrite mulr1 IH.
Qed.

Lemma acc_mass_emap {A B : eqType} (f : A -> B) (mu : EnumQ A) b :
  acc_mass b (emap f mu) =
  sumq [seq px.1 | px <- enumQ_raw mu & f px.2 == b].
Proof.
  change (finite_expect (fun y => if y == b then 1 else 0)
    (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)) =
    sumq [seq px.1 | px <- enumQ_raw mu & f px.2 == b]).
  rewrite finite_expect_map; elim: (enumQ_raw mu)=> [|[p x] tl IH] //=.
  by case: (f x == b)=> /=; rewrite ?mulr1 ?mulr0 ?add0r IH.
Qed.
Lemma acc_mass_filter {A : eqType} (P : pred A) (mu : EnumQ A) a :
  acc_mass a (enumQ_filter (fun px => P px.2) mu) =
  if P a then acc_mass a mu else 0.
Proof.
  change (finite_atom a (List.filter (fun px => P px.2) (enumQ_raw mu)) =
    if P a then finite_atom a (enumQ_raw mu) else 0).
  elim: (enumQ_raw mu)=> [|[p x] tl IH]; first by case: (P a).
  rewrite /=; case Px: (P x); rewrite ?finite_atom_cons IH.
  - case Hxa: (x == a).
    + move/eqP: Hxa=> He; subst x; by rewrite Px.
    + by case: (P a); rewrite ?add0r.
  - case Hxa: (x == a).
    + move/eqP: Hxa=> He; subst x; by rewrite Px.
    + by case: (P a); rewrite ?add0r.
Qed.
Lemma enumQ_filter_proper {A : eqType} (P : pred A) :
  Proper (EqEnumQ ==> EqEnumQ) (enumQ_filter (fun px => P px.2)).
Proof. move=> mu nu H a; rewrite !acc_mass_filter; by case: (P a); rewrite ?H. Qed.
Lemma emap_proper {A B : eqType} (f : A -> B) :
  Proper (EqEnumQ ==> EqEnumQ) (emap f).
Proof.
  move=> mu nu H b; change
    (finite_expect (fun y => if y == b then 1 else 0)
       (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)) =
     finite_expect (fun y => if y == b then 1 else 0)
       (List.map (fun px => (px.1,f px.2)) (enumQ_raw nu))).
  rewrite !finite_expect_map; apply finite_expect_atoms_eq; exact H.
Qed.
End EnumQMap.
Export EnumQMap.
