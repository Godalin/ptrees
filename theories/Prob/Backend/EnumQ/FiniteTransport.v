(** Actual finite rational transport over ordinary scalar weights.
    Nonnegativity is supplied once to the shared container constructor. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset bigop ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteRationalTransport.
From PTree.Prob.Backend.EnumQ Require Import Representation Map Coupling Measure SemanticCoupling.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Interface Require Import Measure SemanticCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition finite_weighted_enumQ {I : finType} {A} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) (decode : I -> A) : EnumQ A.
Proof.
  refine (enumQ_of_list (mu := [seq (weights i,decode i) | i <- enum I]) _).
  move=> p x /List.in_map_iff [i [He _]]; inversion He; subst; exact: Hnn.
Defined.
Lemma weighted_seq_atom {I} {A : eqType} (weights : I -> rat) (decode : I -> A) indices a :
  finite_atom a [seq (weights i,decode i) | i <- indices] =
  \sum_(i <- indices) (if decode i == a then weights i else 0).
Proof.
  elim: indices=> [|i tl IH]; first by rewrite big_nil.
  rewrite big_cons /= finite_atom_cons IH; reflexivity.
Qed.
Lemma finite_weighted_enumQ_atom {I : finType} {A : eqType} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) (decode : I -> A) a :
  acc_mass a (finite_weighted_enumQ Hnn decode) =
  \sum_i (if decode i == a then weights i else 0).
Proof. by rewrite /acc_mass /finite_weighted_enumQ /= weighted_seq_atom big_enum. Qed.
Lemma finite_weighted_enumQ_map {I : finType} {A B} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) (decode : I -> A) (f : A -> B) :
  enumQ_raw (emap f (finite_weighted_enumQ Hnn decode)) =
  enumQ_raw (finite_weighted_enumQ Hnn (fun i => f (decode i))).
Proof. exact: List.map_map. Qed.
Lemma finite_weighted_enumQ_identity_atom {I : finType} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) i :
  acc_mass i (finite_weighted_enumQ Hnn id) = weights i.
Proof. by rewrite finite_weighted_enumQ_atom -big_mkcond big_pred1_eq. Qed.
Lemma finite_weighted_enumQ_sum {I : finType} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) (P : pred I) :
  \sum_(i | P i) acc_mass i (finite_weighted_enumQ Hnn id) =
  \sum_(i | P i) weights i.
Proof. apply eq_bigr=> i _; exact: finite_weighted_enumQ_identity_atom. Qed.

Section MatrixEnumQ.
Context {X Y : finType} (w : X -> Y -> rat) (Hnn : forall x y, 0 <= w x y).
Let joint := finite_weighted_enumQ (fun xy : X*Y => Hnn xy.1 xy.2) id.
Lemma finite_matrix_left_atom x :
  acc_mass x (emap fst joint) = \sum_y w x y.
Proof.
  have Hdata := finite_weighted_enumQ_map (fun xy : X*Y => Hnn xy.1 xy.2) id fst.
  change (acc_mass x (emap fst (finite_weighted_enumQ (fun xy : X*Y => Hnn xy.1 xy.2) id)) = \sum_y w x y).
  rewrite /acc_mass Hdata -/(acc_mass x (finite_weighted_enumQ (fun xy : X*Y => Hnn xy.1 xy.2) fst)).
  rewrite finite_weighted_enumQ_atom.
  rewrite -(@pair_bigA rat 0 _ X Y (fun i j => if i == x then w i j else 0)).
  transitivity (\sum_i (if i == x then \sum_y w i y else 0)).
  - apply eq_bigr=> i _; case: (i == x); [reflexivity|by rewrite big1].
  - by rewrite -big_mkcond big_pred1_eq.
Qed.
Lemma finite_matrix_right_atom y :
  acc_mass y (emap snd joint) = \sum_x w x y.
Proof.
  have Hdata := finite_weighted_enumQ_map (fun xy : X*Y => Hnn xy.1 xy.2) id snd.
  change (acc_mass y (emap snd (finite_weighted_enumQ (fun xy : X*Y => Hnn xy.1 xy.2) id)) = \sum_x w x y).
  rewrite /acc_mass Hdata -/(acc_mass y (finite_weighted_enumQ (fun xy : X*Y => Hnn xy.1 xy.2) snd)).
  rewrite finite_weighted_enumQ_atom.
  rewrite -(@pair_bigA rat 0 _ X Y (fun i j => if j == y then w i j else 0)) exchange_big.
  transitivity (\sum_j (if j == y then \sum_x w x j else 0)).
  - apply eq_bigr=> j _; case: (j == y); [reflexivity|by rewrite big1].
  - by rewrite -big_mkcond big_pred1_eq.
Qed.
End MatrixEnumQ.

Theorem finite_enumQ_transport {X Y : finType} (edge : X -> Y -> bool)
    (mu : EnumQ X) (nu : EnumQ Y) :
  rational_hall (fun x => acc_mass x mu) (fun y => acc_mass y nu) edge ->
  \sum_x acc_mass x mu = \sum_y acc_mass y nu ->
  coupling (fun x y => edge x y) mu nu.
Proof.
  move=> Hall Htotal.
  have [w [Hpos [Hrows [Hcols Hsupport]]]] := finite_rational_transport
    (fun x => acc_mass_nonnegative x mu) (fun y => acc_mass_nonnegative y nu) Hall Htotal.
  exists (finite_weighted_enumQ (fun xy : X*Y => Hpos xy.1 xy.2) id).
  - move=> x; rewrite finite_matrix_left_atom; exact: Hrows.
  - move=> y; rewrite finite_matrix_right_atom; exact: Hcols.
  - move=> x y Hxy; apply Hsupport.
    rewrite finite_weighted_enumQ_identity_atom in Hxy.
    by rewrite lt0r Hxy Hpos.
Qed.

Theorem subenumQ_finite_transport_joint {X Y : finType} (edge : X -> Y -> bool)
    (mu : SubEnumQ X) (nu : SubEnumQ Y) :
  rational_hall (fun x => acc_mass x (subenumQ_raw mu))
    (fun y => acc_mass y (subenumQ_raw nu)) edge ->
  \sum_x acc_mass x (subenumQ_raw mu) = \sum_y acc_mass y (subenumQ_raw nu) ->
  exists joint : SubEnumQ (X*Y), @semantic_coupling SubEnumQ SubEnumQ_SemanticMeasure X Y
    (fun x y => edge x y) mu nu joint.
Proof.
  move=> Hall Htotal; apply subenumQ_coupling_realization.
  change (@sem_lift EnumQ EnumQ_SemanticMeasure X Y (fun x y => edge x y)
    (subenumQ_raw mu) (subenumQ_raw nu)).
  apply enumQ_sem_lift_of_coupling; exact: finite_enumQ_transport Hall Htotal.
Qed.
