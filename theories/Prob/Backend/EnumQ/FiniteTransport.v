(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset bigop ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.EnumQ.SemanticCoupling PTree.Prob.Backend.Common.FiniteRationalTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition finite_weighted_enumQ {I : finType} {A}
    (weights : I -> nnQ) (decode : I -> A) : EnumQ A :=
  [seq (weights i, decode i) | i <- enum I].

Lemma weighted_seq_atom {I} {A : eqType} (weights : I -> nnQ)
    (decode : I -> A) indices a :
  Qval (acc_mass a [seq (weights i, decode i) | i <- indices]) =
  \sum_(i <- indices) (if decode i == a then Qval (weights i) else 0).
Proof.
  elim: indices=> [|i indices IH]; [by rewrite big_nil|].
  rewrite big_cons /= acc_mass_cons. cbn [fst snd].
  case: (decode i == a).
  - change (Qval (acc_mass a [seq (weights j, decode j) | j <- indices]) + Qval (weights i) =
      Qval (weights i) + \sum_(j <- indices) (if decode j == a then Qval (weights j) else 0)).
    rewrite IH. exact: addrC.
  - change (Qval (acc_mass a [seq (weights j, decode j) | j <- indices]) + 0 =
      0 + \sum_(j <- indices) (if decode j == a then Qval (weights j) else 0)).
    by rewrite IH addr0 add0r.
Qed.

Lemma finite_weighted_enumQ_atom {I : finType} {A : eqType}
    (weights : I -> nnQ) (decode : I -> A) a :
  Qval (acc_mass a (finite_weighted_enumQ weights decode)) =
  \sum_i (if decode i == a then Qval (weights i) else 0).
Proof. by rewrite /finite_weighted_enumQ weighted_seq_atom big_enum. Qed.

Lemma finite_weighted_enumQ_map {I : finType} {A B} weights (decode : I -> A) (f : A -> B) :
  emap f (finite_weighted_enumQ weights decode) =
  finite_weighted_enumQ weights (fun i => f (decode i)).
Proof. by rewrite /finite_weighted_enumQ /emap -map_comp. Qed.

Lemma finite_weighted_enumQ_identity_atom {I : finType} (weights : I -> nnQ) i :
  Qval (acc_mass i (finite_weighted_enumQ weights id)) = Qval (weights i).
Proof. by rewrite finite_weighted_enumQ_atom -big_mkcond big_pred1_eq. Qed.

Lemma finite_weighted_enumQ_sum {I : finType} (weights : I -> nnQ) (P : pred I) :
  \sum_(i | P i) Qval (acc_mass i (finite_weighted_enumQ weights id)) =
  \sum_(i | P i) Qval (weights i).
Proof. apply eq_bigr=> i _. exact: finite_weighted_enumQ_identity_atom. Qed.

Section MatrixEnumQ.
Context {X Y : finType} (w : X -> Y -> nnQ).
Let joint := finite_weighted_enumQ (fun xy : X * Y => w xy.1 xy.2) id.

Lemma finite_matrix_left_atom x :
  Qval (acc_mass x (emap fst joint)) = \sum_y Qval (w x y).
Proof.
  rewrite /joint finite_weighted_enumQ_map finite_weighted_enumQ_atom.
  rewrite -(@pair_bigA rat 0 _ X Y (fun i j => if i == x then Qval (w i j) else 0)).
  transitivity (\sum_i (if i == x then \sum_y Qval (w i y) else 0)).
  - apply eq_bigr=> i _. case: (i == x); [reflexivity|by rewrite big1].
  - by rewrite -big_mkcond big_pred1_eq.
Qed.

Lemma finite_matrix_right_atom y :
  Qval (acc_mass y (emap snd joint)) = \sum_x Qval (w x y).
Proof.
  rewrite /joint finite_weighted_enumQ_map finite_weighted_enumQ_atom.
  rewrite -(@pair_bigA rat 0 _ X Y (fun i j => if j == y then Qval (w i j) else 0)) exchange_big.
  transitivity (\sum_j (if j == y then \sum_x Qval (w x j) else 0)).
  - apply eq_bigr=> j _. case: (j == y); [reflexivity|by rewrite big1].
  - by rewrite -big_mkcond big_pred1_eq.
Qed.
End MatrixEnumQ.

(** Realize a finite rational matrix by an ACTUAL weighted enumeration.
    Arbitrary zero entries and duplicate entries of the marginals are
    harmless: marginal equality is EqEnumQ, not list equality. *)
Theorem finite_enumQ_transport {X Y : finType} (edge : X -> Y -> bool)
    (mu : EnumQ X) (nu : EnumQ Y) :
  rational_hall (fun x => Qval (acc_mass x mu)) (fun y => Qval (acc_mass y nu)) edge ->
  \sum_x Qval (acc_mass x mu) = \sum_y Qval (acc_mass y nu) ->
  coupling (fun x y => edge x y) mu nu.
Proof.
  intros Hall Htotal.
  destruct (finite_rational_transport
    (fun x => Qval_nnQ_ge0 (acc_mass x mu))
    (fun y => Qval_nnQ_ge0 (acc_mass y nu)) Hall Htotal)
    as [w [Hpos [Hrows [Hcols Hsupport]]]].
  pose (weights := fun x y => mknnQ (w x y) (Hpos x y)).
  exists (finite_weighted_enumQ (fun xy : X * Y => weights xy.1 xy.2) id).
  - intro x. apply val_inj.
    change (Qval (acc_mass x (emap fst
      (finite_weighted_enumQ (fun xy : X * Y => weights xy.1 xy.2) id))) = Qval (acc_mass x mu)).
    rewrite finite_matrix_left_atom. exact (Hrows x).
  - intro y. apply val_inj.
    change (Qval (acc_mass y (emap snd
      (finite_weighted_enumQ (fun xy : X * Y => weights xy.1 xy.2) id))) = Qval (acc_mass y nu)).
    rewrite finite_matrix_right_atom. exact (Hcols y).
  - intros x y Hxy. apply Hsupport.
    have Hpositive := proj1 (@lt_0_nnQ_iff_ne_0
      (acc_mass (x,y) (finite_weighted_enumQ (fun xy : X * Y => weights xy.1 xy.2) id))) Hxy.
    change (is_true (0 < Qval (acc_mass (x,y)
      (finite_weighted_enumQ (fun xy : X * Y => weights xy.1 xy.2) id)))) in Hpositive.
    by rewrite finite_weighted_enumQ_identity_atom in Hpositive.
Qed.

(** The finite transport theorem now returns the maintained native
    coupling certificate, including both exact semantic marginals. *)
Theorem subenumQ_finite_transport_joint {X Y : finType} (edge : X -> Y -> bool)
    (mu : SubEnumQ X) (nu : SubEnumQ Y) :
  rational_hall (fun x => Qval (acc_mass x (subenumQ_raw mu)))
    (fun y => Qval (acc_mass y (subenumQ_raw nu))) edge ->
  \sum_x Qval (acc_mass x (subenumQ_raw mu)) =
    \sum_y Qval (acc_mass y (subenumQ_raw nu)) ->
  exists joint : SubEnumQ (X * Y),
    @semantic_coupling SubEnumQ SubEnumQ_SemanticMeasure X Y
      (fun x y => edge x y) mu nu joint.
Proof.
  intros Hall Htotal. apply subenumQ_coupling_realization.
  change (@sem_lift EnumQ EnumQ_SemanticMeasure X Y
    (fun x y => edge x y) (subenumQ_raw mu) (subenumQ_raw nu)).
  apply enumQ_sem_lift_of_coupling. exact (finite_enumQ_transport Hall Htotal).
Qed.
