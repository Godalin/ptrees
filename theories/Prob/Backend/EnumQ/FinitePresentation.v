(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple bigop ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.FiniteTransport PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.IndexedCoupling.
From PTree.Prob.Backend.Common Require Import FinitePresentation.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Positions, not values, form the finite carrier.  In particular this
    representation needs neither an inhabitant nor decidable equality on A,
    and retains duplicate entries and zero weights. *)
Definition enumQ_position {A} (mu : EnumQ A) := finite_position (enumQ_raw mu).
Definition enumQ_position_entry {A} (mu : EnumQ A) (i : enumQ_position mu) :=
  finite_position_entry (enumQ_raw mu) i.
Arguments enumQ_position_entry {A} mu i.
Definition enumQ_position_weight {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_weight (enumQ_raw mu) i.
Definition enumQ_position_value {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_value (enumQ_raw mu) i.
Arguments enumQ_position_weight {A} mu i.
Arguments enumQ_position_value {A} mu i.
Definition enumQ_positions {A} (mu : EnumQ A) : EnumQ (enumQ_position mu) :=
  finite_enum_positions mu.

Lemma enumQ_positions_decode {A} (mu : EnumQ A) :
  enumQ_raw (emap (enumQ_position_value mu) (enumQ_positions mu)) = enumQ_raw mu.
Proof. exact: finite_positions_decode. Qed.

Lemma enumQ_positions_subprob {A} (mu : SubEnumQ A) :
  enumQ_subprob (enumQ_positions (subenumQ_raw mu)).
Proof.
  change (finite_mass (finite_enum_positions (subenumQ_raw mu)) <= 1).
  rewrite finite_enum_positions_mass; exact (subenumQ_bound mu).
Qed.
Definition subenumQ_positions {A} (mu : SubEnumQ A) : SubEnumQ (enumQ_position (subenumQ_raw mu)) :=
  finite_subdist_positions mu.

Lemma enumQ_lift_decode {A B} (mu : EnumQ A) (decode : A -> B) :
  @sem_lift EnumQ EnumQ_SemanticMeasure A B (fun x y => decode x = y) mu (emap decode mu).
Proof.
  apply (IndexedCoupling.indexed_coupling_raw
    (mu := emap id (enumQ_prune mu)) (nu := emap decode (enumQ_prune mu))).
  - exact: emap_id.
  - symmetry; exact: enumQ_prune_emap.
  - apply IndexedCoupling.indexed_coupling_emap with (S := eq).
    + move=> x y ->; reflexivity.
    + apply IndexedCoupling.indexed_coupling_refl=> x; reflexivity.
Qed.

Lemma subenumQ_positions_decode {A} (mu : SubEnumQ A) :
  sem_lift (fun i x => enumQ_position_value (subenumQ_raw mu) i = x)
    (subenumQ_positions mu) mu.
Proof.
  change (@sem_lift EnumQ EnumQ_SemanticMeasure _ _
    (fun i x => enumQ_position_value (subenumQ_raw mu) i = x)
    (enumQ_positions (subenumQ_raw mu)) (subenumQ_raw mu)).
  have H := enumQ_lift_decode (enumQ_positions (subenumQ_raw mu))
    (enumQ_position_value (subenumQ_raw mu)).
  eapply sem_lift_proper_r; last exact H.
  apply enumQ_repr_eq_implies_meas_eq; exact: enumQ_positions_decode.
Qed.

Lemma weighted_seq_expect {I A} (weights : I -> rat) (decode : I -> A) indices f :
  finite_expect f [seq (weights i,decode i) | i <- indices] =
  \sum_(i <- indices) weights i * f (decode i).
Proof. by elim: indices=> [|i indices IH]; rewrite ?big_nil ?big_cons /= ?IH. Qed.
Lemma finite_weighted_enumQ_expect {I : finType} {A} (weights : I -> rat)
    (Hnn : forall i, 0 <= weights i) (decode : I -> A) f :
  enumQ_expect f (finite_weighted_enumQ Hnn decode) = \sum_i weights i * f (decode i).
Proof.
  change (finite_expect f [seq (weights i,decode i) | i <- enum I] = \sum_i weights i * f (decode i)).
  by rewrite weighted_seq_expect big_enum.
Qed.
Lemma enumQ_expect_finite {A} (mu : EnumQ A) f :
  enumQ_expect f mu = finite_expect f (enumQ_raw mu).
Proof. reflexivity. Qed.
Lemma enumQ_atom_finite {A : eqType} (mu : EnumQ A) x :
  acc_mass x mu = finite_atom x (enumQ_raw mu).
Proof. reflexivity. Qed.
Lemma finite_enumQ_expect {X : finType} (mu : EnumQ X) f :
  enumQ_expect f mu = \sum_x acc_mass x mu * f x.
Proof. exact: finite_expect_by_atoms. Qed.
