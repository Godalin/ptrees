(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple bigop ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Iteration.
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
Definition enumQ_position {A} (mu : EnumQ A) := finite_position mu.
Definition enumQ_position_entry {A} (mu : EnumQ A) (i : enumQ_position mu) :=
  finite_position_entry mu i.
Arguments enumQ_position_entry {A} mu i.
Definition enumQ_position_weight {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_weight mu i.
Definition enumQ_position_value {A} (mu : EnumQ A) (i : enumQ_position mu) := finite_position_value mu i.
Arguments enumQ_position_weight {A} mu i.
Arguments enumQ_position_value {A} mu i.
Definition enumQ_positions {A} (mu : EnumQ A) : EnumQ (enumQ_position mu) :=
  finite_positions mu.

Lemma enumQ_positions_decode {A} (mu : EnumQ A) :
  emap (enumQ_position_value mu) (enumQ_positions mu) = mu.
Proof. exact: finite_positions_decode. Qed.

Lemma enumQ_positions_subprob {A} (mu : SubEnumQ A) :
  enumQ_subprob (enumQ_positions (subenumQ_raw mu)).
Proof.
  unfold enumQ_subprob, enumQ_mass.
  rewrite -(enumQ_expect_one_emap (enumQ_position_value (subenumQ_raw mu)))
    enumQ_positions_decode. exact (subenumQ_bound mu).
Qed.

Definition subenumQ_positions {A} (mu : SubEnumQ A) : SubEnumQ (enumQ_position (subenumQ_raw mu)) :=
  {| subenumQ_raw := enumQ_positions (subenumQ_raw mu);
     subenumQ_bound := enumQ_positions_subprob mu |}.

Lemma enumQ_lift_decode {A B} (mu : EnumQ A) (decode : A -> B) :
  @sem_lift EnumQ EnumQ_SemanticMeasure A B (fun x y => decode x = y) mu (emap decode mu).
Proof.
  change (IndexedCoupling.indexed_coupling (fun x y => decode x = y)
    (enumQ_prune mu) (enumQ_prune (emap decode mu))).
  rewrite enumQ_prune_emap.
  rewrite -{1}(emap_id (enumQ_prune mu)).
  apply IndexedCoupling.indexed_coupling_emap with (S := eq).
  - intros x y ->. reflexivity.
  - apply IndexedCoupling.indexed_coupling_refl. intro x. reflexivity.
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
  rewrite enumQ_positions_decode in H. exact H.
Qed.

Lemma weighted_seq_expect {I A} (weights : I -> nnQ) (decode : I -> A) indices f :
  enumQ_expect f [seq (weights i, decode i) | i <- indices] =
  \sum_(i <- indices) Qval (weights i) * f (decode i).
Proof. by elim: indices=> [|i indices IH]; rewrite ?big_nil ?big_cons /= ?IH. Qed.

Lemma finite_weighted_enumQ_expect {I : finType} {A}
    (weights : I -> nnQ) (decode : I -> A) f :
  enumQ_expect f (finite_weighted_enumQ weights decode) =
  \sum_i Qval (weights i) * f (decode i).
Proof. by rewrite /finite_weighted_enumQ weighted_seq_expect big_enum. Qed.

(** The atom-sum form needed by finite transportation is independent of
    the list representation, including repeated atoms. *)
Lemma enumQ_expect_finite {A} (mu : EnumQ A) f :
  enumQ_expect f mu =
  finite_expect f (List.map (fun px => (Qval px.1, px.2)) mu).
Proof. by elim: mu=> [|[p x] tl IH] //=; rewrite IH. Qed.

Lemma enumQ_atom_finite {A : eqType} (mu : EnumQ A) x :
  Qval (acc_mass x mu) =
  finite_atom x (List.map (fun px => (Qval px.1, px.2)) mu).
Proof.
  elim: mu=> [|[p a] tl IH]; first reflexivity.
  rewrite acc_mass_cons /= finite_atom_cons.
  case: (a == x).
  - change (Qval (acc_mass x tl) + Qval p = Qval p +
      finite_atom x (List.map (fun px => (Qval px.1, px.2)) tl)).
    by rewrite IH addrC.
  - change (Qval (acc_mass x tl) + 0 = 0 +
      finite_atom x (List.map (fun px => (Qval px.1, px.2)) tl)).
    by rewrite IH addr0 add0r.
Qed.

Lemma finite_enumQ_expect {X : finType} (mu : EnumQ X) f :
  enumQ_expect f mu = \sum_x Qval (acc_mass x mu) * f x.
Proof.
  rewrite enumQ_expect_finite finite_expect_by_atoms.
  apply eq_bigr=> x _; by rewrite enumQ_atom_finite.
Qed.
