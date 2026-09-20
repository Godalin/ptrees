(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finset bigop ssralg ssrnum order rat.
From PTree.Prob.Backend Require Import FiniteMatching FiniteCapacityMatching FiniteRationalTransport RatSubTypes TwoLevelMeasureSubEnum.
From PTree.Prob.Interface Require Import SemanticCoupling.
From PTree.Prob.Backend Require Import FiniteEnumTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.

Module FiniteTransportRegression.
Definition source (b : bool) : nat := if b then 2 else 1.
Definition target (b : bool) : nat := if b then 1 else 2.
Definition edge (x y : bool) : bool := x || ~~ y.

Lemma neighbors_true S :
  (true \in matching_neighbors edge setT S) = (true \in S).
Proof.
  apply/idP/idP.
  - move/matching_neighborsP=> [_ [[] [Hx He]]]; [exact Hx|discriminate].
  - intro Hx. apply/matching_neighborsP. split; [by rewrite inE|].
    exists true. by split.
Qed.

Lemma neighbors_false S :
  (false \in matching_neighbors edge setT S) = ((true \in S) || (false \in S)).
Proof.
  apply/idP/idP.
  - move/matching_neighborsP=> [_ [[] [Hx _]]]; apply/orP; [by left|by right].
  - move/orP=> [Hx|Hx]; apply/matching_neighborsP; split; try by rewrite inE.
    + exists true. by split.
    + exists false. by split.
Qed.

Lemma split_capacity_hall : capacity_hall source target edge.
Proof.
  intro S. rewrite big_mkcond big_bool.
  rewrite [X in _ <= X]big_mkcond big_bool neighbors_true neighbors_false.
  by case: (true \in S); case: (false \in S).
Qed.

(** The left true node MUST split its mass between two targets.  A
    deterministic map on the original two labels cannot implement this
    transport; the numbered-copy construction is genuinely used. *)
Theorem forced_split_integer_joint : exists w : bool -> bool -> nat,
  (forall x, \sum_y w x y = source x) /\
  (forall y, \sum_x w x y = target y) /\
  (forall x y, 0 < w x y -> edge x y) /\
  w true true = 1 /\ w true false = 1 /\
  w false true = 0 /\ w false false = 1.
Proof.
  have Htotal : \sum_x source x = \sum_y target y by rewrite !big_bool.
  destruct (finite_capacity_transport split_capacity_hall Htotal)
    as [w [Hr [Hc He]]].
  have Hz : w false true = 0.
  { case E: (w false true)=> [|n]; [reflexivity|].
    have Hp : 0 < w false true by rewrite E.
    have Hbad := He false true Hp. discriminate Hbad. }
  have Hrt := Hr true. have Hrf := Hr false. have Hct := Hc true.
  rewrite !big_bool /source /target Hz /= in Hrt Hrf Hct.
  rewrite -!plusE in Hrt Hrf Hct.
  exists w. repeat split; try assumption; lia.
Qed.

Local Open Scope ring_scope.
Definition source_probability (b : bool) : rat := if b then 2 / 3 else 1 / 3.
Definition target_probability (b : bool) : rat := if b then 1 / 3 else 2 / 3.

Lemma split_rational_hall : rational_hall source_probability target_probability edge.
Proof.
  intro S. rewrite big_mkcond big_bool.
  rewrite [X in _ <= X]big_mkcond big_bool neighbors_true neighbors_false.
  case: (true \in S); case: (false \in S); vm_compute; reflexivity.
Qed.

Theorem split_rational_joint : exists w : bool -> bool -> rat,
  (forall x y, 0 <= w x y) /\
  (forall x, \sum_y w x y = source_probability x) /\
  (forall y, \sum_x w x y = target_probability y) /\
  (forall x y, 0 < w x y -> edge x y).
Proof.
  apply finite_rational_transport.
  - intros []; vm_compute; reflexivity.
  - intros []; vm_compute; reflexivity.
  - exact split_rational_hall.
  - rewrite !big_bool. apply addrC.
Qed.

Definition source_weight (b : bool) : nnQ.
Proof. refine (mknnQ (source_probability b) _). destruct b; vm_compute; reflexivity. Defined.
Definition target_weight (b : bool) : nnQ.
Proof. refine (mknnQ (target_probability b) _). destruct b; vm_compute; reflexivity. Defined.

Definition source_measure : SubEnum bool.
Proof.
  refine {| subenum_raw := finite_weighted_enum source_weight id |}.
  rewrite /enum_subprob /enum_mass /finite_weighted_enum enumT unlock.
  vm_compute. reflexivity.
Defined.

Definition target_measure : SubEnum bool.
Proof.
  refine {| subenum_raw := finite_weighted_enum target_weight id |}.
  rewrite /enum_subprob /enum_mass /finite_weighted_enum enumT unlock.
  vm_compute. reflexivity.
Defined.

(** The same forced-splitting problem now yields an actual native joint,
    not only an external matrix certificate. *)
Theorem split_subenum_joint : exists joint : SubEnum (bool * bool),
  @semantic_coupling SubEnum SubEnum_SemanticMeasure bool bool
    (fun x y => edge x y) source_measure target_measure joint.
Proof.
  apply subenum_finite_transport_joint.
  - intro S. cbn [subenum_raw source_measure target_measure].
    rewrite !finite_weighted_enum_sum. exact (split_rational_hall S).
  - cbn [subenum_raw source_measure target_measure].
    rewrite !finite_weighted_enum_sum !big_bool. apply addrC.
Qed.

(** Having the same nonempty support on both sides is not a sufficient
    substitute for the quantitative Hall inequalities. *)
Theorem identity_edges_fail_hall : ~ rational_hall source_probability target_probability eq_op.
Proof.
  intro Hall. have H := Hall [set true].
  have Hneighbors : matching_neighbors (fun x y : bool => x == y) setT [set true] = [set true].
  { apply/setP=> y. apply/idP/idP.
    - move/matching_neighborsP=> [_ [x [Hx /eqP <-]]]. exact Hx.
    - intro Hy. apply/matching_neighborsP. split; [by rewrite inE|].
      exists y. split=> //; exact: eqxx. }
  rewrite Hneighbors !big_set1 in H. vm_compute in H. discriminate.
Qed.

(** No inhabitedness of either copy space is smuggled into the
    construction: an empty source and zero target mass are allowed. *)
Theorem zero_transport_empty_source : exists w : 'I_0 -> bool -> rat,
  (forall x y, 0 <= w x y) /\
  (forall x, \sum_y w x y = 0) /\
  (forall y, \sum_x w x y = 0) /\
  (forall x y, 0 < w x y -> false).
Proof.
  apply (@finite_rational_transport
    (@Finite.Pack 'I_0 (Finite.on 'I_0))
    (@Finite.Pack bool (Finite.on bool))
    (fun _ => 0) (fun _ => 0) (fun _ _ => false)).
  - intro x. exact: lexx.
  - intro y. exact: lexx.
  - intro S. by rewrite !big1 // lexx.
  - by rewrite !big1.
Qed.
End FiniteTransportRegression.
