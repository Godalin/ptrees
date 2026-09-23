(** External validation: arbitrary-relation lifting is omega-closed for
    countably supported subprobabilities. No coherent family of joints is
    supplied or assumed; the limiting joint is obtained by transport. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling RelationalLimit.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CountableLimit.
Variable R : realType.

Theorem oval_coupled_lub_of_countable_limits {A B} (T : A -> B -> Prop)
    (c : nat -> OmegaVal R A) (d : nat -> OmegaVal R B)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  oval_countably_supported (oval_lub Hc) ->
  oval_countably_supported (oval_lub Hd) ->
  (forall n, oval_coupled T (c n) (d n)) ->
  oval_coupled T (oval_lub Hc) (oval_lub Hd).
Proof.
  intros Hleft Hright Hcoupled.
  apply (oval_bidual_coupled Hleft Hright).
  apply oval_bidual_lub=> n.
  destruct (Hcoupled n) as [joint Hj]; exact (oval_joint_dual Hj).
Qed.

Theorem oval_coupled_lub {A B} (T : A -> B -> Prop)
    (c : nat -> OmegaVal R A) (d : nat -> OmegaVal R B)
    (Hc : oval_increasing c) (Hd : oval_increasing d) :
  (forall n, oval_countably_supported (c n)) ->
  (forall n, oval_countably_supported (d n)) ->
  (forall n, oval_coupled T (c n) (d n)) ->
  oval_coupled T (oval_lub Hc) (oval_lub Hd).
Proof.
  intros Hleft Hright; apply oval_coupled_lub_of_countable_limits;
    apply oval_countably_supported_lub; assumption.
Qed.

(** Extensional endpoint witnesses: neither record equality nor a canonical
    representative of either limit is required. *)
Theorem oval_coupled_lub_witnesses {A B} (T : A -> B -> Prop)
    (c : nat -> OmegaVal R A) (d : nat -> OmegaVal R B)
    (Hc : oval_increasing c) (Hd : oval_increasing d) mu nu :
  (forall n, oval_countably_supported (c n)) ->
  (forall n, oval_countably_supported (d n)) ->
  (forall n, oval_coupled T (c n) (d n)) ->
  oval_eq (oval_lub Hc) mu -> oval_eq (oval_lub Hd) nu ->
  oval_coupled T mu nu.
Proof.
  intros Hleft Hright Hcoupled Hmu Hnu.
  destruct (oval_coupled_lub Hc Hd Hleft Hright Hcoupled) as [J [Hl [Hr Hae]]].
  exists J; split.
  - intros f Hf; rewrite (Hl f Hf); exact (Hmu f Hf).
  - split.
    + intros f Hf; rewrite (Hr f Hf); exact (Hnu f Hf).
    + exact Hae.
Qed.
End CountableLimit.
