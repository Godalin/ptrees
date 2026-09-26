(** The retained legacy factory uses raw EnumQ. Its use here is a genuine
    probability program, not arbitrary finite weights. No termination claim
    is needed for this node-validity invariant. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import WellFormedness Shallow.
From PTree.Prob.Backend.EnumQ Require Import Representation Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Examples.BernoulliFactory Require Import BernoulliFactory BernoulliFactoryProbability.
From PTree.Examples.FactoryController Require Import Controller.
Import EnumQ.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma embed_probability {E A} (t : ptree factoryE EnumQ A) :
  probabilistic_ptree t -> probabilistic_ptree (@embed E A t).
Proof.
  revert t. cofix CIH. intros t H.
  unfold probabilistic_ptree, embed in *.
  rewrite observe_interp. destruct H.
  - constructor.
  - constructor. apply CIH. assumption.
  - destruct e.
  - constructor; [assumption|]. intro x. apply CIH. apply H0.
Qed.

Lemma update_probability f : probabilistic_ptree (update f).
Proof.
  unfold update, State.get, State.put, PTree.trigger.
  apply probabilistic_ptree_bind.
  - apply probabilistic_ptree_vis. intro s. apply probabilistic_ptree_ret.
  - intro s. apply probabilistic_ptree_vis. intro u. apply probabilistic_ptree_ret.
Qed.

Lemma respond_probability j r : probabilistic_ptree (respond j r).
Proof.
  destruct r; cbn [respond]; apply probabilistic_ptree_bind;
    try apply update_probability; intro u.
  - apply probabilistic_ptree_bind.
    + apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
    + intro x. apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_bind.
    + apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
    + intro x. apply probabilistic_ptree_bind.
      * apply probabilistic_ptree_vis. intro y. apply probabilistic_ptree_ret.
      * intro y. apply probabilistic_ptree_ret.
Qed.

Theorem controller_probability sampler pc :
  probabilistic_ptree sampler -> probabilistic_ptree (controller sampler pc).
Proof.
  intro H. apply probabilistic_ptree_iter. intros [|j].
  - apply probabilistic_ptree_vis. intro x. apply probabilistic_ptree_ret.
  - apply probabilistic_ptree_bind; [exact H|].
    intro b. apply probabilistic_ptree_vis. intro r. apply respond_probability.
Qed.

Theorem implementation_probability : probabilistic_ptree controller_impl.
Proof.
  apply controller_probability, embed_probability.
  exact probabilistic_third_to_two_fifths.
Qed.

Theorem specification_probability : probabilistic_ptree controller_spec.
Proof. apply controller_probability, embed_probability, probabilistic_factory_direct_q. Qed.
