(** The executable raw-Enum implementation inhabits the probabilistic
    fragment.  Normalization is needed for the source measure; termination
    and nondegeneracy are not needed for this syntax-level contract. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition PTreeProbability.
From PTree.Prob Require Import RatSubTypes DiscreteMC MeasureIterationEnum
  TwoLevelMeasureEnum TwoLevelMeasureSubEnum.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli BernoulliFactory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Enum GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Lemma probabilistic_factory_sampler_step {E : Type -> Type}
    (sampler : ptree E Enum bool) x :
  probabilistic_ptree sampler ->
  probabilistic_ptree (factory_sampler_step sampler x).
Proof.
  intro Hsampler. unfold factory_sampler_step.
  apply probabilistic_ptree_bind; [exact Hsampler|].
  intro b. apply probabilistic_ptree_ret.
Qed.

Theorem probabilistic_factory_with_sampler {E : Type -> Type}
    (sampler : ptree E Enum bool) q :
  probabilistic_ptree sampler ->
  probabilistic_ptree (factory_with_sampler sampler q).
Proof.
  intro Hsampler. unfold factory_with_sampler.
  apply probabilistic_ptree_iter. intro x.
  apply probabilistic_factory_sampler_step. exact Hsampler.
Qed.

Lemma factory_biased_coin_subprob pfalse ptrue :
  Qval pfalse + Qval ptrue = 1 ->
  enum_subprob (factory_biased_coin pfalse ptrue).
Proof.
  intro Hsum. unfold enum_subprob, enum_mass, factory_biased_coin.
  change (Qval pfalse * 1 + (Qval ptrue * 1 + 0) <= 1).
  by rewrite !mulr1 addr0 Hsum.
Qed.

Theorem probabilistic_factory_fair_coin pfalse ptrue :
  Qval pfalse + Qval ptrue = 1 ->
  probabilistic_ptree (factory_fair_coin pfalse ptrue).
Proof.
  intro Hsum. unfold factory_fair_coin.
  apply probabilistic_ptree_iter. intro u. unfold factory_vn_step.
  apply probabilistic_ptree_prob; [apply factory_biased_coin_subprob; exact Hsum|].
  intro b1.
  apply probabilistic_ptree_prob; [apply factory_biased_coin_subprob; exact Hsum|].
  intro b2. apply probabilistic_ptree_ret.
Qed.

Theorem probabilistic_biased_to_rational_coin pfalse ptrue q :
  Qval pfalse + Qval ptrue = 1 ->
  probabilistic_ptree (biased_to_rational_coin pfalse ptrue q).
Proof.
  intro Hsum. unfold biased_to_rational_coin.
  apply probabilistic_factory_with_sampler.
  apply probabilistic_factory_fair_coin. exact Hsum.
Qed.

Lemma probabilistic_factory_direct_fair :
  probabilistic_ptree factory_direct_fair.
Proof.
  unfold factory_direct_fair. apply probabilistic_ptree_prob.
  - change (enum_subprob vn_fair).
    unfold enum_subprob, enum_mass, vn_fair.
    change ((1 / 2 : rat) * 1 + (1 / 2 * 1 + 0) <= 1). by [].
  - intro b. apply probabilistic_ptree_ret.
Qed.

Lemma probabilistic_factory_direct_q q (q0 : 0 <= q) (q1 : q <= 1) :
  probabilistic_ptree (factory_direct_q q0 q1).
Proof.
  unfold factory_direct_q. apply probabilistic_ptree_prob.
  - change (enum_subprob (rational_bernoulli_measure q0 q1)).
    unfold enum_subprob, enum_mass. by rewrite rational_bernoulli_total.
  - intro b. apply probabilistic_ptree_ret.
Qed.

Example probabilistic_third_to_two_fifths :
  probabilistic_ptree third_to_two_fifths.
Proof. apply probabilistic_biased_to_rational_coin. exact third_bias_normalized. Qed.
