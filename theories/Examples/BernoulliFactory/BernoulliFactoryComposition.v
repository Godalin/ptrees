(** Case role: paper case study / shared algebra.
    Reading entry: peutt_factory_vn_direct.
    Scope: EnumQ / observable FreeOmega; two unbounded analyses are consumed as behavior equations.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Algebraic composition of independently verified Factory components. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import FunctionalExtensionality Morphisms.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Map.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Interp.FreeOmega Require Import Rewriting.
From PTree.Eq Require Import PEutt PStruct PStrong.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded RationalBernoulli BernoulliFactory OperationalBernoulliFactory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Import FreeOmegaRewriting.
Local Notation MF := (FreeOmega EnumQ).
Local Notation peutt := (@peutt factoryE EnumQ MF
  (FreeOmegaObservableSemanticMeasure (NI := EnumQ_SemanticMeasure)
    (NO := EnumQ_SemanticOmega)) FreeOmegaObservableSemanticMeasureCoreLaws
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).

(** No termination hypothesis: the closed loop respects sampler equivalence. *)
Theorem peutt_factory_sampler_congr
    (s1 s2 : ptree factoryE EnumQ bool) q :
  peutt eq s1 s2 ->
  peutt eq (factory_with_sampler s1 q) (factory_with_sampler s2 q).
Proof.
  intro Hsampler. unfold factory_with_sampler, factory_sampler_step.
  setoid_rewrite Hsampler. reflexivity.
Qed.

(** This context is specific to the factory, not to generic iteration. *)
#[export] Instance factory_with_sampler_Proper :
  Proper (peutt eq ==> eq ==> peutt eq) (@factory_with_sampler factoryE).
Proof. intros t u H q q' ->. apply peutt_factory_sampler_congr. exact H. Qed.

Lemma factory_fair_step_standard x :
  peutt eq (factory_sampler_step factory_direct_fair x) (factory_standard_step x).
Proof.
  unfold factory_sampler_step, factory_direct_fair.
  setoid_rewrite (peutt_sample_bind (MF := MF) vn_fair).
  setoid_rewrite (peutt_sample_map (MF := MF) vn_fair).
  (* The representation-specific calculation is confined to this local
     analysis endpoint; clients rewrite the program equation above. *)
  change (peutt eq
    (Prob (bind_EnumQ vn_fair (fun b => ret_EnumQ (binary_round_result x b)))
      (fun a => Ret a)) (factory_standard_step x)).
  unfold factory_standard_step. rewrite fair_binary_round_measure. reflexivity.
Qed.

Lemma peutt_factory_fair_standard q :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_standard q).
Proof.
  unfold factory_with_sampler, factory_standard.
  setoid_rewrite (factory_fair_step_standard : pointwise_relation _ (peutt eq) _ _).
  reflexivity.
Qed.

Section RationalTarget.
Variable q : rat.
Hypotheses (q0 : 0 <= q) (q1 : q <= 1).

Theorem peutt_factory_fair_direct :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_direct_q q0 q1).
Proof.
  setoid_rewrite peutt_factory_fair_standard.
  setoid_rewrite (peutt_factory_standard_direct q0 q1). reflexivity.
Qed.

(** Any equivalent closed sampler can be installed without redoing the
    arithmetic/convergence proof of the binary algorithm. *)
Theorem peutt_factory_correct
    (sampler : ptree factoryE EnumQ bool)
    (Hsampler : peutt eq sampler factory_direct_fair) :
  peutt eq (factory_with_sampler sampler q) (factory_direct_q q0 q1).
Proof.
  setoid_rewrite Hsampler. exact peutt_factory_fair_direct.
Qed.

(** Parametric source bias followed by an arbitrary rational target.
    Both component support obligations are proved; no example-specific law is used. *)
Theorem peutt_factory_vn_direct
    (pfalse ptrue : rat)
    (pfalse0 : 0 <= pfalse) (ptrue0 : 0 <= ptrue)
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : 0 < pfalse * ptrue) :
  peutt eq (biased_to_rational_coin pfalse0 ptrue0 q) (factory_direct_q q0 q1).
Proof.
  unfold biased_to_rational_coin.
  setoid_rewrite (peutt_factory_vn_fair pfalse0 ptrue0 pnormalized pnontrivial).
  setoid_rewrite peutt_factory_fair_standard.
  setoid_rewrite (peutt_factory_standard_direct q0 q1). reflexivity.
Qed.
End RationalTarget.

Corollary peutt_third_to_two_fifths_compositional :
  peutt eq third_to_two_fifths direct_two_fifths.
Proof.
  exact (peutt_factory_vn_direct
    two_fifths_nonnegative two_fifths_at_most_one
    third_false_nonnegative third_true_nonnegative
    third_bias_normalized third_bias_nontrivial).
Qed.

(** A behavioral regression: inserting an internal delay in the sampler
    preserves the whole loop, even though the sampler syntax changes. *)
Example factory_sampler_tau_regression q :
  peutt eq (factory_with_sampler (Tau factory_direct_fair) q)
    (factory_with_sampler factory_direct_fair q).
Proof.
  apply peutt_factory_sampler_congr.
  apply peutt_tau_l.
Qed.
