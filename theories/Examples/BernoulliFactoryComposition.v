(** Algebraic composition of independently verified Factory components. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
From Coq Require Import FunctionalExtensionality Program.Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts
  MeasureIteration MeasureIterationEnum TwoLevelMeasure TwoLevelMeasureEnum
  FreeOmegaMeasure EnumMap.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting
  OperationalProbabilisticPTS OperationalProbabilisticPTSFreeOmega PEutt PStrong.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli
  BernoulliFactory OperationalBernoulliFactory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation MF := (FreeOmega Enum).
Local Notation peutt := (@peutt factoryE Enum MF
  (FreeOmegaObservableSemanticMeasure (NI := Enum_SemanticMeasure)
    (NO := Enum_SemanticOmega)) FreeOmegaObservableSemanticMeasureCoreLaws
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).

(** No termination hypothesis: the closed loop respects sampler equivalence. *)
Theorem peutt_factory_sampler_congr
    (s1 s2 : ptree factoryE Enum bool) q :
  peutt eq s1 s2 ->
  peutt eq (factory_with_sampler s1 q) (factory_with_sampler s2 q).
Proof.
  intro Hsampler. unfold factory_with_sampler.
  eapply free_peutt_iter_behavioral_rel with (SI := eq).
  - exact factoryE_no_event.
  - intros x y ->. unfold factory_sampler_step.
    eapply peutt_rel_mono with (RR := eq).
    + intros u v ->. destruct v; reflexivity.
    + eapply free_peutt_bind with (RR := eq).
      * exact Hsampler.
      * intros a b ->. apply peutt_refl.
  - reflexivity.
Qed.

Lemma factory_fair_step_standard x :
  peutt eq (factory_sampler_step factory_direct_fair x) (factory_standard_step x).
Proof.
  unfold factory_sampler_step, factory_direct_fair, factory_standard_step.
  transitivity (Prob vn_fair (fun b => Ret (binary_round_result x b))
    : ptree factoryE Enum (rat + bool)).
  - apply free_peutt_of_pstruct.
    apply pstruct_fold. rewrite observe_bind. cbn.
    constructor. intro b. apply observe_eq_pstruct. reflexivity.
  - rewrite <- (fair_binary_round_measure x).
    transitivity (Prob vn_fair (fun b =>
        Prob (ret_Enum (binary_round_result x b)) (fun next => Ret next))
      : ptree factoryE Enum (rat + bool)).
    + eapply peutt_prob with (XR := eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros a b ->. apply peutt_sym.
        exact (peutt_prob_ret (NI := Enum_SemanticMeasure)
          (FI := FreeOmegaObservableSemanticMeasure) (MX := FreeOmegaMixedMeasure)
          (binary_round_result x b) (fun next => (Ret next : ptree factoryE Enum (rat + bool)))).
    + apply (peutt_prob_flatten (NI := Enum_SemanticMeasure)
        (FI := FreeOmegaObservableSemanticMeasure) (MX := FreeOmegaMixedMeasure)).
Qed.

Lemma peutt_factory_fair_standard q :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_standard q).
Proof.
  unfold factory_with_sampler, factory_standard.
  eapply free_peutt_iter_behavioral_rel with (SI := eq).
  - exact factoryE_no_event.
  - intros x y ->. eapply peutt_rel_mono with (RR := eq).
    + intros u v ->. destruct v; reflexivity.
    + apply factory_fair_step_standard.
  - reflexivity.
Qed.

Section RationalTarget.
Variable q : rat.
Hypotheses (q0 : 0 <= q) (q1 : q <= 1).

Theorem peutt_factory_fair_direct :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_direct_q q0 q1).
Proof.
  eapply peutt_trans.
  - exact (peutt_factory_fair_standard q).
  - exact (peutt_factory_standard_direct q0 q1).
Qed.

(** Any equivalent closed sampler can be installed without redoing the
    arithmetic/convergence proof of the binary algorithm. *)
Theorem peutt_factory_correct
    (sampler : ptree factoryE Enum bool)
    (Hsampler : peutt eq sampler factory_direct_fair) :
  peutt eq (factory_with_sampler sampler q) (factory_direct_q q0 q1).
Proof.
  eapply peutt_trans.
  - exact (peutt_factory_sampler_congr q Hsampler).
  - exact peutt_factory_fair_direct.
Qed.

(** Parametric source bias followed by an arbitrary rational target.
    Both component support obligations are proved; no example-specific law is used. *)
Theorem peutt_factory_vn_direct
    (pfalse ptrue : nnQ)
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : 0 < Qval pfalse * Qval ptrue) :
  peutt eq (biased_to_rational_coin pfalse ptrue q) (factory_direct_q q0 q1).
Proof.
  change (peutt eq
    (factory_with_sampler (factory_fair_coin pfalse ptrue) q)
    (factory_direct_q q0 q1)).
  eapply peutt_trans.
  - apply peutt_factory_sampler_congr.
    exact (peutt_factory_vn_fair pnormalized pnontrivial).
  - exact peutt_factory_fair_direct.
Qed.
End RationalTarget.

Corollary peutt_third_to_two_fifths_compositional :
  peutt eq third_to_two_fifths direct_two_fifths.
Proof.
  exact (peutt_factory_vn_direct
    two_fifths_nonnegative two_fifths_at_most_one
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
