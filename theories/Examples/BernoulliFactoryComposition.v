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
  OperationalProbabilisticPTS OperationalProbabilisticPTSFreeOmega ProbabilisticEutt PStrong.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli
  BernoulliFactory OperationalBernoulliFactory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum EnumMap GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation MF := (FreeOmega Enum).
Local Notation peutt := (@probabilistic_eutt factoryE Enum MF
  (FreeOmegaObservableSemanticMeasure (NI := Enum_SemanticMeasure)
    (NO := Enum_SemanticOmega)) FreeOmegaObservableSemanticMeasureCoreLaws
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).
Local Notation weak := (@operational_weak factoryE Enum MF
  (FreeOmegaObservableSemanticMeasure (NI := Enum_SemanticMeasure)
    (NO := Enum_SemanticOmega)) FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).

(** No termination hypothesis: the closed loop respects sampler equivalence. *)
Theorem probabilistic_eutt_factory_sampler_congr
    (s1 s2 : ptree factoryE Enum bool) q :
  peutt eq s1 s2 ->
  peutt eq (factory_with_sampler s1 q) (factory_with_sampler s2 q).
Proof.
  intro Hsampler. unfold factory_with_sampler.
  eapply free_probabilistic_eutt_iter_behavioral_rel with (SI := eq).
  - exact factoryE_no_event.
  - intros x y ->. unfold factory_sampler_step.
    eapply probabilistic_eutt_rel_mono with (RR := eq).
    + intros u v ->. destruct v; reflexivity.
    + eapply free_probabilistic_eutt_bind with (RR := eq).
      * exact Hsampler.
      * intros a b ->. apply probabilistic_eutt_refl.
  - reflexivity.
Qed.

Definition factory_fair_heads : MF (frontier_head factoryE Enum bool) :=
  FOSample vn_fair (fun b => FORet (FHRet b)).

Lemma factory_direct_fair_weak :
  weak (observe factory_direct_fair) factory_fair_heads.
Proof.
  unfold factory_direct_fair, factory_fair_heads.
  change (weak (ProbF vn_fair (fun b => Ret b))
    (mixed_bind vn_fair (fun b => FORet (FHRet b)))).
  eapply operational_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. change (weak (RetF b) (FORet (FHRet b))).
    apply (operational_weak_ret
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (MX := FreeOmegaMixedMeasure) (E := factoryE)).
Qed.

Lemma factory_fair_heads_observes :
  free_omega_observes operational_factory_head_value factory_fair_heads vn_fair.
Proof.
  unfold factory_fair_heads.
  replace vn_fair with (bind_Enum vn_fair (fun b => ret_Enum b)) at 2
    by (rewrite bind_ret_emap emap_id; reflexivity).
  constructor. intro b. constructor.
Qed.

Section ParametricVN.
Variables pfalse ptrue : nnQ.
Hypothesis pnormalized : Qval pfalse + Qval ptrue = 1.
Hypothesis pnontrivial : 0 < Qval pfalse * Qval ptrue.

Lemma factory_vn_fair_support
    (sim : ptree factoryE Enum bool -> ptree factoryE Enum bool -> Prop) :
  free_omega_support_lift (frontier_head_rel eq sim)
    (operational_factory_raw_heads pfalse ptrue) factory_fair_heads.
Proof.
  assert (Hpfalse : pfalse <> nnQ_0).
  { intro Hzero. pose proof pnontrivial as Hpos. rewrite Hzero in Hpos.
    cbn [nnQ_0 Qval] in Hpos.
    rewrite mul0r ltxx in Hpos. discriminate. }
  assert (Hptrue : ptrue <> nnQ_0).
  { intro Hzero. pose proof pnontrivial as Hpos. rewrite Hzero in Hpos.
    cbn [nnQ_0 Qval] in Hpos.
    rewrite mulr0 ltxx in Hpos. discriminate. }
  unfold free_omega_support_lift. split.
    + intros P HP. unfold operational_factory_raw_heads in HP.
      dependent destruction HP. specialize (H 1%nat).
      cbn [operational_factory_raw_schedule] in H.
      rewrite operational_factory_raw_hitting_three in H.
      pose proof (free_omega_ae_sample_inv H) as Hfirst.
      assert (Hfirst_false : free_omega_ae P
          (FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
            match vn_round_result false b2 with
            | inl _ => operational_factory_raw_hitting pfalse ptrue 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := pfalse).
        - cbn. auto.
        - exact Hpfalse. }
      assert (Hfirst_true : free_omega_ae P
          (FOSample (factory_biased_coin pfalse ptrue) (fun b2 =>
            match vn_round_result true b2 with
            | inl _ => operational_factory_raw_hitting pfalse ptrue 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := ptrue).
        - cbn. auto.
        - exact Hptrue. }
      pose proof (free_omega_ae_sample_inv Hfirst_false) as Hsecond_false.
      pose proof (free_omega_ae_sample_inv Hfirst_true) as Hsecond_true.
      assert (HPfalse : P (FHRet false)).
      { specialize (Hsecond_false ptrue true). cbn in Hsecond_false.
        pose proof (Hsecond_false (or_intror (or_introl Logic.eq_refl))
          Hptrue) as Hr.
        dependent destruction Hr. exact H0. }
      assert (HPtrue : P (FHRet true)).
      { specialize (Hsecond_true pfalse false). cbn in Hsecond_true.
        pose proof (Hsecond_true (or_introl Logic.eq_refl)
          Hpfalse) as Hr.
        dependent destruction Hr. exact H0. }
      unfold factory_fair_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ. unfold factory_fair_heads in HQ.
      pose proof (free_omega_ae_sample_inv HQ) as Hfair.
      assert (HQfalse : Q (FHRet false)).
      { specialize (Hfair one_div_two false). cbn in Hfair.
        pose proof (Hfair (or_introl Logic.eq_refl)
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H. }
      assert (HQtrue : Q (FHRet true)).
      { specialize (Hfair one_div_two true). cbn in Hfair.
        pose proof (Hfair (or_intror (or_introl Logic.eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H. }
      apply free_omega_ae_mono with (P := fun _ => True).
      * intros h _. destruct h as [b|X e k]; [|destruct e].
        exists (FHRet b). split; [constructor; reflexivity|].
        destruct b; assumption.
      * generalize (operational_factory_raw_heads pfalse ptrue). intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true Enum Enum_SemanticMeasure
                Enum_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

Lemma factory_vn_fair_heads_lift
    (sim : ptree factoryE Enum bool -> ptree factoryE Enum bool -> Prop) :
  free_omega_qlift (frontier_head_rel eq sim)
    (operational_factory_raw_heads pfalse ptrue) factory_fair_heads.
Proof.
  eapply FOQLObserve with
    (obsA := operational_factory_head_value)
    (obsB := operational_factory_head_value)
    (outA := vn_fair) (outB := vn_fair) (S := eq).
  - exact (operational_factory_fair_heads_observes pnormalized pnontrivial).
  - exact factory_fair_heads_observes.
  - apply sem_lift_refl. intro b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1], h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - exact (factory_vn_fair_support sim).
Qed.

Theorem probabilistic_eutt_factory_vn_fair :
  peutt eq (factory_fair_coin pfalse ptrue) factory_direct_fair.
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - exact (operational_factory_fair_coin_weak pfalse ptrue).
  - exact factory_direct_fair_weak.
  - exact (factory_vn_fair_heads_lift _).
Qed.
End ParametricVN.

Definition factory_standard_step (x : rat) : ptree factoryE Enum (rat + bool) :=
  Prob (binary_coin_transition x) (fun next => Ret next).
Definition factory_standard (q : rat) : ptree factoryE Enum bool :=
  PTree.iter factory_standard_step q.

Lemma factory_fair_step_standard x :
  peutt eq (factory_sampler_step factory_direct_fair x) (factory_standard_step x).
Proof.
  unfold factory_sampler_step, factory_direct_fair, factory_standard_step.
  transitivity (Prob vn_fair (fun b => Ret (binary_round_result x b))
    : ptree factoryE Enum (rat + bool)).
  - apply free_probabilistic_eutt_of_pstructural.
    apply pstructural_fold. rewrite observe_bind. cbn.
    constructor. intro b. apply observe_eq_pstructural. reflexivity.
  - rewrite <- (fair_binary_round_measure x).
    transitivity (Prob vn_fair (fun b =>
        Prob (ret_Enum (binary_round_result x b)) (fun next => Ret next))
      : ptree factoryE Enum (rat + bool)).
    + eapply probabilistic_eutt_prob with (XR := eq).
      * apply sem_lift_refl. intro b. reflexivity.
      * intros a b ->. apply probabilistic_eutt_sym.
        exact (probabilistic_eutt_prob_ret (NI := Enum_SemanticMeasure)
          (FI := FreeOmegaObservableSemanticMeasure) (MX := FreeOmegaMixedMeasure)
          (binary_round_result x b) (fun next => (Ret next : ptree factoryE Enum (rat + bool)))).
    + apply (probabilistic_eutt_prob_flatten (NI := Enum_SemanticMeasure)
        (FI := FreeOmegaObservableSemanticMeasure) (MX := FreeOmegaMixedMeasure)).
Qed.

Lemma probabilistic_eutt_factory_fair_standard q :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_standard q).
Proof.
  unfold factory_with_sampler, factory_standard.
  eapply free_probabilistic_eutt_iter_behavioral_rel with (SI := eq).
  - exact factoryE_no_event.
  - intros x y ->. eapply probabilistic_eutt_rel_mono with (RR := eq).
    + intros u v ->. destruct v; reflexivity.
    + apply factory_fair_step_standard.
  - reflexivity.
Qed.

Lemma factory_standard_step_weak x :
  weak (observe (factory_standard_step x)) (operational_factory_standard_step_heads x).
Proof.
  unfold factory_standard_step, operational_factory_standard_step_heads.
  change (weak (ProbF (binary_coin_transition x) (fun next => Ret next))
    (mixed_bind (binary_coin_transition x) (fun next => FORet (FHRet next)))).
  eapply operational_weak_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros next _. apply operational_factory_binary_ret_weak.
Qed.

Lemma factory_standard_weak q :
  weak (observe (factory_standard q)) (operational_factory_standard_q_heads q).
Proof.
  unfold factory_standard.
  eapply free_operational_weak_iter_of_unbounded_steps
    with (step_out := operational_factory_standard_step_heads)
         (no_event := factoryE_no_event).
  - exact factory_standard_step_weak.
  - unfold operational_factory_standard_q_heads.
    apply FOQLLub. intro n.
    assert (Hrows : forall x,
      free_iter_complete_rows factoryE_no_event
        operational_factory_standard_step_heads n x =
      operational_factory_standard_q_row n x).
    { induction n as [|n IH]; intro x; [reflexivity|].
      cbn [free_iter_complete_rows operational_factory_standard_q_row].
      f_equal. }
    rewrite Hrows. apply free_omega_qlift_refl. intro h. reflexivity.
Qed.

Section RationalTarget.
Variable q : rat.
Hypotheses (q0 : 0 <= q) (q1 : q <= 1).
Context `{RationalSupport : OperationalFactoryRationalSupportLaws q}.

Theorem probabilistic_eutt_factory_standard_direct :
  peutt eq (factory_standard q) (factory_direct_q q0 q1).
Proof.
  eapply probabilistic_eutt_of_hitting_lift.
  - exact (factory_standard_weak q).
  - apply (proj2 (ptree_primitive_weak_adequate _ _)).
    exact (proj1 (operational_factory_direct_q_ast q0 q1)).
  - exact (operational_factory_standard_q_heads_lift_direct q0 q1 _).
Qed.

Theorem probabilistic_eutt_factory_fair_direct :
  peutt eq (factory_with_sampler factory_direct_fair q) (factory_direct_q q0 q1).
Proof.
  eapply probabilistic_eutt_trans.
  - exact (probabilistic_eutt_factory_fair_standard q).
  - exact probabilistic_eutt_factory_standard_direct.
Qed.

(** Any equivalent closed sampler can be installed without redoing the
    arithmetic/convergence proof of the binary algorithm. *)
Theorem probabilistic_eutt_factory_correct
    (sampler : ptree factoryE Enum bool)
    (Hsampler : peutt eq sampler factory_direct_fair) :
  peutt eq (factory_with_sampler sampler q) (factory_direct_q q0 q1).
Proof.
  eapply probabilistic_eutt_trans.
  - exact (probabilistic_eutt_factory_sampler_congr q Hsampler).
  - exact probabilistic_eutt_factory_fair_direct.
Qed.

(** Parametric source bias followed by an arbitrary rational target.
    Only the target support condition remains; no step-support axiom is used. *)
Theorem probabilistic_eutt_factory_vn_direct
    (pfalse ptrue : nnQ)
    (pnormalized : Qval pfalse + Qval ptrue = 1)
    (pnontrivial : 0 < Qval pfalse * Qval ptrue) :
  peutt eq (biased_to_rational_coin pfalse ptrue q) (factory_direct_q q0 q1).
Proof.
  change (peutt eq
    (factory_with_sampler (factory_fair_coin pfalse ptrue) q)
    (factory_direct_q q0 q1)).
  eapply probabilistic_eutt_trans.
  - apply probabilistic_eutt_factory_sampler_congr.
    exact (probabilistic_eutt_factory_vn_fair pnormalized pnontrivial).
  - exact probabilistic_eutt_factory_fair_direct.
Qed.
End RationalTarget.

Corollary probabilistic_eutt_third_to_two_fifths_compositional
    `{OperationalFactoryRationalSupportLaws (2 / 5)} :
  peutt eq third_to_two_fifths direct_two_fifths.
Proof.
  exact (probabilistic_eutt_factory_vn_direct
    two_fifths_nonnegative two_fifths_at_most_one
    third_bias_normalized third_bias_nontrivial).
Qed.

(** A behavioral regression: inserting an internal delay in the sampler
    preserves the whole loop, even though the sampler syntax changes. *)
Example factory_sampler_tau_regression q :
  peutt eq (factory_with_sampler (Tau factory_direct_fair) q)
    (factory_with_sampler factory_direct_fair q).
Proof.
  apply probabilistic_eutt_factory_sampler_congr.
  apply probabilistic_eutt_tau_l.
Qed.
