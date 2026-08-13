Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import ClassicalEpsilon.
Require Import Program.Equality.

From Coinduction Require Import all.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded PStrong
  ProbabilisticPTS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The finite and AST relations observe different frontier domains.
    [aufrontier_finitely_generated t] is the exact conservativity condition
    under which every AST observation of [t] already has a finite witness,
    up to extensional measure equality. *)
Section FrontierConservativity.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC}
  `{MO : @MeasureOmegaInterface M MI}.

Definition aufrontier_finitely_generated {R}
    (ot : ptree' E M R) : Prop :=
  forall hs, aufrontier ot hs ->
    exists hs0, apfrontier ot hs0 /\ meas_eq hs0 hs.

Lemma aufrontier_finitely_generated_untau {R}
    (t : ptree E M R) :
  aufrontier_finitely_generated (TauF t) ->
  aufrontier_finitely_generated (observe t).
Proof.
  intros Hgen hs Hf.
  destruct (Hgen _ (AUFTau Hf)) as [hs0 [Hftau Heq]].
  exists hs0. split; [exact (apfrontier_tau_inv Hftau)|exact Heq].
Qed.

Lemma finite_match_to_ast_match {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) :
  aufrontier_finitely_generated ot1 ->
  aufrontier_finitely_generated ot2 ->
  apfrontier_match RR sim ot1 ot2 ->
  aufrontier_match RR sim ot1 ot2.
Proof.
  intros Hgen1 Hgen2 [HL HR]. split.
  - intros hs1 Huf1. destruct (Hgen1 _ Huf1) as [hf1 [Hf1 E1]].
    destruct (HL _ Hf1) as [hf2 [Hf2 Hlift]].
    exists hf2. split; [exact (AUFFinite Hf2)|].
    apply (meas_lift_proper_l
      (R := aphead_rel RR sim) (mu := hf1)).
    + exact E1.
    + exact Hlift.
  - intros hs2 Huf2. destruct (Hgen2 _ Huf2) as [hf2 [Hf2 E2]].
    destruct (HR _ Hf2) as [hf1 [Hf1 Hlift]].
    exists hf1. split; [exact (AUFFinite Hf1)|].
    apply (meas_lift_proper_r
      (R := aphead_rel RR sim) (nu := hf2)).
    + exact E2.
    + exact Hlift.
Qed.

End FrontierConservativity.

Section FiniteToASTInclusion.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

(** Relation-wide conservativity is needed because visible and guarded
    probabilistic continuations recursively enter new state pairs. *)
Theorem apweak_auweak_of_finite_generation {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (finite_generation : forall (t1 : ptree E M R1)
      (t2 : ptree E M R2),
      apweak RR t1 t2 ->
      aufrontier_finitely_generated (observe t1) /\
      aufrontier_finitely_generated (observe t2)) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    apweak RR t1 t2 -> auweak RR t1 t2.
Proof.
  unfold auweak. coinduction CH CIH. intros t1 t2 Hrel.
  unfold fauweak, auweak_body; cbn.
  pose proof (apweak_unfold Hrel) as Hstep.
  pose proof (finite_generation _ _ Hrel) as [Hgen1 Hgen2].
  induction Hstep.
  - eapply AUWFrontier.
    + exact (AUFFinite H).
    + exact (AUFFinite H0).
    + eapply meas_lift_mono; [|exact H1]. exact (aphead_rel_mono CIH).
  - apply AUWTau.
    + apply finite_match_to_ast_match.
      * exact Hgen1.
      * exact Hgen2.
      * eapply apfrontier_match_mono; [exact CIH|exact H].
    + exact (CIH _ _ H0).
  - apply AUWProb.
    + apply finite_match_to_ast_match; [exact Hgen1|exact Hgen2|].
      eapply apfrontier_match_mono; [exact CIH|exact H].
    + eapply meas_lift_mono; [|exact H0]. intros x y Hxy. exact (CIH _ _ Hxy).
  - apply AUWTauL. apply IHHstep.
    + exact (aufrontier_finitely_generated_untau Hgen1).
    + exact Hgen2.
  - apply AUWTauR. apply IHHstep.
    + exact Hgen1.
    + exact (aufrontier_finitely_generated_untau Hgen2).
Qed.

End FiniteToASTInclusion.

Section StrongToFiniteWeak.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MZ : MeasureZeroInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MAE : @MeasureLiftAELaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Lemma pstrongF_apfrontier_transport {R1 R2}
    (RR : R1 -> R2 -> Prop) :
  forall (ot1 : ptree' E M R1) hs1,
    apfrontier ot1 hs1 ->
    forall (ot2 : ptree' E M R2),
      pstrongF RR (pstrong RR) ot1 ot2 ->
      exists hs2, apfrontier ot2 hs2 /\
        meas_lift (aphead_rel RR (pstrong RR)) hs1 hs2.
Proof.
  intros ot1 hs1 Hf1. induction Hf1; intros ot2 Hstrong;
    dependent destruction Hstrong.
  - exists (meas_ret (APHRet r2)). split; first constructor.
    apply meas_lift_ret. constructor. assumption.
  - exists (meas_ret (APHVis e k2)). split; first constructor.
    apply meas_lift_ret. constructor. assumption.
  - destruct (IHHf1 _ (pstrong_unfold H)) as [hs2 [Hf2 Hlift]].
    exists hs2. split; [exact (APFTau Hf2)|exact Hlift].
  - pose (Good2 y := exists x,
      pstrong RR (k x) (k2 y) /\ Good x).
    assert (Hgood2 : meas_ae nu Good2).
    { unfold Good2. eapply meas_lift_ae_transport_r; eassumption. }
    assert (Hex : forall y, Good2 y -> exists hs,
        apfrontier (observe (k2 y)) hs /\
        exists x, pstrong RR (k x) (k2 y) /\ Good x /\
          meas_lift (aphead_rel RR (pstrong RR)) (front x) hs).
    { intros y [x [Hxy Hgx]].
      match goal with IH : forall x, Good x -> _ |- _ =>
        destruct (IH x Hgx _ (pstrong_unfold Hxy))
          as [hs [Hfs Hlift]] end.
      exists hs. split; [exact Hfs|].
      exists x. repeat split; assumption. }
    pose (front2 y :=
      match excluded_middle_informative (Good2 y) with
      | left Hy => proj1_sig (constructive_indefinite_description _ (Hex y Hy))
      | right _ => @meas_empty M MZ _
      end).
    exists (meas_bind nu front2). split.
    + apply (APFProb (front := front2) (Good := Good2)).
      * exact Hgood2.
      *
      intros y Hy. unfold front2.
      destruct excluded_middle_informative as [Hy'|Hn]; last contradiction.
      exact (proj1 (proj2_sig
        (constructive_indefinite_description _ (Hex y Hy')))).
    + eapply meas_lift_bind_ae
        with (R := fun x y => pstrong RR (k x) (k2 y))
             (P := Good) (Q := Good2).
      * exact H2.
      * exact H.
      * exact Hgood2.
      *
      intros x y Hxy Hgx Hgy. unfold front2.
      destruct excluded_middle_informative as [Hy|Hn]; last contradiction.
      destruct (proj2 (proj2_sig
        (constructive_indefinite_description _ (Hex y Hy))))
        as [z [Hzy [Hgz Hz]]].
      match goal with IH : forall x, Good x -> _ |- _ =>
        destruct (IH x Hgx _ (pstrong_unfold Hxy))
          as [hsx [Hfsx Hliftx]] end.
      assert (Heq : meas_eq hsx
          (proj1_sig (constructive_indefinite_description _ (Hex y Hy)))).
      { apply (apfrontier_sem_unique (ot := observe (k2 y))).
        - exists hsx. split; [exact Hfsx|apply meas_eq_refl].
        - exists (proj1_sig
            (constructive_indefinite_description _ (Hex y Hy))). split.
          + exact (proj1 (proj2_sig
              (constructive_indefinite_description _ (Hex y Hy)))).
          + apply meas_eq_refl. }
      eapply meas_lift_proper_r; [exact Heq|exact Hliftx].
Qed.

Lemma pstrong_apfrontier_transport {R1 R2}
    (RR : R1 -> R2 -> Prop) (t1 : ptree E M R1) (t2 : ptree E M R2) :
  pstrong RR t1 t2 ->
  forall hs1, apfrontier (observe t1) hs1 ->
  exists hs2, apfrontier (observe t2) hs2 /\
    meas_lift (aphead_rel RR (pstrong RR)) hs1 hs2.
Proof.
  intros Hstrong hs1 Hf1.
  exact (@pstrongF_apfrontier_transport R1 R2 RR
    (observe t1) hs1 Hf1 (observe t2) (pstrong_unfold Hstrong)).
Qed.

Theorem pstrong_frontier_match {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  pstrong RR t1 t2 ->
  apfrontier_match RR (pstrong RR) (observe t1) (observe t2).
Proof.
  intros Hstrong. split.
  - exact (pstrong_apfrontier_transport Hstrong).
  - intros hs2 Hf2.
    pose proof (pstrong_sym Hstrong) as Hsym.
    destruct (pstrong_apfrontier_transport Hsym Hf2)
      as [hs1 [Hf1 Hlift]].
    exists hs1. split; [exact Hf1|].
    eapply meas_lift_mono; [|exact (meas_lift_sym Hlift)].
    intros h1 h2 Hh. dependent destruction Hh.
    + constructor. exact H.
    + constructor. intro x. apply pstrong_sym. exact (H x).
Qed.

Theorem pstrong_apweak {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    pstrong RR t1 t2 -> apweak RR t1 t2.
Proof.
  unfold apweak. coinduction CH CIH. intros t1 t2 Hstrong.
  unfold fapweak, apweak_body; cbn.
  pose proof (pstrong_unfold Hstrong) as Hstep.
  inversion Hstep; subst.
  - apply APWFrontier with
        (hs1 := meas_ret (APHRet r1))
        (hs2 := meas_ret (APHRet r2)).
    + constructor.
    + constructor.
    + apply meas_lift_ret. constructor. assumption.
  - apply APWTau.
    + eapply apfrontier_match_mono; [exact CIH|].
      rewrite H. rewrite H0. exact (pstrong_frontier_match Hstrong).
    + exact (CIH _ _ H1).
  - apply APWFrontier with
        (hs1 := meas_ret (APHVis e k1))
        (hs2 := meas_ret (APHVis e k2)).
    + constructor.
    + constructor.
    + apply meas_lift_ret. constructor. intro x. exact (CIH _ _ (H1 x)).
  - apply APWProb.
    + eapply apfrontier_match_mono; [exact CIH|].
      rewrite H. rewrite H0. exact (pstrong_frontier_match Hstrong).
    + eapply meas_lift_mono; [|exact H1]. intros x y Hxy. exact (CIH _ _ Hxy).
Qed.

Corollary pstrong_auweak_of_finite_generation {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (finite_generation : forall (t1 : ptree E M R1)
      (t2 : ptree E M R2),
      apweak RR t1 t2 ->
      aufrontier_finitely_generated (observe t1) /\
      aufrontier_finitely_generated (observe t2)) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    pstrong RR t1 t2 -> auweak RR t1 t2.
Proof.
  intros t1 t2 Hstrong.
  apply (@apweak_auweak_of_finite_generation E M MI MC ML MO
    R1 R2 RR finite_generation t1 t2).
  exact (@pstrong_apweak R1 R2 RR t1 t2 Hstrong).
Qed.

End StrongToFiniteWeak.

(** The final behavioral endpoint is already characterized independently
    by the guarded distribution-valued PTS. *)
Section HierarchyEndpoint.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Corollary auweak_guarded_pts_endpoint {R1 R2}
    (RR : R1 -> R2 -> Prop) (t1 : ptree E M R1) (t2 : ptree E M R2) :
  auweak RR t1 t2 <-> ppts_guarded_bisim RR t1 t2.
Proof. symmetry. exact (ppts_guarded_iff_auweak RR t1 t2). Qed.

End HierarchyEndpoint.
