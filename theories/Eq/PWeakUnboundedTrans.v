Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

Ltac genobs_clear x ox :=
  remember (observe x) as ox;
  first
    [ match goal with H : ox = observe x |- _ => clear H x end
    | match goal with H : observe x = ox |- _ => clear H x end ].

Ltac inv H := inversion H; subst; clear H.

Section AUWeakUnboundedTrans.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}.
Context `{ML : @MeasureLaws M MI MC}.
Context `{MO : @MeasureOmegaInterface M MI}.
Context `{UC : @UnboundedFrontierCoherence E M MI MO}.

Lemma meas_lift_comp_here {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : M A) (nu : M B) (xi : M C) :
  meas_lift R mu nu -> meas_lift S nu xi ->
  meas_lift (fun x z => exists y, R x y /\ S y z) mu xi.
Proof.
  exact: (@meas_lift_comp M MI MC ML A B C R S mu nu xi).
Qed.

Lemma auweak_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2)
    (t3 : ptree E M R3) :
  auweak RR1 t1 t2 ->
  auweak RR2 t2 t3 ->
  auweak (aurelcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  unfold auweak at 3.
  coinduction CH CIH.
  move=> t1 t2 t3 INL INR.
  move: (auweak_unfold INL) => INL'.
  move: (auweak_unfold INR) => INR'.
  clear INL INR.
  rename INL' into INL.
  rename INR' into INR.
  unfold fauweak, auweak_body; cbn.
  have FMCOMP :
      aufrontier_match (aurelcomp RR1 RR2)
        (elem CH)
        (observe t1) (observe t3).
  { eapply aufrontier_match_comp
      with (ot2 := observe t2)
           (sim1 := auweak RR1)
           (sim2 := auweak RR2).
    - move=> u v w Huv Hvw.
      exact: CIH Huv Hvw.
    - exact: auweakF_frontier_match INL.
    - exact: auweakF_frontier_match INR. }
  genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - move: (proj1 FMCOMP _ H) => [hs3 [Hf3 Hc13]].
    eapply AUWFrontier; eassumption.
  - have DEC :
      (exists m3, ot3 = TauF m3) \/
      (forall m3, ot3 <> TauF m3).
    { destruct ot3.
      - right. move=> m3 Hbad. discriminate.
      - left. eexists. reflexivity.
      - right. move=> m3 Hbad. discriminate.
      - right. move=> m3 Hbad. discriminate. }
    destruct DEC as [[m3 Hm3] | Hnot].
    + subst ot3.
      constructor.
      * exact FMCOMP.
      * eapply CIH.
        -- eassumption.
        -- apply auweak_inv_tau.
           apply auweak_fold. exact INR.
    + dependent destruction INR;
        try (exfalso; eapply Hnot; eauto; fail).
      * move: (proj2 H _ H1) => [hs0 [Hf1 Hc12]].
        move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
        eapply AUWFrontier; eassumption.
      * apply AUWTauL.
        remember (observe t3) as omid eqn:Hmid in INR.
        hinduction INR before CIH; intros; try discriminate.
        -- dependent destruction Hmid.
           have Htau : aufrontier (TauF t3) hs1.
           exact: AUFTau H.
           move: (proj2 H2 _ Htau) => [hs0 [Hftau Hc12]].
           have Hfbase := @aufrontier_tau_inv E M MI MO UC _ t0 hs0 Hftau.
           eapply AUWFrontier; [exact Hfbase|exact H0|].
           have Hc := meas_lift_comp_here Hc12 H1.
           eapply (meas_lift_mono
             (R := fun h1 h3 => exists h2,
               aphead_rel RR1 (auweak RR1) h1 h2 /\
               aphead_rel RR2 (auweak RR2) h2 h3)
             (S := aphead_rel (aurelcomp RR1 RR2)
               (elem CH))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (auhead_rel_comp
                (sim1 := auweak RR1)
                (sim2 := auweak RR2)
                (sim3 := elem CH)).
              ** move=> u v w Huv Hvw.
                 exact: CIH Huv Hvw.
              ** exact Hh12.
              ** exact Hh23.
           ++ exact Hc.
        -- exfalso. eapply Hnot. reflexivity.
        -- move: (auweak_unfold H2) => H2'.
           rewrite -Hmid in H2'.
           remember (ProbF mu k1) as omid2 eqn:Hmid2 in H2'.
           hinduction H2' before CIH; intros; try discriminate.
           ++ dependent destruction Hmid2.
              move: (proj1 H2 _ H0) => [hs3 [Hf3 Hc23]].
              eapply AUWFrontier; [exact H|exact Hf3|].
              have Hc := meas_lift_comp_here H1 Hc23.
              eapply (meas_lift_mono
                (R := fun h1 h3 => exists h2,
                  aphead_rel RR1 (auweak RR1) h1 h2 /\
                  aphead_rel RR2 (auweak RR2) h2 h3)
                (S := aphead_rel (aurelcomp RR1 RR2)
                  (elem CH))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (auhead_rel_comp
                   (sim1 := auweak RR1)
                   (sim2 := auweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (aufrontier_match_comp
                   (sim1 := auweak RR1)
                   (sim2 := auweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := meas_lift_comp_here H0 H2.
                 eapply meas_lift_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 exact: CIH Hxy Hyz.
           ++ apply AUWTauL.
              eapply IHH2'; eauto.
        -- have HPtau : auweak RR1 t0 (Tau t1).
           { apply auweak_fold. cbn. rewrite Hmid.
             exact (auweak_unfold H0). }
           have HP : auweak RR1 t0 t1.
             exact: auweak_inv_tau_r HPtau.
           have FMbase :
               aufrontier_match RR1 (auweak RR1)
                 (observe t0) (observe t1).
           { exact: auweakF_frontier_match (auweak_unfold HP). }
           eapply (IHINR t0 t1).
           ++ exact: aufrontier_match_tau FMbase.
           ++ exact HP.
           ++ reflexivity.
           ++ exact FMCOMP.
           ++ exact Hnot.
  - exfalso. eapply Hnot. reflexivity.
  - match type of INR with
    | auweakF _ _ ?mid _ =>
        remember mid as omid eqn:Hmiddle
    end.
    hinduction INR before CIH; intros; try discriminate.
    + move: (proj2 H2 _ H) => [hs0 [Hf1 Hc12]].
      move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
      eapply AUWFrontier; eassumption.
    + dependent destruction Hmiddle.
      constructor.
      * exact FMCOMP.
      * have Hjoint := meas_lift_comp_here H2 H0.
        eapply (meas_lift_mono
          (R := fun x z => exists y,
            auweak RR1 (k0 x) (k3 y) /\
            auweak RR2 (k3 y) (k2 z))
          (S := fun x z =>
            elem CH (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           exact: CIH Hxy Hyz.
        -- exact Hjoint.
    + apply AUWTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: aufrontier_match_untau_r FMCOMP.
  - apply AUWTauL.
    eapply IHINL.
    + exact INR.
    + exact: aufrontier_match_untau_l FMCOMP.
  - match type of INR with
    | auweakF _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5].
    have Hbase := @aufrontier_tau_inv E M MI MO UC _ _ _ H.
    eapply IHINL.
    - eapply AUWFrontier; [exact Hbase|exact H0|exact H1].
    - exact FMCOMP.
  - apply AUWTauR.
    eapply IHINL.
    + exact (auweak_unfold H0).
    + exact: aufrontier_match_untau_r FMCOMP.
  - apply AUWTauR.
    eapply IHINL.
    + exact: auweakF_inv_tau_l_step INR.
    + exact: aufrontier_match_untau_r FMCOMP.
Qed.

Lemma auweak_trans {R : Type} :
  Transitive (@auweak E M MI MC MO R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : auweak (aurelcomp eq eq) t1 t3.
  { exact: auweak_trans_comp H12 H23. }
  eapply (auweak_rel_mono (RR := aurelcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact Hp.
Qed.

#[global] Instance auweak_equivalence {R : Type} :
  Equivalence (@auweak E M MI MC MO R R eq).
Proof.
  split.
  - exact auweak_refl.
  - exact auweak_sym_eq.
  - exact auweak_trans.
Qed.

End AUWeakUnboundedTrans.
