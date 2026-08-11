Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.
From PTree.Eq Require Import PWeakAbstract.

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

Section APWeakAbstractTrans.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}.
Context `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}.

Lemma meas_lift_comp_here {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : M A) (nu : M B) (xi : M C) :
  meas_lift R mu nu -> meas_lift S nu xi ->
  meas_lift (fun x z => exists y, R x y /\ S y z) mu xi.
Proof.
  exact: (@meas_lift_comp M MI MC ML A B C R S mu nu xi).
Qed.

Lemma apweakF_inv_tau_l_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (ot2 : ptree' E M R2) :
  apweakF RR (apweak RR) (TauF t1) ot2 ->
  apweakF RR (apweak RR) (observe t1) ot2.
Proof.
  move=> Hstep.
  remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Elhs.
    dependent destruction H. eapply APWFrontier; eassumption.
  - injection Elhs as Et. subst t0.
    apply APWTauR. exact (apweak_unfold H0).
  - injection Elhs as Et. subst t0. exact Hstep.
  - apply APWTauR. eapply IHHstep; eauto.
Qed.

Lemma apweakF_inv_tau_r_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (ot1 : ptree' E M R1) (t2 : ptree E M R2) :
  apweakF RR (apweak RR) ot1 (TauF t2) ->
  apweakF RR (apweak RR) ot1 (observe t2).
Proof.
  move=> Hstep.
  remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Erhs.
    dependent destruction H0. eapply APWFrontier; eassumption.
  - injection Erhs as Et. subst t2.
    apply APWTauL. exact (apweak_unfold H0).
  - apply APWTauL. eapply IHHstep; eauto.
  - injection Erhs as Et. subst t2. exact Hstep.
Qed.

Lemma apweak_inv_tau_r {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweak RR t1 (Tau t2) -> apweak RR t1 t2.
Proof.
  revert t1 t2.
  unfold apweak at 2. coinduction CH CIH.
  move=> t1' t2' Hrel.
  unfold fapweak, apweak_body; cbn.
  eapply (apweakF_monotone
    (sim1 := apweak RR) (sim2 := elem CH)).
  - move=> u v Huv. apply (gfp_chain (b := fapweak RR) CH). exact Huv.
  - exact (apweakF_inv_tau_r_step (apweak_unfold Hrel)).
Qed.

Lemma apweak_inv_tau_l {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweak RR (Tau t1) t2 -> apweak RR t1 t2.
Proof.
  revert t1 t2.
  unfold apweak at 2. coinduction CH CIH.
  move=> t1' t2' Hrel.
  unfold fapweak, apweak_body; cbn.
  eapply (apweakF_monotone
    (sim1 := apweak RR) (sim2 := elem CH)).
  - move=> u v Huv. apply (gfp_chain (b := fapweak RR) CH). exact Huv.
  - exact (apweakF_inv_tau_l_step (apweak_unfold Hrel)).
Qed.

Lemma apweak_inv_tau {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweak RR (Tau t1) (Tau t2) -> apweak RR t1 t2.
Proof.
  move=> H. apply apweak_inv_tau_l in H.
  exact: apweak_inv_tau_r H.
Qed.

Lemma apweak_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2)
    (t3 : ptree E M R3) :
  apweak RR1 t1 t2 ->
  apweak RR2 t2 t3 ->
  apweak (aprelcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  unfold apweak at 3.
  coinduction CH CIH.
  move=> t1 t2 t3 INL INR.
  move: (apweak_unfold INL) => INL'.
  move: (apweak_unfold INR) => INR'.
  clear INL INR.
  rename INL' into INL.
  rename INR' into INR.
  unfold fapweak, apweak_body; cbn.
  have FMCOMP :
      apfrontier_match (aprelcomp RR1 RR2)
        (elem CH)
        (observe t1) (observe t3).
  { eapply apfrontier_match_comp
      with (ot2 := observe t2)
           (sim1 := apweak RR1)
           (sim2 := apweak RR2).
    - move=> u v w Huv Hvw.
      exact: CIH Huv Hvw.
    - exact: apweakF_frontier_match INL.
    - exact: apweakF_frontier_match INR. }
  genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - move: (proj1 FMCOMP _ H) => [hs3 [Hf3 Hc13]].
    eapply APWFrontier; eassumption.
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
        -- apply apweak_inv_tau.
           apply apweak_fold. exact INR.
    + dependent destruction INR;
        try (exfalso; eapply Hnot; eauto; fail).
      * move: (proj2 H _ H1) => [hs0 [Hf1 Hc12]].
        move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
        eapply APWFrontier; eassumption.
      * apply APWTauL.
        remember (observe t3) as omid eqn:Hmid in INR.
        hinduction INR before CIH; intros; try discriminate.
        -- dependent destruction Hmid.
           have Htau : apfrontier (TauF t3) hs1.
             exact: APFTau H.
           move: (proj2 H2 _ Htau) => [hs0 [Hftau Hc12]].
           dependent destruction Hftau.
           eapply APWFrontier; [eassumption|exact H0|].
           have Hc := meas_lift_comp_here Hc12 H1.
           eapply (meas_lift_mono
             (R := fun h1 h3 => exists h2,
               aphead_rel RR1 (apweak RR1) h1 h2 /\
               aphead_rel RR2 (apweak RR2) h2 h3)
             (S := aphead_rel (aprelcomp RR1 RR2)
               (elem CH))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (aphead_rel_comp
                (sim1 := apweak RR1)
                (sim2 := apweak RR2)
                (sim3 := elem CH)).
              ** move=> u v w Huv Hvw.
                 exact: CIH Huv Hvw.
              ** exact Hh12.
              ** exact Hh23.
           ++ exact Hc.
        -- exfalso. eapply Hnot. reflexivity.
        -- move: (apweak_unfold H2) => H2'.
           rewrite -Hmid in H2'.
           remember (ProbF mu k1) as omid2 eqn:Hmid2 in H2'.
           hinduction H2' before CIH; intros; try discriminate.
           ++ dependent destruction Hmid2.
              move: (proj1 H2 _ H0) => [hs3 [Hf3 Hc23]].
              eapply APWFrontier; [exact H|exact Hf3|].
              have Hc := meas_lift_comp_here H1 Hc23.
              eapply (meas_lift_mono
                (R := fun h1 h3 => exists h2,
                  aphead_rel RR1 (apweak RR1) h1 h2 /\
                  aphead_rel RR2 (apweak RR2) h2 h3)
                (S := aphead_rel (aprelcomp RR1 RR2)
                  (elem CH))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (aphead_rel_comp
                   (sim1 := apweak RR1)
                   (sim2 := apweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (apfrontier_match_comp
                   (sim1 := apweak RR1)
                   (sim2 := apweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := meas_lift_comp_here H0 H2.
                 eapply meas_lift_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 exact: CIH Hxy Hyz.
           ++ apply APWTauL.
              eapply IHH2'; eauto.
        -- have HPtau : apweak RR1 t0 (Tau t1).
           { apply apweak_fold. cbn. rewrite Hmid.
             exact (apweak_unfold H0). }
           have HP : apweak RR1 t0 t1.
             exact: apweak_inv_tau_r HPtau.
           have FMbase :
               apfrontier_match RR1 (apweak RR1)
                 (observe t0) (observe t1).
           { exact: apweakF_frontier_match (apweak_unfold HP). }
           eapply (IHINR t0 t1).
           ++ exact: apfrontier_match_tau FMbase.
           ++ exact HP.
           ++ reflexivity.
           ++ exact FMCOMP.
           ++ exact Hnot.
  - exfalso. eapply Hnot. reflexivity.
  - match type of INR with
    | apweakF _ _ ?mid _ =>
        remember mid as omid eqn:Hmiddle
    end.
    hinduction INR before CIH; intros; try discriminate.
    + move: (proj2 H2 _ H) => [hs0 [Hf1 Hc12]].
      move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
      eapply APWFrontier; eassumption.
    + dependent destruction Hmiddle.
      constructor.
      * exact FMCOMP.
      * have Hjoint := meas_lift_comp_here H2 H0.
        eapply (meas_lift_mono
          (R := fun x z => exists y,
            apweak RR1 (k0 x) (k3 y) /\
            apweak RR2 (k3 y) (k2 z))
          (S := fun x z =>
            elem CH (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           exact: CIH Hxy Hyz.
        -- exact Hjoint.
    + apply APWTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: apfrontier_match_untau_r FMCOMP.
  - apply APWTauL.
    eapply IHINL.
    + exact INR.
    + exact: apfrontier_match_untau_l FMCOMP.
  - match type of INR with
    | apweakF _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5].
    dependent destruction H.
    eapply IHINL.
    - eapply APWFrontier; eassumption.
    - exact FMCOMP.
  - apply APWTauR.
    eapply IHINL.
    + exact (apweak_unfold H0).
    + exact: apfrontier_match_untau_r FMCOMP.
  - apply APWTauR.
    eapply IHINL.
    + exact: apweakF_inv_tau_l_step INR.
    + exact: apfrontier_match_untau_r FMCOMP.
Qed.

Lemma apweak_trans {R : Type} :
  Transitive (@apweak E M MI MC R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : apweak (aprelcomp eq eq) t1 t3.
  { exact: apweak_trans_comp H12 H23. }
  eapply (apweak_rel_mono (RR := aprelcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact Hp.
Qed.

Lemma apweak_sym_eq {R : Type} :
  Symmetric (@apweak E M MI MC R R eq).
Proof.
  move=> t1 t2 H12.
  eapply (apweak_rel_mono
    (RR := fun y x : R => x = y) (SS := eq)).
  - move=> x y Hxy. symmetry. exact Hxy.
  - exact: apweak_sym H12.
Qed.

#[global] Instance apweak_equivalence {R : Type} :
  Equivalence (@apweak E M MI MC R R eq).
Proof.
  split.
  - exact apweak_refl.
  - exact apweak_sym_eq.
  - exact apweak_trans.
Qed.

End APWeakAbstractTrans.
