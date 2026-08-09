Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Paco Require Import paco.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.
From PTree.Eq Require Import PWeakAbstract PWeakAbstractPaco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

Ltac genobs_clear x ox :=
  remember (observe x) as ox;
  match goal with H : ox = observe x |- _ => clear H x end.

Ltac inv H := inversion H; subst; clear H.

#[local] Hint Constructors apweakF aprelcomp : paco.

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

Lemma apweakP_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2)
    (t3 : ptree E M R3) :
  apweakP RR1 t1 t2 ->
  apweakP RR2 t2 t3 ->
  apweakP (aprelcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  pcofix CIH.
  move=> t1 t2 t3 INL INR.
  pstep.
  unfold apweakP in INL, INR.
  punfold INL.
  punfold INR.
  red in INL, INR |- *.
  have FMCOMP :
      apfrontier_match (aprelcomp RR1 RR2)
        (upaco2 (apweakP_ (aprelcomp RR1 RR2)) r)
        (observe t1) (observe t3).
  { eapply apfrontier_match_comp
      with (ot2 := observe t2)
           (sim1 := upaco2 (apweakP_ RR1) bot2)
           (sim2 := upaco2 (apweakP_ RR2) bot2).
    - move=> u v w Huv Hvw.
      right.
      destruct Huv, Hvw; try contradiction;
        eauto with paco.
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
      * right. pclearbot.
        eapply CIH.
        -- eassumption.
        -- eapply apweakP_inv_tau.
           unfold apweakP. pfold. exact INR.
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
               aphead_rel RR1 (upaco2 (apweakP_ RR1) bot2) h1 h2 /\
               aphead_rel RR2 (upaco2 (apweakP_ RR2) bot2) h2 h3)
             (S := aphead_rel (aprelcomp RR1 RR2)
               (upaco2 (apweakP_ (aprelcomp RR1 RR2)) r))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (aphead_rel_comp
                (sim1 := upaco2 (apweakP_ RR1) bot2)
                (sim2 := upaco2 (apweakP_ RR2) bot2)
                (sim3 := upaco2
                  (apweakP_ (aprelcomp RR1 RR2)) r)).
              ** move=> u v w Huv Hvw.
                 right.
                 destruct Huv, Hvw; try contradiction;
                   eauto with paco.
              ** exact Hh12.
              ** exact Hh23.
           ++ exact Hc.
        -- exfalso. eapply Hnot. reflexivity.
        -- pclearbot.
           punfold H2.
           red in H2.
           rewrite -Hmid in H2.
           remember (ProbF mu k1) as omid2 eqn:Hmid2 in H2.
           hinduction H2 before CIH; intros; try discriminate.
           ++ dependent destruction Hmid2.
              move: (proj1 H2 _ H0) => [hs3 [Hf3 Hc23]].
              eapply APWFrontier; [exact H|exact Hf3|].
              have Hc := meas_lift_comp_here H1 Hc23.
              eapply (meas_lift_mono
                (R := fun h1 h3 => exists h2,
                  aphead_rel RR1 (upaco2 (apweakP_ RR1) bot2) h1 h2 /\
                  aphead_rel RR2 (upaco2 (apweakP_ RR2) bot2) h2 h3)
                (S := aphead_rel (aprelcomp RR1 RR2)
                  (upaco2 (apweakP_ (aprelcomp RR1 RR2)) r))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (aphead_rel_comp
                   (sim1 := upaco2 (apweakP_ RR1) bot2)
                   (sim2 := upaco2 (apweakP_ RR2) bot2)
                   (sim3 := upaco2
                     (apweakP_ (aprelcomp RR1 RR2)) r)).
                 --- move=> u v w Huv Hvw.
                     right.
                     destruct Huv, Hvw; try contradiction;
                       eauto with paco.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (apfrontier_match_comp
                   (sim1 := upaco2 (apweakP_ RR1) bot2)
                   (sim2 := upaco2 (apweakP_ RR2) bot2)
                   (sim3 := upaco2
                     (apweakP_ (aprelcomp RR1 RR2)) r)).
                 --- move=> u v w Huv Hvw.
                     right.
                     destruct Huv, Hvw; try contradiction;
                       eauto with paco.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := meas_lift_comp_here H0 H2.
                 eapply meas_lift_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 right.
                 destruct Hxy, Hyz; try contradiction;
                   eauto with paco.
           ++ eauto 6 with paco.
        -- pclearbot.
           have HPtau : apweakP RR1 t0 (Tau t1).
           { unfold apweakP in H0 |- *.
             punfold H0.
             pfold.
             red in H0 |- *.
             cbn.
             rewrite Hmid.
             exact H0. }
           have HP : apweakP RR1 t0 t1.
             exact: apweakP_inv_tau_r HPtau.
           have FMbase :
               apfrontier_match RR1 (upaco2 (apweakP_ RR1) bot2)
                 (observe t0) (observe t1).
           { unfold apweakP in HP.
             punfold HP.
             red in HP.
             exact: apweakF_frontier_match HP. }
           eapply (IHINR t0 t1).
           ++ exact: apfrontier_match_tau FMbase.
           ++ left. exact HP.
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
            upaco2 (apweakP_ RR1) bot2 (k0 x) (k3 y) /\
            upaco2 (apweakP_ RR2) bot2 (k3 y) (k2 z))
          (S := fun x z =>
            upaco2 (apweakP_ (aprelcomp RR1 RR2)) r
              (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           right.
           destruct Hxy, Hyz; try contradiction;
             eauto with paco.
        -- exact Hjoint.
    + apply APWTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: apfrontier_match_untau_r FMCOMP.
  - eauto with paco.
  - match type of INR with
    | apweakF _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5 with paco].
    apply APWTauL.
    eapply IHINL.
    - eapply APWFrontier; eassumption.
    - exact: apfrontier_match_untau_l FMCOMP.
  - apply APWTauL.
    eapply IHINL.
    + constructor; [exact H | exact H0].
    + exact: apfrontier_match_untau_l FMCOMP.
  - apply APWTauL.
    eapply IHINL.
    + constructor; [exact H | exact H0].
    + exact: apfrontier_match_untau_l FMCOMP.
  - apply APWTauL.
    eapply IHINL.
    + apply APWTauL. exact INR.
    + exact: apfrontier_match_untau_l FMCOMP.
  - apply APWTauL.
    eapply IHINL.
    + apply APWTauR. exact INR.
    + exact: apfrontier_match_untau_l FMCOMP.
  - eapply IHINL.
    + exact: apweakF_inv_tau_l_step INR.
    + exact FMCOMP.
Qed.

Lemma apweak_trans {R : Type} :
  Transitive (@apweak E M MI MC R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : apweakP (aprelcomp eq eq) t1 t3.
  { eapply apweakP_trans_comp.
    - exact: apweak_to_apweakP H12.
    - exact: apweak_to_apweakP H23. }
  eapply (apweak_rel_mono (RR := aprelcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact: apweakP_to_apweak Hp.
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
