Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Paco Require Import paco.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling.
From PTree.Eq Require Import PFrontier PWeak PWeakFacts PWeakPaco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

Ltac genobs_clear x ox :=
  remember (observe x) as ox;
  match goal with H : ox = observe x |- _ => clear H x end.

Ltac inv H := inversion H; subst; clear H.

#[local] Hint Constructors pweakF prelcomp : paco.

Section PWeakTrans.

Context {E : Type -> Type}.

Lemma pweakP_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2)
    (t3 : ptree E Enum R3) :
  pweakP RR1 t1 t2 ->
  pweakP RR2 t2 t3 ->
  pweakP (prelcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  pcofix CIH.
  move=> t1 t2 t3 INL INR.
  pstep.
  unfold pweakP in INL, INR.
  punfold INL.
  punfold INR.
  red in INL, INR |- *.
  have FMCOMP :
      frontier_match (prelcomp RR1 RR2)
        (upaco2 (pweakP_ (prelcomp RR1 RR2)) r)
        (observe t1) (observe t3).
  { eapply frontier_match_comp
      with (ot2 := observe t2)
           (sim1 := upaco2 (pweakP_ RR1) bot2)
           (sim2 := upaco2 (pweakP_ RR2) bot2).
    - move=> u v w Huv Hvw.
      right.
      destruct Huv, Hvw; try contradiction;
        eauto with paco.
    - exact: pweakF_frontier_match INL.
    - exact: pweakF_frontier_match INR. }
  genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - move: (proj1 FMCOMP _ H) => [hs3 [Hf3 Hc13]].
    eapply PWFrontier; eassumption.
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
        -- eapply pweakP_inv_tau.
           unfold pweakP. pfold. exact INR.
    + dependent destruction INR;
        try (exfalso; eapply Hnot; eauto; fail).
      * move: (proj2 H _ H1) => [hs0 [Hf1 Hc12]].
        move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
        eapply PWFrontier; eassumption.
      * apply PWTauL.
        remember (observe t3) as omid eqn:Hmid in INR.
        hinduction INR before CIH; intros; try discriminate.
        -- dependent destruction Hmid.
           have Htau : pfrontier (TauF t3) hs1.
             exact: PFTau H.
           move: (proj2 H2 _ Htau) => [hs0 [Hftau Hc12]].
           dependent destruction Hftau.
           eapply PWFrontier; [eassumption|exact H0|].
           have Hc := indexed_coupling_comp Hc12 H1.
           eapply (indexed_coupling_mono
             (R := fun h1 h3 => exists h2,
               phead_rel RR1 (upaco2 (pweakP_ RR1) bot2) h1 h2 /\
               phead_rel RR2 (upaco2 (pweakP_ RR2) bot2) h2 h3)
             (S := phead_rel (prelcomp RR1 RR2)
               (upaco2 (pweakP_ (prelcomp RR1 RR2)) r))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (phead_rel_comp
                (sim1 := upaco2 (pweakP_ RR1) bot2)
                (sim2 := upaco2 (pweakP_ RR2) bot2)
                (sim3 := upaco2
                  (pweakP_ (prelcomp RR1 RR2)) r)).
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
              eapply PWFrontier; [exact H|exact Hf3|].
              have Hc := indexed_coupling_comp H1 Hc23.
              eapply (indexed_coupling_mono
                (R := fun h1 h3 => exists h2,
                  phead_rel RR1 (upaco2 (pweakP_ RR1) bot2) h1 h2 /\
                  phead_rel RR2 (upaco2 (pweakP_ RR2) bot2) h2 h3)
                (S := phead_rel (prelcomp RR1 RR2)
                  (upaco2 (pweakP_ (prelcomp RR1 RR2)) r))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (phead_rel_comp
                   (sim1 := upaco2 (pweakP_ RR1) bot2)
                   (sim2 := upaco2 (pweakP_ RR2) bot2)
                   (sim3 := upaco2
                     (pweakP_ (prelcomp RR1 RR2)) r)).
                 --- move=> u v w Huv Hvw.
                     right.
                     destruct Huv, Hvw; try contradiction;
                       eauto with paco.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (frontier_match_comp
                   (sim1 := upaco2 (pweakP_ RR1) bot2)
                   (sim2 := upaco2 (pweakP_ RR2) bot2)
                   (sim3 := upaco2
                     (pweakP_ (prelcomp RR1 RR2)) r)).
                 --- move=> u v w Huv Hvw.
                     right.
                     destruct Huv, Hvw; try contradiction;
                       eauto with paco.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := coupling_comp H0 H2.
                 eapply coupling_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 right.
                 destruct Hxy, Hyz; try contradiction;
                   eauto with paco.
           ++ eauto 6 with paco.
        -- pclearbot.
           have HPtau : pweakP RR1 t0 (Tau t1).
           { unfold pweakP in H0 |- *.
             punfold H0.
             pfold.
             red in H0 |- *.
             cbn.
             rewrite Hmid.
             exact H0. }
           have HP : pweakP RR1 t0 t1.
             exact: pweakP_inv_tau_r HPtau.
           have FMbase :
               frontier_match RR1 (upaco2 (pweakP_ RR1) bot2)
                 (observe t0) (observe t1).
           { unfold pweakP in HP.
             punfold HP.
             red in HP.
             exact: pweakF_frontier_match HP. }
           eapply (IHINR t0 t1).
           ++ exact: frontier_match_tau FMbase.
           ++ left. exact HP.
           ++ reflexivity.
           ++ exact FMCOMP.
           ++ exact Hnot.
  - exfalso. eapply Hnot. reflexivity.
  - match type of INR with
    | @pweakF _ _ _ _ _ ?mid _ =>
        remember mid as omid eqn:Hmiddle
    end.
    hinduction INR before CIH; intros; try discriminate.
    + move: (proj2 H2 _ H) => [hs0 [Hf1 Hc12]].
      move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
      eapply PWFrontier; eassumption.
    + dependent destruction Hmiddle.
      constructor.
      * exact FMCOMP.
      * have Hjoint := coupling_comp H2 H0.
        eapply (coupling_mono
          (R := fun x z => exists y,
            upaco2 (pweakP_ RR1) bot2 (k0 x) (k3 y) /\
            upaco2 (pweakP_ RR2) bot2 (k3 y) (k2 z))
          (S := fun x z =>
            upaco2 (pweakP_ (prelcomp RR1 RR2)) r
              (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           right.
           destruct Hxy, Hyz; try contradiction;
             eauto with paco.
        -- exact Hjoint.
    + apply PWTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: frontier_match_untau_r FMCOMP.
  - eauto with paco.
  - match type of INR with
    | @pweakF _ _ _ _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5 with paco].
    apply PWTauL.
    eapply IHINL.
    - eapply PWFrontier; eassumption.
    - exact: frontier_match_untau_l FMCOMP.
  - apply PWTauL.
    eapply IHINL.
    + constructor; [exact H | exact H0].
    + exact: frontier_match_untau_l FMCOMP.
  - apply PWTauL.
    eapply IHINL.
    + constructor; [exact H | exact H0].
    + exact: frontier_match_untau_l FMCOMP.
  - apply PWTauL.
    eapply IHINL.
    + apply PWTauL. exact INR.
    + exact: frontier_match_untau_l FMCOMP.
  - apply PWTauL.
    eapply IHINL.
    + apply PWTauR. exact INR.
    + exact: frontier_match_untau_l FMCOMP.
  - eapply IHINL.
    + exact: pweakF_inv_tau_l_step INR.
    + exact FMCOMP.
Qed.

Lemma pweak_trans {R : Type} :
  Transitive (@pweak E R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : pweakP (prelcomp eq eq) t1 t3.
  { eapply pweakP_trans_comp.
    - exact: pweak_to_pweakP H12.
    - exact: pweak_to_pweakP H23. }
  eapply (pweak_rel_mono (RR := prelcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact: pweakP_to_pweak Hp.
Qed.

Lemma pweak_sym_eq {R : Type} :
  Symmetric (@pweak E R R eq).
Proof.
  move=> t1 t2 H12.
  eapply (pweak_rel_mono
    (RR := fun y x : R => x = y) (SS := eq)).
  - move=> x y Hxy. symmetry. exact Hxy.
  - exact: pweak_sym H12.
Qed.

#[global] Instance pweak_equivalence {R : Type} :
  Equivalence (@pweak E R R eq).
Proof.
  split.
  - exact pweak_refl.
  - exact pweak_sym_eq.
  - exact pweak_trans.
Qed.

End PWeakTrans.
