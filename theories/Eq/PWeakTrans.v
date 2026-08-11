Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling.
From PTree.Eq Require Import PFrontier PWeak PWeakFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

Ltac genobs_clear x ox :=
  remember (observe x) as ox;
  first
    [ match goal with H : ox = observe x |- _ => clear H x end
    | match goal with H : observe x = ox |- _ => clear H x end ].

Ltac inv H := inversion H; subst; clear H.

Section PWeakTrans.

Context {E : Type -> Type}.

Lemma pweakF_inv_tau_l_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (ot2 : ptree' E Enum R2) :
  pweakF RR (pweak RR) (TauF t1) ot2 ->
  pweakF RR (pweak RR) (observe t1) ot2.
Proof.
  move=> Hstep.
  remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Elhs.
    dependent destruction H. eapply PWFrontier; eassumption.
  - injection Elhs as Et. subst t0.
    apply PWTauR. exact (pweak_unfold H0).
  - injection Elhs as Et. subst t0. exact Hstep.
  - apply PWTauR. eapply IHHstep; eauto.
Qed.

Lemma pweakF_inv_tau_r_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (ot1 : ptree' E Enum R1) (t2 : ptree E Enum R2) :
  pweakF RR (pweak RR) ot1 (TauF t2) ->
  pweakF RR (pweak RR) ot1 (observe t2).
Proof.
  move=> Hstep.
  remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Erhs.
    dependent destruction H0. eapply PWFrontier; eassumption.
  - injection Erhs as Et. subst t2.
    apply PWTauL. exact (pweak_unfold H0).
  - apply PWTauL. eapply IHHstep; eauto.
  - injection Erhs as Et. subst t2. exact Hstep.
Qed.

Lemma pweak_inv_tau_r {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweak RR t1 (Tau t2) -> pweak RR t1 t2.
Proof.
  revert t1 t2.
  unfold pweak at 2. coinduction CH CIH.
  move=> t1' t2' Hrel.
  unfold fpweak, pweak_body; cbn.
  eapply (pweakF_monotone
    (sim1 := pweak RR) (sim2 := elem CH)).
  - move=> u v Huv. apply (gfp_chain (b := fpweak RR) CH). exact Huv.
  - exact (pweakF_inv_tau_r_step (pweak_unfold Hrel)).
Qed.

Lemma pweak_inv_tau_l {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweak RR (Tau t1) t2 -> pweak RR t1 t2.
Proof.
  revert t1 t2.
  unfold pweak at 2. coinduction CH CIH.
  move=> t1' t2' Hrel.
  unfold fpweak, pweak_body; cbn.
  eapply (pweakF_monotone
    (sim1 := pweak RR) (sim2 := elem CH)).
  - move=> u v Huv. apply (gfp_chain (b := fpweak RR) CH). exact Huv.
  - exact (pweakF_inv_tau_l_step (pweak_unfold Hrel)).
Qed.

Lemma pweak_inv_tau {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweak RR (Tau t1) (Tau t2) -> pweak RR t1 t2.
Proof.
  move=> H. apply pweak_inv_tau_l in H.
  exact: pweak_inv_tau_r H.
Qed.

Lemma pweak_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2)
    (t3 : ptree E Enum R3) :
  pweak RR1 t1 t2 ->
  pweak RR2 t2 t3 ->
  pweak (prelcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  unfold pweak at 3.
  coinduction CH CIH.
  move=> t1 t2 t3 INL INR.
  move: (pweak_unfold INL) => INL'.
  move: (pweak_unfold INR) => INR'.
  clear INL INR.
  rename INL' into INL.
  rename INR' into INR.
  unfold fpweak, pweak_body; cbn.
  have FMCOMP :
      frontier_match (prelcomp RR1 RR2)
        (elem CH)
        (observe t1) (observe t3).
  { eapply frontier_match_comp
      with (ot2 := observe t2)
           (sim1 := pweak RR1)
           (sim2 := pweak RR2).
    - move=> u v w Huv Hvw.
      exact: CIH Huv Hvw.
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
      * eapply CIH.
        -- eassumption.
        -- apply pweak_inv_tau.
           apply pweak_fold. exact INR.
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
               phead_rel RR1 (pweak RR1) h1 h2 /\
               phead_rel RR2 (pweak RR2) h2 h3)
             (S := phead_rel (prelcomp RR1 RR2)
               (elem CH))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (phead_rel_comp
                (sim1 := pweak RR1)
                (sim2 := pweak RR2)
                (sim3 := elem CH)).
              ** move=> u v w Huv Hvw.
                 exact: CIH Huv Hvw.
              ** exact Hh12.
              ** exact Hh23.
           ++ exact Hc.
        -- exfalso. eapply Hnot. reflexivity.
        -- move: (pweak_unfold H2) => H2'.
           rewrite -Hmid in H2'.
           remember (ProbF mu k1) as omid2 eqn:Hmid2 in H2'.
           hinduction H2' before CIH; intros; try discriminate.
           ++ dependent destruction Hmid2.
              move: (proj1 H2 _ H0) => [hs3 [Hf3 Hc23]].
              eapply PWFrontier; [exact H|exact Hf3|].
              have Hc := indexed_coupling_comp H1 Hc23.
              eapply (indexed_coupling_mono
                (R := fun h1 h3 => exists h2,
                  phead_rel RR1 (pweak RR1) h1 h2 /\
                  phead_rel RR2 (pweak RR2) h2 h3)
                (S := phead_rel (prelcomp RR1 RR2)
                  (elem CH))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (phead_rel_comp
                   (sim1 := pweak RR1)
                   (sim2 := pweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (frontier_match_comp
                   (sim1 := pweak RR1)
                   (sim2 := pweak RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := coupling_comp H0 H2.
                 eapply coupling_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 exact: CIH Hxy Hyz.
           ++ apply PWTauL. eapply IHH2'; eauto.
        -- have HPtau : pweak RR1 t0 (Tau t1).
           { apply pweak_fold. cbn. rewrite Hmid.
             exact (pweak_unfold H0). }
           have HP : pweak RR1 t0 t1.
             exact: pweak_inv_tau_r HPtau.
           have FMbase :
               frontier_match RR1 (pweak RR1)
                 (observe t0) (observe t1).
           { exact: pweakF_frontier_match (pweak_unfold HP). }
           eapply (IHINR t0 t1).
           ++ exact: frontier_match_tau FMbase.
           ++ exact HP.
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
            pweak RR1 (k0 x) (k3 y) /\
            pweak RR2 (k3 y) (k2 z))
          (S := fun x z =>
            elem CH (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           exact: CIH Hxy Hyz.
        -- exact Hjoint.
    + apply PWTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: frontier_match_untau_r FMCOMP.
  - apply PWTauL.
    eapply IHINL.
    + exact INR.
    + exact: frontier_match_untau_l FMCOMP.
  - match type of INR with
    | @pweakF _ _ _ _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5].
    dependent destruction H.
    eapply IHINL.
    - eapply PWFrontier; eassumption.
    - exact FMCOMP.
  - apply PWTauR.
    eapply IHINL.
    + exact (pweak_unfold H0).
    + exact: frontier_match_untau_r FMCOMP.
  - apply PWTauR.
    eapply IHINL.
    + exact: pweakF_inv_tau_l_step INR.
    + exact: frontier_match_untau_r FMCOMP.
Qed.

Lemma pweak_trans {R : Type} :
  Transitive (@pweak E R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : pweak (prelcomp eq eq) t1 t3.
  { exact: pweak_trans_comp H12 H23. }
  eapply (pweak_rel_mono (RR := prelcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact Hp.
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
