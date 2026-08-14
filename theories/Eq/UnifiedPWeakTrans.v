Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier UnifiedPWeak.

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

Section UnifiedWeakTrans.

Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{UC : @UnifiedFrontierCoherence E MN MF NI FI MX FO}.

Lemma sem_lift_comp_here {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : MF A) (nu : MF B) (xi : MF C) :
  sem_lift R mu nu -> sem_lift S nu xi ->
  sem_lift (fun x z => exists y, R x y /\ S y z) mu xi.
Proof.
  exact: (@sem_lift_comp MF FI FC A B C R S mu nu xi).
Qed.

Lemma node_sem_lift_comp_here {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : MN A) (nu : MN B) (xi : MN C) :
  sem_lift R mu nu -> sem_lift S nu xi ->
  sem_lift (fun x z => exists y, R x y /\ S y z) mu xi.
Proof.
  exact: (@sem_lift_comp MN NI NC A B C R S mu nu xi).
Qed.

Lemma weak_bisim_trans_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (t3 : ptree E MN R3) :
  weak_bisim RR1 t1 t2 ->
  weak_bisim RR2 t2 t3 ->
  weak_bisim (unified_relcomp RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3.
  unfold weak_bisim at 3.
  coinduction CH CIH.
  move=> t1 t2 t3 INL INR.
  move: (weak_bisim_unfold INL) => INL'.
  move: (weak_bisim_unfold INR) => INR'.
  clear INL INR.
  rename INL' into INL.
  rename INR' into INR.
  unfold funified_weak, weak_bisim_body; cbn.
  have FMCOMP :
      unified_frontier_match (unified_relcomp RR1 RR2)
        (elem CH)
        (observe t1) (observe t3).
  { eapply unified_frontier_match_comp
      with (ot2 := observe t2)
           (sim1 := weak_bisim RR1)
           (sim2 := weak_bisim RR2).
    - move=> u v w Huv Hvw.
      exact: CIH Huv Hvw.
    - exact: weak_bisimF_frontier_match INL.
    - exact: weak_bisimF_frontier_match INR. }
  genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2.
  - move: (proj1 FMCOMP _ H) => [hs3 [Hf3 Hc13]].
    eapply UWBFrontier; eassumption.
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
        -- apply weak_bisim_inv_tau.
           apply weak_bisim_fold. exact INR.
    + dependent destruction INR;
        try (exfalso; eapply Hnot; eauto; fail).
      * move: (proj2 H _ H1) => [hs0 [Hf1 Hc12]].
        move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
        eapply UWBFrontier; eassumption.
      * apply UWBTauL.
        remember (observe t3) as omid eqn:Hmid in INR.
        hinduction INR before CIH; intros; try discriminate.
        -- dependent destruction Hmid.
           have Htau : frontier (TauF t3) hs1.
           exact: UFTau H.
           move: (proj2 H2 _ Htau) => [hs0 [Hftau Hc12]].
           have Hfbase := @unified_frontier_tau_inv E MN MF NI FI MX FO UC _ t0 hs0 Hftau.
           eapply UWBFrontier; [exact Hfbase|exact H0|].
           have Hc := sem_lift_comp_here Hc12 H1.
           eapply (sem_lift_mono
             (R := fun h1 h3 => exists h2,
               frontier_head_rel RR1 (weak_bisim RR1) h1 h2 /\
               frontier_head_rel RR2 (weak_bisim RR2) h2 h3)
             (T := frontier_head_rel (unified_relcomp RR1 RR2)
               (elem CH))).
           ++ move=> h1 h3 [h2 [Hh12 Hh23]].
              eapply (frontier_head_rel_comp
                (sim1 := weak_bisim RR1)
                (sim2 := weak_bisim RR2)
                (sim3 := elem CH)).
              ** move=> u v w Huv Hvw.
                 exact: CIH Huv Hvw.
              ** exact Hh12.
              ** exact Hh23.
           ++ exact Hc.
        -- exfalso. eapply Hnot. reflexivity.
        -- move: (weak_bisim_unfold H2) => H2'.
           rewrite -Hmid in H2'.
           remember (ProbF mu k1) as omid2 eqn:Hmid2 in H2'.
           hinduction H2' before CIH; intros; try discriminate.
           ++ dependent destruction Hmid2.
              move: (proj1 H2 _ H0) => [hs3 [Hf3 Hc23]].
              eapply UWBFrontier; [exact H|exact Hf3|].
              have Hc := sem_lift_comp_here H1 Hc23.
              eapply (sem_lift_mono
                (R := fun h1 h3 => exists h2,
                  frontier_head_rel RR1 (weak_bisim RR1) h1 h2 /\
                  frontier_head_rel RR2 (weak_bisim RR2) h2 h3)
                (T := frontier_head_rel (unified_relcomp RR1 RR2)
                  (elem CH))).
              ** move=> h1 h3 [h2 [Hh12 Hh23]].
                 eapply (frontier_head_rel_comp
                   (sim1 := weak_bisim RR1)
                   (sim2 := weak_bisim RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact Hh12.
                 --- exact Hh23.
              ** exact Hc.
           ++ dependent destruction Hmid2.
              constructor.
              ** eapply (unified_frontier_match_comp
                   (sim1 := weak_bisim RR1)
                   (sim2 := weak_bisim RR2)
                   (sim3 := elem CH)).
                 --- move=> u v w Huv Hvw.
                     exact: CIH Huv Hvw.
                 --- exact H.
                 --- exact H1.
              ** have Hjoint := node_sem_lift_comp_here H0 H2.
                 eapply sem_lift_mono; [|exact Hjoint].
                 move=> x z [y [Hxy Hyz]].
                 exact: CIH Hxy Hyz.
           ++ apply UWBTauL.
              eapply IHH2'; eauto.
        -- have HPtau : weak_bisim RR1 t0 (Tau t1).
           { apply weak_bisim_fold. cbn. rewrite Hmid.
             exact (weak_bisim_unfold H0). }
           have HP : weak_bisim RR1 t0 t1.
             exact: weak_bisim_inv_tau_r HPtau.
           have FMbase :
               unified_frontier_match RR1 (weak_bisim RR1)
                 (observe t0) (observe t1).
           { exact: weak_bisimF_frontier_match (weak_bisim_unfold HP). }
           eapply (IHINR t0 t1).
           ++ exact: unified_frontier_match_tau FMbase.
           ++ exact HP.
           ++ reflexivity.
           ++ exact FMCOMP.
           ++ exact Hnot.
  - exfalso. eapply Hnot. reflexivity.
  - match type of INR with
    | weak_bisimF _ _ ?mid _ =>
        remember mid as omid eqn:Hmiddle
    end.
    hinduction INR before CIH; intros; try discriminate.
    + move: (proj2 H2 _ H) => [hs0 [Hf1 Hc12]].
      move: (proj1 FMCOMP _ Hf1) => [hs3 [Hf3 Hc13]].
      eapply UWBFrontier; eassumption.
    + dependent destruction Hmiddle.
      constructor.
      * exact FMCOMP.
      * have Hjoint := node_sem_lift_comp_here H2 H0.
        eapply (sem_lift_mono
          (R := fun x z => exists y,
            weak_bisim RR1 (k0 x) (k3 y) /\
            weak_bisim RR2 (k3 y) (k2 z))
          (T := fun x z =>
            elem CH (k0 x) (k2 z))).
        -- move=> x z [y [Hxy Hyz]].
           exact: CIH Hxy Hyz.
        -- exact Hjoint.
    + apply UWBTauR.
      eapply (IHINR X Y mu nu k1 k2).
      * exact Hmiddle.
      * exact H.
      * exact H0.
      * exact: unified_frontier_match_untau_r FMCOMP.
  - apply UWBTauL.
    eapply IHINL.
    + exact INR.
    + exact: unified_frontier_match_untau_l FMCOMP.
  - match type of INR with
    | weak_bisimF _ _ ?mid _ =>
        remember mid as omid eqn:Hmid
    end.
    hinduction INR before CIH; intros; try inversion Hmid; subst.
    all: try solve [eauto 5].
    have Hbase := @unified_frontier_tau_inv E MN MF NI FI MX FO UC _ _ _ H.
    eapply IHINL.
    - eapply UWBFrontier; [exact Hbase|exact H0|exact H1].
    - exact FMCOMP.
  - apply UWBTauR.
    eapply IHINL.
    + exact (weak_bisim_unfold H0).
    + exact: unified_frontier_match_untau_r FMCOMP.
  - apply UWBTauR.
    eapply IHINL.
    + exact: weak_bisimF_inv_tau_l_step INR.
    + exact: unified_frontier_match_untau_r FMCOMP.
Qed.

Lemma weak_bisim_trans {R : Type} :
  Transitive (@weak_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hp : weak_bisim (unified_relcomp eq eq) t1 t3.
  { exact: weak_bisim_trans_comp H12 H23. }
  eapply (weak_bisim_rel_mono (RR := unified_relcomp eq eq) (SS := eq)).
  - move=> x z [y [Hxy Hyz]].
    exact: eq_trans Hxy Hyz.
  - exact Hp.
Qed.

#[global] Instance weak_bisim_equivalence {R : Type} :
  Equivalence (@weak_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  split.
  - exact weak_bisim_refl.
  - exact weak_bisim_sym_eq.
  - exact weak_bisim_trans.
Qed.

End UnifiedWeakTrans.
