Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From Paco Require Import paco.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling.
From PTree.Eq Require Import PFrontier PWeak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

Ltac genobs_clear x ox :=
  remember (observe x) as ox;
  match goal with H : ox = observe x |- _ => clear H x end.

Ltac inv H := inversion H; subst; clear H.

#[local] Hint Constructors pweakF : paco.

Section PWeakPaco.

Context {E : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition pweakP_
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) : Prop :=
  pweakF RR sim (observe t1) (observe t2).

Lemma pweakP_monotone : monotone2 pweakP_.
Proof.
  move=> t1 t2 sim1 sim2 Hstep Hsub.
  eapply pweakF_monotone; [exact Hsub|exact Hstep].
Qed.

#[local] Hint Resolve pweakP_monotone : paco.

Definition pweakP : ptree E Enum R1 -> ptree E Enum R2 -> Prop :=
  paco2 pweakP_ bot2.

Lemma pweak_to_pweakP :
  forall t1 t2, pweak RR t1 t2 -> pweakP t1 t2.
Proof.
  pcofix CIH.
  move=> t1 t2 Hrel.
  pstep.
  move: (pweak_unfold Hrel) => Hstep.
  red.
  eapply pweakF_monotone.
  - move=> u v Huv. right. exact: CIH Huv.
  - exact Hstep.
Qed.

Lemma pweakP_to_pweak :
  forall t1 t2, pweakP t1 t2 -> pweak RR t1 t2.
Proof.
  unfold pweak.
  coinduction CH CIH.
  move=> t1 t2 Hrel.
  unfold pweakP in Hrel.
  punfold Hrel.
  red in Hrel.
  cbn in Hrel.
  change (pweakF RR (elem CH) (observe t1) (observe t2)).
  eapply (pweakF_monotone
    (sim1 := upaco2 pweakP_ bot2)
    (sim2 := elem CH)).
  - move=> u v Huv.
    pclearbot.
    apply CIH. exact Huv.
  - exact Hrel.
Qed.

Lemma pweak_iff_pweakP t1 t2 :
  pweak RR t1 t2 <-> pweakP t1 t2.
Proof.
  split.
  - exact: pweak_to_pweakP.
  - exact: pweakP_to_pweak.
Qed.

Lemma pweakP_inv_tau_r
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweakP t1 (Tau t2) -> pweakP t1 t2.
Proof.
  move=> Hrel.
  unfold pweakP in Hrel |- *.
  pstep. red.
  punfold Hrel.
  red in Hrel.
  cbn in Hrel.
  remember (TauF t2) as rhs eqn:Erhs in Hrel.
  dependent induction Hrel; try discriminate.
  - dependent destruction H0.
    eapply PWFrontier; eassumption.
  - pclearbot.
    rewrite -x.
    apply PWTauL.
    pstep_reverse.
  - rewrite -x.
    apply PWTauL.
    eapply IHHrel; eauto.
  - assumption.
Qed.

Lemma pweakP_inv_tau_l
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweakP (Tau t1) t2 -> pweakP t1 t2.
Proof.
  move=> Hrel.
  unfold pweakP in Hrel |- *.
  pstep. red.
  punfold Hrel.
  red in Hrel.
  cbn in Hrel.
  remember (TauF t1) as lhs eqn:Elhs in Hrel.
  dependent induction Hrel; try discriminate.
  - dependent destruction H.
    eapply PWFrontier; eassumption.
  - pclearbot.
    rewrite -x.
    apply PWTauR.
    pstep_reverse.
  - assumption.
  - rewrite -x.
    apply PWTauR.
    eapply IHHrel; eauto.
Qed.

Lemma pweakP_inv_tau
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweakP (Tau t1) (Tau t2) -> pweakP t1 t2.
Proof.
  move=> H.
  apply pweakP_inv_tau_l in H.
  exact: pweakP_inv_tau_r H.
Qed.

Lemma pweakF_inv_tau_l_step
    (t1 : ptree E Enum R1) (ot2 : ptree' E Enum R2) :
  pweakF RR (upaco2 pweakP_ bot2) (TauF t1) ot2 ->
  pweakF RR (upaco2 pweakP_ bot2) (observe t1) ot2.
Proof.
  move=> Hstep.
  remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - match goal with
    | Heq : _ = TauF _ |- _ => dependent destruction Heq
    | Heq : TauF _ = _ |- _ => dependent destruction Heq
    end.
    apply pfrontier_tau_inv in H.
    eapply PWFrontier; eassumption.
  - injection Elhs as Et.
    subst t0.
    pclearbot.
    apply PWTauR.
    have Hu := paco2_unfold pweakP_monotone H0.
    exact Hu.
  - injection Elhs as Et.
    subst t0.
    assumption.
  - apply PWTauR.
    eapply IHHstep; eauto.
Qed.

Lemma pweakF_inv_tau_r_step
    (ot1 : ptree' E Enum R1) (t2 : ptree E Enum R2) :
  pweakF RR (upaco2 pweakP_ bot2) ot1 (TauF t2) ->
  pweakF RR (upaco2 pweakP_ bot2) ot1 (observe t2).
Proof.
  move=> Hstep.
  remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - match goal with
    | Heq : _ = TauF _ |- _ => dependent destruction Heq
    | Heq : TauF _ = _ |- _ => dependent destruction Heq
    end.
    apply pfrontier_tau_inv in H0.
    eapply PWFrontier; eassumption.
  - inversion Erhs; subst.
    pclearbot.
    apply PWTauL.
    have Hu := paco2_unfold pweakP_monotone H0.
    exact Hu.
  - apply PWTauL.
    eapply IHHstep; eauto.
  - injection Erhs as Et.
    subst t2.
    assumption.
Qed.

End PWeakPaco.

#[global] Hint Resolve pweakP_monotone : paco.
