Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From Paco Require Import paco.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.
From PTree.Eq Require Import PWeakAbstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H) :=
  move IND before H; revert_until IND; induction IND.

#[local] Hint Constructors apweakF : paco.

Section PWeakAbstractPaco.

Context {E : Type -> Type} {M : Type -> Type}.
Context `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition apweakP_
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  apweakF RR sim (observe t1) (observe t2).

Lemma apweakP_monotone : monotone2 apweakP_.
Proof.
  move=> t1 t2 sim1 sim2 Hstep Hsub.
  eapply apweakF_monotone; [exact Hsub|exact Hstep].
Qed.

#[local] Hint Resolve apweakP_monotone : paco.

Definition apweakP : ptree E M R1 -> ptree E M R2 -> Prop :=
  paco2 apweakP_ bot2.

Lemma apweak_to_apweakP :
  forall t1 t2, apweak RR t1 t2 -> apweakP t1 t2.
Proof.
  pcofix CIH. move=> t1 t2 Hrel. pstep.
  move: (apweak_unfold Hrel)=> Hstep. red.
  eapply apweakF_monotone.
  - move=> u v Huv. right. exact: CIH Huv.
  - exact Hstep.
Qed.

Lemma apweakP_to_apweak :
  forall t1 t2, apweakP t1 t2 -> apweak RR t1 t2.
Proof.
  unfold apweak. coinduction CH CIH. move=> t1 t2 Hrel.
  unfold apweakP in Hrel. punfold Hrel. red in Hrel. cbn in Hrel.
  change (apweakF RR (elem CH) (observe t1) (observe t2)).
  eapply (apweakF_monotone
    (sim1 := upaco2 apweakP_ bot2)
    (sim2 := elem CH)).
  - move=> u v Huv. pclearbot. apply CIH. exact Huv.
  - exact Hrel.
Qed.

Lemma apweak_iff_apweakP t1 t2 :
  apweak RR t1 t2 <-> apweakP t1 t2.
Proof. split; [exact: apweak_to_apweakP|exact: apweakP_to_apweak]. Qed.

Lemma apweakP_inv_tau_r
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweakP t1 (Tau t2) -> apweakP t1 t2.
Proof.
  move=> Hrel. unfold apweakP in Hrel |- *. pstep. red.
  punfold Hrel. red in Hrel. cbn in Hrel.
  remember (TauF t2) as rhs eqn:Erhs in Hrel.
  dependent induction Hrel; try discriminate.
  - dependent destruction H0. eapply APWFrontier; eassumption.
  - pclearbot. rewrite -x. apply APWTauL. pstep_reverse.
  - rewrite -x. apply APWTauL. eapply IHHrel; eauto.
  - assumption.
Qed.

Lemma apweakP_inv_tau_l
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweakP (Tau t1) t2 -> apweakP t1 t2.
Proof.
  move=> Hrel. unfold apweakP in Hrel |- *. pstep. red.
  punfold Hrel. red in Hrel. cbn in Hrel.
  remember (TauF t1) as lhs eqn:Elhs in Hrel.
  dependent induction Hrel; try discriminate.
  - dependent destruction H. eapply APWFrontier; eassumption.
  - pclearbot. rewrite -x. apply APWTauR. pstep_reverse.
  - assumption.
  - rewrite -x. apply APWTauR. eapply IHHrel; eauto.
Qed.

Lemma apweakP_inv_tau
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  apweakP (Tau t1) (Tau t2) -> apweakP t1 t2.
Proof.
  move=> H. apply apweakP_inv_tau_l in H.
  exact: apweakP_inv_tau_r H.
Qed.

Lemma apweakF_inv_tau_l_step
    (t1 : ptree E M R1) (ot2 : ptree' E M R2) :
  apweakF RR (upaco2 apweakP_ bot2) (TauF t1) ot2 ->
  apweakF RR (upaco2 apweakP_ bot2) (observe t1) ot2.
Proof.
  move=> Hstep.
  remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - match goal with
    | Heq : _ = TauF _ |- _ => dependent destruction Heq
    | Heq : TauF _ = _ |- _ => dependent destruction Heq
    end.
    dependent destruction H. eapply APWFrontier; eassumption.
  - injection Elhs as Et. subst t0. pclearbot. apply APWTauR.
    have Hu := paco2_unfold apweakP_monotone H0. exact Hu.
  - injection Elhs as Et. subst t0. assumption.
  - apply APWTauR. eapply IHHstep; eauto.
Qed.

Lemma apweakF_inv_tau_r_step
    (ot1 : ptree' E M R1) (t2 : ptree E M R2) :
  apweakF RR (upaco2 apweakP_ bot2) ot1 (TauF t2) ->
  apweakF RR (upaco2 apweakP_ bot2) ot1 (observe t2).
Proof.
  move=> Hstep.
  remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - match goal with
    | Heq : _ = TauF _ |- _ => dependent destruction Heq
    | Heq : TauF _ = _ |- _ => dependent destruction Heq
    end.
    dependent destruction H0. eapply APWFrontier; eassumption.
  - inversion Erhs; subst. pclearbot. apply APWTauL.
    have Hu := paco2_unfold apweakP_monotone H0. exact Hu.
  - apply APWTauL. eapply IHHstep; eauto.
  - injection Erhs as Et. subst t2. assumption.
Qed.

End PWeakAbstractPaco.

#[global] Hint Resolve apweakP_monotone : paco.
