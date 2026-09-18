Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Logic.ClassicalChoice.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import
  FiniteInternal UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt
  PStrong PFiniteResidual.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The semantic bridge is separate from the operational judgment. *)
Section FiniteInternalHitting.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{FI : SemanticMeasure MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Section OneReturnType.
Context {R : Type}.
Local Notation K := (@ptree_primitive_kernel E MN MF FI MX R).

Theorem finite_internal_hitting_lift t out
    (front : ptree E MN R -> MF (stable_head E MN R)) target :
  finite_internal t out ->
  (forall u, stable_hitting K (observe u) (front u)) ->
  stable_hitting K (observe t) target ->
  sem_lift eq target (sem_bind out front).
Proof.
  intros Hexec Hfront. revert target. induction Hexec; intros target Htarget.
  - eapply sem_lift_proper_r.
    + apply sem_eq_sym. apply sem_bind_ret_l.
    + eapply sem_lift_proper_l.
      * eapply stable_hitting_unique; [apply Hfront|exact Htarget].
      * apply sem_lift_refl. intro h. reflexivity.
  - apply IHHexec. apply (proj1 (stable_hitting_tau_iff t target)).
    exact Htarget.
  - assert (Hprob : stable_hitting K (observe (Prob mu k))
        (mixed_bind mu (fun x => front (k x)))).
    { eapply stable_hitting_prob with (Good := fun _ => True).
      - apply sem_ae_true.
      - intros x _. apply Hfront. }
    eapply sem_lift_proper_l.
    + eapply stable_hitting_unique; [exact Hprob|exact Htarget].
    + eapply sem_lift_proper_r.
      * apply sem_eq_sym. apply mixed_bind_assoc.
      * eapply mixed_lift_bind with (R := eq).
        -- apply sem_lift_refl. intro x. reflexivity.
        -- intros x y ->. apply H0. apply Hfront.
Qed.

End OneReturnType.

(** Sound inductive compression around an already established behavioral
    relation.  This is a rewriting rule, not a coinduction-up-to theorem:
    its premise must not be replaced by an unproved coinductive hypothesis. *)
Theorem peutt_of_finite_internal {A B} (RR : A -> B -> Prop)
    (t1 : ptree E MN A) (t2 : ptree E MN B) out1 out2 :
  finite_internal t1 out1 -> finite_internal t2 out2 ->
  sem_lift (@peutt E MN MF FI FC MX FO A B RR) out1 out2 ->
  peutt RR t1 t2.
Proof.
  intros Hexec1 Hexec2 Hres.
  assert (Hex1 : forall u : ptree E MN A, exists out,
      stable_hitting (@ptree_primitive_kernel E MN MF FI MX A)
        (observe u) out).
  { intro u. apply stable_hitting_exists. }
  assert (Hex2 : forall u : ptree E MN B, exists out,
      stable_hitting (@ptree_primitive_kernel E MN MF FI MX B)
        (observe u) out).
  { intro u. apply stable_hitting_exists. }
  destruct (choice _ Hex1) as [front1 Hfront1].
  destruct (choice _ Hex2) as [front2 Hfront2].
  eapply peutt_of_hitting_lift; [apply Hfront1|apply Hfront2|].
  eapply sem_lift_mono with
    (R := fun x z => exists y, x = y /\ stable_head_rel RR (peutt RR) y z).
  - intros x z [y [-> Hyz]]. exact Hyz.
  - eapply sem_lift_comp.
    + eapply finite_internal_hitting_lift;
        [exact Hexec1|exact Hfront1|apply Hfront1].
    + eapply sem_lift_mono with
        (R := fun x z => exists y, stable_head_rel RR (peutt RR) x y /\ z = y).
      * intros x z [y [Hxy Heq]]. subst y. exact Hxy.
      * eapply sem_lift_comp.
        -- eapply sem_lift_bind; [exact Hres|].
           intros u v Huv. eapply peutt_hitting_lift;
             [exact Huv|apply Hfront1|apply Hfront2].
        -- apply sem_lift_sym. eapply finite_internal_hitting_lift;
             [exact Hexec2|exact Hfront2|apply Hfront2].
Qed.

(** A single guarded round is sound when its recursive obligations are
    already proved.  This pre-fixed-point fact alone does NOT establish
    inclusion of the greatest fixed point [pfinite_residual_rel]. *)
Theorem pfinite_residual_round_sound {A} (t1 t2 : ptree E MN A) :
  pfinite_residualF eq (@peutt E MN MF FI FC MX FO A A eq) t1 t2 ->
  peutt eq t1 t2.
Proof.
  intro Hstep. destruct Hstep.
  eapply peutt_of_finite_internal; [exact H|exact H0|].
  eapply sem_lift_mono; [|exact H1].
  intros u1 u2 Hguard. unfold pfinite_guard in Hguard.
  change (peutt_state eq (observe u1) (observe u2)).
  remember (observe u1) as o1 in Hguard |- *.
  remember (observe u2) as o2 in Hguard |- *.
  destruct Hguard.
  - apply peutt_ret. exact H2.
  - apply peutt_tau_Proper. exact H2.
  - apply peutt_vis. exact H2.
  - eapply peutt_prob; [exact H2|]. intros x y Hxy. exact Hxy.
Qed.

End FiniteInternalHitting.
