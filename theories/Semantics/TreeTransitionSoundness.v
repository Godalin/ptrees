Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This comparison module, unlike the transition semantics and its GFP,
    deliberately imports PEutt. No definition in either relation changes.
    Return relations below may be arbitrary, on a common return carrier.
    In particular RR = eq gives the behavioral inclusion of interest. *)
Section Soundness.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}.
Context {R : Type} (RR : R -> R -> Prop).
Local Notation tree := (ptree E MN R).
Local Notation head := (stable_head E MN R).
Local Notation W := (@peutt E MN MF FI FC MX FO R R RR).
Local Notation HR := (stable_head_rel RR W).

(** There is no need for a new zero-coupling axiom on a common carrier.
    Restrict the reflexive coupling to the empty AE support. *)
Lemma tree_transition_zero_lift {A} (rel : A -> A -> Prop) :
  sem_lift rel sem_zero sem_zero.
Proof.
  assert (Hself : sem_lift (@eq A) sem_zero sem_zero).
  { apply sem_lift_refl. intro x. reflexivity. }
  pose proof (sem_lift_ae_restrict Hself
    (sem_ae_zero (fun _ : A => False)) (sem_ae_zero (fun _ : A => False))) as Hempty.
  eapply sem_lift_mono; [|exact Hempty]. intros x y [_ [Hfalse _]]. contradiction.
Qed.

Lemma peutt_stable_heads_as_trees h k : HR h k ->
  tree_trans_head_rel W h k.
Proof.
  intro H. destruct H; unfold tree_trans_head_rel; cbn.
  - apply peutt_ret. assumption.
  - apply peutt_vis. assumption.
Qed.

Lemma peutt_couples_complete_heads (t u : tree) front1 front2 :
  W t u -> ptree_stable_hitting (MF := MF) (observe t) front1 ->
  ptree_stable_hitting (MF := MF) (observe u) front2 -> sem_lift HR front1 front2.
Proof. intros. eapply peutt_hitting_lift; eassumption. Qed.

Lemma related_heads_enable_same_label h k label : HR h k ->
  (head_enabled h label <-> head_enabled k label).
Proof.
  intro H. destruct H; split; intro Hen; dependent destruction Hen; constructor.
Qed.

Lemma peutt_head_action_results label h k out1 out2 :
  HR h k -> head_action_result label h out1 -> head_action_result label k out2 ->
  sem_lift (tree_trans_head_rel W) out1 out2.
Proof.
  intros Hrel Hleft Hright.
  destruct Hleft as [Hstep1|Hno1 Hz1]; destruct Hright as [Hstep2|Hno2 Hz2].
  - destruct Hrel.
    + exfalso. eapply head_step_ret. exact Hstep1.
    + dependent destruction Hstep1. apply head_step_vis_iff in Hstep2.
      eapply sem_lift_mono; [apply peutt_stable_heads_as_trees|].
      eapply peutt_couples_complete_heads; [apply H|exact H0|exact Hstep2].
  - exfalso. apply Hno2. apply (proj1 (related_heads_enable_same_label label Hrel)).
    eapply head_step_enabled; exact Hstep1.
  - exfalso. apply Hno1. apply (proj2 (related_heads_enable_same_label label Hrel)).
    eapply head_step_enabled; exact Hstep2.
  - eapply sem_lift_proper_l; [apply sem_eq_sym; exact Hz1|].
    eapply sem_lift_proper_r; [apply sem_eq_sym; exact Hz2|].
    apply tree_transition_zero_lift.
Qed.

(** A reusable projection argument: keep the original whole-head coupling,
    then apply the relational bind law to the chosen observation kernels. *)
Lemma peutt_projects_heads {O1 O2} (OR : O1 -> O2 -> Prop)
    (project1 : head -> MF O1) (project2 : head -> MF O2)
    (Hproject : forall h k, HR h k -> sem_lift OR (project1 h) (project2 k))
    (t u : tree) out1 out2 :
  W t u -> tree_head_observation project1 t out1 ->
  tree_head_observation project2 u out2 -> sem_lift OR out1 out2.
Proof.
  intros Hrel [front1 [Hhit1 Ho1]] [front2 [Hhit2 Ho2]].
  eapply sem_lift_proper_l; [exact Ho1|].
  eapply sem_lift_proper_r; [exact Ho2|].
  eapply sem_lift_bind; [eapply peutt_couples_complete_heads; eassumption|exact Hproject].
Qed.

Theorem peutt_preserves_tree_return_observation (t u : tree) out1 out2 :
  W t u -> tree_return_observation t out1 -> tree_return_observation u out2 ->
  sem_lift RR out1 out2.
Proof.
  eapply peutt_projects_heads. intros h k Hrel. destruct Hrel; cbn.
  - apply sem_lift_ret. assumption.
  - apply tree_transition_zero_lift.
Qed.

Theorem peutt_preserves_tree_offered_event_observation (t u : tree) out1 out2 :
  W t u -> tree_offered_event_observation t out1 -> tree_offered_event_observation u out2 ->
  sem_lift eq out1 out2.
Proof.
  eapply peutt_projects_heads. intros h k Hrel. destruct Hrel; cbn.
  - apply tree_transition_zero_lift.
  - apply sem_lift_ret. reflexivity.
Qed.

(** AE restriction is essential: the contribution functions need only be
    correct almost everywhere, not at null heads. Integrating a coupling
    restricted to BOTH such predicates preserves the original masses. *)
Theorem peutt_preserves_tree_trans (t u : tree) label out1 out2 :
  W t u -> tree_trans t label out1 -> tree_trans u label out2 ->
  sem_lift (tree_trans_head_rel W) out1 out2.
Proof.
  intros Hrel [front1 [next1 [Hhit1 [Hae1 Ho1]]]]
    [front2 [next2 [Hhit2 [Hae2 Ho2]]]].
  pose proof (peutt_couples_complete_heads Hrel Hhit1 Hhit2) as Hfront.
  pose proof (sem_lift_ae_restrict Hfront Hae1 Hae2) as Hrestricted.
  eapply sem_lift_proper_l; [exact Ho1|].
  eapply sem_lift_proper_r; [exact Ho2|].
  eapply sem_lift_bind; [exact Hrestricted|].
  intros h k [Hhk [Hleft Hright]]. eapply peutt_head_action_results; eassumption.
Qed.

Context `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.

(** The candidate is peutt itself: this is a direct post-fixed-point
    theorem, not a transport through selected-head bisimulation. *)
Theorem peutt_tree_trans_postfixed (t u : tree) :
  W t u -> tree_trans_bisimF RR W t u.
Proof.
  intro Hrel. split.
  - split; intros out Hout.
    + destruct (tree_head_observation_exists (return_projection (MF := MF)) u) as [other Hother].
      exists other. split; [exact Hother|].
      eapply peutt_preserves_tree_return_observation; eassumption.
    + destruct (tree_head_observation_exists (return_projection (MF := MF)) t) as [other Hother].
      exists other. split; [exact Hother|].
      eapply peutt_preserves_tree_return_observation; eassumption.
  - split.
    + split; intros out Hout.
      * destruct (tree_head_observation_exists (offered_event_projection (MF := MF)) u) as [other Hother].
        exists other. split; [exact Hother|].
        eapply peutt_preserves_tree_offered_event_observation; eassumption.
      * destruct (tree_head_observation_exists (offered_event_projection (MF := MF)) t) as [other Hother].
        exists other. split; [exact Hother|].
        eapply peutt_preserves_tree_offered_event_observation; eassumption.
    + intro label. split; intros out Hout.
      * destruct (tree_trans_exists u label) as [other Hother].
        exists other. split; [exact Hother|]. eapply peutt_preserves_tree_trans; eassumption.
      * destruct (tree_trans_exists t label) as [other Hother].
        exists other. split; [exact Hother|]. eapply peutt_preserves_tree_trans; eassumption.
Qed.

Theorem peutt_tree_trans_bisim (t u : tree) :
  W t u -> tree_trans_bisim RR t u.
Proof.
  eapply tree_trans_bisim_coinduction. exact peutt_tree_trans_postfixed.
Qed.
End Soundness.
