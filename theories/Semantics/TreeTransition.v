Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.Equality Logic.ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Semantics Require Import HeadTransition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An offered event is observable before a response is supplied. In
    particular this retains events whose response type is Empty_set. *)
Inductive offered_event (E : Type -> Type) : Type :=
  | Offered {X : Type} (e : E X).
Arguments Offered {E X} _.

(** Enabling is independent of the existence/mass of successor hitting.
    A matching action whose continuation diverges is still enabled. *)
Inductive head_enabled {E MN R} :
    stable_head E MN R -> obs_label E -> Prop :=
  | HeadEnabled {X} (e : E X) (k : X -> ptree E MN R) x :
      head_enabled (FHVis e k) (Obs e x).

Lemma head_enabled_ret {E MN R} (r : R) (label : obs_label E) :
  ~ @head_enabled E MN R (FHRet r) label.
Proof. intro H. inversion H. Qed.

Section TreeTransition.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R : Type}.
Local Notation head := (stable_head E MN R).
Local Notation hits t out := (ptree_stable_hitting (MF := MF) (observe t) out).

Definition return_projection (h : head) : MF R :=
  match h with FHRet r => sem_ret r | @FHVis _ _ _ _ _ _ => sem_zero end.
Definition offered_event_projection (h : head) : MF (offered_event E) :=
  match h with FHRet _ => sem_zero | @FHVis _ _ _ _ e _ => sem_ret (Offered e) end.

(** Observation measures retain their original mass. A nonmatching kind of
    head contributes zero, not a normalized conditional probability. *)
Definition tree_head_observation {O} (project : head -> MF O)
    (t : ptree E MN R) (out : MF O) : Prop :=
  exists front, hits t front /\ sem_eq (sem_bind front project) out.
Definition tree_return_observation := tree_head_observation return_projection.
Definition tree_offered_event_observation := tree_head_observation offered_event_projection.

(** A PER-HEAD contribution. This is not a rule for choosing one head of
    the source distribution. The whole source is integrated below. *)
Inductive head_action_result (label : obs_label E) (h : head) (out : MF head) : Prop :=
  | HARMatch : head_step h label out -> head_action_result label h out
  | HARMiss : ~ head_enabled h label -> sem_eq out sem_zero ->
      head_action_result label h out.

(** Raw-tree, response-wise transition. First complete internal execution,
    then integrate ALL matching heads' successor distributions. The AE
    premise permits arbitrary choices only on null branches. Both witnesses
    are proof data; uniqueness up to equality coupling is proved below.

    The target consists of stable heads, as in head_step, but the SOURCE
    here is an arbitrary raw PTree. There is no mdp_state or totality premise,
    and no bisimulation is defined in this module. *)
Definition tree_trans (t : ptree E MN R) (label : obs_label E) (out : MF head) : Prop :=
  exists front next,
    hits t front /\
    sem_ae front (fun h => head_action_result label h (next h)) /\
    sem_eq (sem_bind front next) out.

Lemma head_step_enabled (h : head) (label : obs_label E) (out : MF head) :
  head_step h label out -> head_enabled h label.
Proof. intro H. destruct H. constructor. Qed.

Section Core.
Context `{FC : @SemanticMeasureCoreLaws MF FI}.

Lemma tree_trans_from_hitting t label front next :
  hits t front ->
  sem_ae front (fun h => head_action_result label h (next h)) ->
  tree_trans t label (sem_bind front next).
Proof. intros Hhit Hae. exists front, next. split; [exact Hhit|]. split; [exact Hae|apply sem_eq_refl]. Qed.

Lemma tree_trans_output_proper t label out out' :
  sem_eq out out' -> tree_trans t label out -> tree_trans t label out'.
Proof.
  intros Heq [front [next [Hhit [Hae Hout]]]]. exists front, next.
  split; [exact Hhit|]. split; [exact Hae|]. eapply sem_eq_trans; eassumption.
Qed.

Lemma tree_head_observation_output_proper {O} (project : head -> MF O) t out out' :
  sem_eq out out' -> tree_head_observation project t out ->
  tree_head_observation project t out'.
Proof.
  intros Heq [front [Hhit Hout]]. exists front. split; [exact Hhit|].
  eapply sem_eq_trans; eassumption.
Qed.

Section Uniqueness.
Context `{FOL : @SemanticOmegaLaws MF FI FO}.

Lemma head_action_result_unique label h out1 out2 :
  head_action_result label h out1 -> head_action_result label h out2 ->
  sem_eq out1 out2.
Proof.
  intros H1 H2. destruct H1 as [H1|Hnone1 Hzero1]; destruct H2 as [H2|Hnone2 Hzero2].
  - eapply head_step_unique; eassumption.
  - exfalso. apply Hnone2. eapply head_step_enabled; eassumption.
  - exfalso. apply Hnone1. eapply head_step_enabled; eassumption.
  - eapply sem_eq_trans; [exact Hzero1|]. apply sem_eq_sym. exact Hzero2.
Qed.

Context `{FB : @SemanticMeasureBindLaws MF FI}.

Theorem tree_head_observation_unique {O} (project : head -> MF O) t out1 out2 :
  tree_head_observation project t out1 -> tree_head_observation project t out2 ->
  sem_lift eq out1 out2.
Proof.
  intros [front1 [H1 Ho1]] [front2 [H2 Ho2]].
  eapply sem_lift_proper_l; [exact Ho1|].
  eapply sem_lift_proper_r; [exact Ho2|].
  eapply sem_lift_bind with (R := eq).
  - assert (Heq : sem_eq front1 front2).
    { eapply stable_hitting_unique; [exact H1|exact H2]. }
    eapply sem_lift_proper_r; [exact Heq|].
    apply sem_lift_refl. intro h. reflexivity.
  - intros h k ->. apply sem_lift_refl. intro x. reflexivity.
Qed.

Context `{FCAE : @SemanticMeasureCouplingAELaws MF FI}.

(** The interface need not reflect equality couplings to sem_eq. This is
    the same representation-independent uniqueness boundary as finite
    interaction observations, with no extra reflection axiom. *)
Theorem tree_trans_unique t label out1 out2 :
  tree_trans t label out1 -> tree_trans t label out2 -> sem_lift eq out1 out2.
Proof.
  intros [front1 [next1 [H1 [Hae1 Ho1]]]] [front2 [next2 [H2 [Hae2 Ho2]]]].
  assert (Hfront : sem_lift eq front1 front2).
  { assert (Heq : sem_eq front1 front2).
    { eapply stable_hitting_unique; [exact H1|exact H2]. }
    eapply sem_lift_proper_r; [exact Heq|].
    apply sem_lift_refl. intro h. reflexivity. }
  pose proof (sem_lift_ae_restrict Hfront Hae1 Hae2) as Hrestricted.
  eapply sem_lift_proper_l; [exact Ho1|].
  eapply sem_lift_proper_r; [exact Ho2|].
  eapply sem_lift_bind; [exact Hrestricted|].
  intros h k [Heq [Hleft Hright]]. subst k.
  assert (Hout : sem_eq (next1 h) (next2 h)).
  { eapply head_action_result_unique; [exact Hleft|exact Hright]. }
  eapply sem_lift_proper_r; [exact Hout|].
  apply sem_lift_refl. intro x. reflexivity.
Qed.
End Uniqueness.

Section Existence.
Context `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.

Lemma head_action_result_exists label h : exists out, head_action_result label h out.
Proof.
  destruct (classic (head_enabled h label)) as [Hyes|Hno].
  - destruct Hyes as [X e k x].
    destruct (head_step_exists e k x) as [out Hstep]. exists out. constructor. exact Hstep.
  - exists sem_zero. apply HARMiss; [exact Hno|apply sem_eq_refl].
Qed.

Theorem tree_head_observation_exists {O} (project : head -> MF O) t :
  exists out, tree_head_observation project t out.
Proof.
  destruct (stable_hitting_exists (@ptree_primitive_kernel E MN MF FI MX R) (observe t))
    as [front Hhit]. exists (sem_bind front project), front.
  split; [exact Hhit|apply sem_eq_refl].
Qed.

(** Classical choice selects complete-hitting witnesses, not one supported
    state. There is still only one transition measure up to coupling. *)
Theorem tree_trans_exists t label : exists out, tree_trans t label out.
Proof.
  destruct (choice _ (head_action_result_exists label)) as [next Hnext].
  destruct (stable_hitting_exists (@ptree_primitive_kernel E MN MF FI MX R) (observe t))
    as [front Hhit]. exists (sem_bind front next).
  apply tree_trans_from_hitting; [exact Hhit|].
  eapply sem_ae_mono; [|apply sem_ae_true]. intros h _. apply Hnext.
Qed.
End Existence.

Section Computation.
Context `{FB : @SemanticMeasureBindLaws MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma tree_head_observation_ret {O} (project : head -> MF O) r :
  tree_head_observation project (Ret r) (project (FHRet r)).
Proof.
  exists (sem_ret (FHRet r)). split; [apply ptree_stable_hitting_ret|apply sem_bind_ret_l].
Qed.

Lemma tree_head_observation_vis {O X} (project : head -> MF O) (e : E X) k :
  tree_head_observation project (Vis e k) (project (FHVis e k)).
Proof.
  exists (sem_ret (FHVis e k)). split; [apply ptree_stable_hitting_vis|apply sem_bind_ret_l].
Qed.

Lemma tree_return_ret r : tree_return_observation (Ret r) (sem_ret r).
Proof. apply tree_head_observation_ret. Qed.
Lemma tree_offered_ret r : tree_offered_event_observation (Ret r) sem_zero.
Proof. apply tree_head_observation_ret. Qed.
Lemma tree_return_vis {X} (e : E X) k : tree_return_observation (Vis e k) sem_zero.
Proof. apply tree_head_observation_vis. Qed.
Lemma tree_offered_vis {X} (e : E X) k :
  tree_offered_event_observation (Vis e k) (sem_ret (Offered e)).
Proof. exact (tree_head_observation_vis offered_event_projection e k). Qed.

Lemma tree_head_observation_tau_iff {O} (project : head -> MF O) t out :
  tree_head_observation project (Tau t) out <-> tree_head_observation project t out.
Proof.
  split; intros [front [Hhit Hout]]; exists front; split; try exact Hout.
  - exact (proj1 (ptree_stable_hitting_tau_iff t front) Hhit).
  - exact (proj2 (ptree_stable_hitting_tau_iff t front) Hhit).
Qed.

Lemma tree_trans_tau_iff t label out : tree_trans (Tau t) label out <-> tree_trans t label out.
Proof.
  split; intros [front [next [Hhit Hrest]]]; exists front, next; split; try exact Hrest.
  - exact (proj1 (ptree_stable_hitting_tau_iff t front) Hhit).
  - exact (proj2 (ptree_stable_hitting_tau_iff t front) Hhit).
Qed.

Context `{FAE : @SemanticMeasureAEKleisliLaws MF FI}.

Lemma tree_trans_ret r label : tree_trans (Ret r) label sem_zero.
Proof.
  exists (sem_ret (FHRet r)), (fun _ : head => (sem_zero : MF head)).
  split; [apply ptree_stable_hitting_ret|]. split.
  2: exact (sem_bind_ret_l (FHRet r) (fun _ : head => (sem_zero : MF head))).
  apply sem_ae_ret. apply HARMiss; [apply head_enabled_ret|apply sem_eq_refl].
Qed.

(** The raw API includes zero outputs for absent labels, whereas head_step
    itself has no step from Ret or a nonmatching event. *)
Lemma tree_trans_vis {X} (e : E X) k x out :
  hits (k x) out -> tree_trans (Vis e k) (Obs e x) out.
Proof.
  intro Hhit. exists (sem_ret (FHVis e k)), (fun _ : head => out).
  split; [apply ptree_stable_hitting_vis|]. split.
  2: exact (sem_bind_ret_l (FHVis e k) (fun _ : head => out)).
  apply sem_ae_ret. apply HARMatch. constructor. exact Hhit.
Qed.

Lemma tree_trans_vis_miss {X} (e : E X) k label :
  ~ head_enabled (FHVis e k) label -> tree_trans (Vis e k) label sem_zero.
Proof.
  intro Hno. exists (sem_ret (FHVis e k)), (fun _ : head => (sem_zero : MF head)).
  split; [apply ptree_stable_hitting_vis|]. split.
  2: exact (sem_bind_ret_l (FHVis e k) (fun _ : head => (sem_zero : MF head))).
  apply sem_ae_ret. apply HARMiss; [exact Hno|apply sem_eq_refl].
Qed.
End Computation.
End Core.
End TreeTransition.
