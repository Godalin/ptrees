Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Semantics Require Import HeadTransition MDPFragment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The source model exposes a state observation and has a total kernel
    for every state/action pair.
    The target fragment additionally admits observable terminal states;
    this particular encoding never returns. *)
Record MDP (MN : Type -> Type) `{NI : SemanticMeasure MN}
    `{NO : @SemanticOmega MN NI} := {
  mdp_states : Type;
  mdp_actions : Type;
  mdp_observations : Type;
  mdp_observe : mdp_states -> mdp_observations;
  mdp_transition : mdp_states -> mdp_actions -> MN mdp_states;
  mdp_transition_total : forall s a, sem_total (mdp_transition s a)
}.
Arguments MDP MN {NI NO}.
Arguments mdp_states {MN NI NO} _.
Arguments mdp_actions {MN NI NO} _.
Arguments mdp_observations {MN NI NO} _.
Arguments mdp_observe {MN NI NO} _ _.
Arguments mdp_transition {MN NI NO} _ _ _.
Arguments mdp_transition_total {MN NI NO} _ _ _.

Variant mdpE (O A : Type) : Type -> Type := Choose (o : O) : mdpE O A A.
Arguments Choose {O A} _.

(** One visible interaction exposes the current observation and accepts
    an action. No extra observation-only event is inserted. *)
Lemma mdp_choose_head_rel_iff {O A MN R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree (mdpE O A) MN R1 -> ptree (mdpE O A) MN R2 -> Prop)
    (o1 o2 : O) k1 k2 :
  stable_head_rel RR sim (FHVis (Choose o1) k1) (FHVis (Choose o2) k2) <->
  o1 = o2 /\ forall a, sim (k1 a) (k2 a).
Proof.
  split.
  - intro H. dependent destruction H. split; [reflexivity|assumption].
  - intros [-> H]. constructor. exact H.
Qed.

Section Source.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Variable D : MDP MN.

CoFixpoint mdp_encode (s : mdp_states D) :
    ptree (mdpE (mdp_observations D) (mdp_actions D)) MN unit :=
  Vis (Choose (mdp_observe D s)) (fun a => Prob (mdp_transition D s a) mdp_encode).

Definition mdp_encode_head s :
    stable_head (mdpE (mdp_observations D) (mdp_actions D)) MN unit :=
  FHVis (Choose (mdp_observe D s)) (fun a => Prob (mdp_transition D s a) mdp_encode).

(** Independent textbook coupling bisimulation, over SOURCE states. *)
Definition mdp_bisimF (sim : mdp_states D -> mdp_states D -> Prop) s t :=
  mdp_observe D s = mdp_observe D t /\
  forall a, sem_lift sim (mdp_transition D s a) (mdp_transition D t a).

Program Definition fmdp_bisim : mon (mdp_states D -> mdp_states D -> Prop) :=
  {| body := mdp_bisimF |}.
Next Obligation.
  intros P Q Hsub s t [Hobs H]. split; [exact Hobs|].
  intro a. eapply sem_lift_mono; [exact Hsub|apply H].
Qed.
Definition mdp_bisim := gfp fmdp_bisim.
Lemma mdp_bisim_unfold s t : mdp_bisim s t -> mdp_bisimF mdp_bisim s t.
Proof. intro H. apply (gfp_pfp fmdp_bisim) in H. exact H. Qed.
Lemma mdp_bisim_fold s t : mdp_bisimF mdp_bisim s t -> mdp_bisim s t.
Proof. intro H. unfold mdp_bisim. apply (gfp_fp fmdp_bisim). exact H. Qed.
Lemma mdp_bisim_observe s t : mdp_bisim s t -> mdp_observe D s = mdp_observe D t.
Proof. intro H. exact (proj1 (mdp_bisim_unfold H)). Qed.
Lemma mdp_bisim_step s t : mdp_bisim s t ->
  forall a, sem_lift mdp_bisim (mdp_transition D s a) (mdp_transition D t a).
Proof. intro H. exact (proj2 (mdp_bisim_unfold H)). Qed.
Theorem mdp_bisim_coinduction (sim : mdp_states D -> mdp_states D -> Prop)
    (Hpost : forall s t, sim s t -> mdp_bisimF sim s t) :
  forall s t, sim s t -> mdp_bisim s t.
Proof.
  intros s t H. unfold mdp_bisim.
  eapply (@leq_gfp _ _ fmdp_bisim sim); eauto.
Qed.

Section Behavior.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Local Notation hits t out := (ptree_stable_hitting (MF := MF) (observe t) out).

Definition mdp_successors (mu : MN (mdp_states D)) :=
  mixed_bind mu (fun s => sem_ret (mdp_encode_head s)).

Lemma mdp_encode_hitting s : hits (mdp_encode s) (sem_ret (mdp_encode_head s)).
Proof.
  change (ptree_stable_hitting (MF := MF)
    (VisF (Choose (mdp_observe D s)) (fun a => Prob (mdp_transition D s a) mdp_encode))
    (sem_ret (mdp_encode_head s))).
  apply ptree_stable_hitting_vis.
Qed.

Lemma mdp_sample_hitting mu :
  hits (Prob mu mdp_encode) (mdp_successors mu).
Proof.
  eapply ptree_stable_hitting_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros s _. apply mdp_encode_hitting.
Qed.

Theorem mdp_encode_step s a :
  head_step (mdp_encode_head s) (Obs (Choose (mdp_observe D s)) a)
    (mdp_successors (mdp_transition D s a)).
Proof. constructor. apply mdp_sample_hitting. Qed.

(** Exact kernel agreement, modulo the interface's equality of measures.
    No choice of a canonical complete-hitting representative is needed. *)
Theorem mdp_encode_step_unique s a out :
  head_step (mdp_encode_head s) (Obs (Choose (mdp_observe D s)) a) out ->
  sem_eq out (mdp_successors (mdp_transition D s a)).
Proof.
  intro H. eapply head_step_unique; [exact H|apply mdp_encode_step].
Qed.

(** Explicit sufficient premises for the unary fragment. The base mixed
    interface alone says nothing about totality or AE of mixed binds.
    The SubEnum endpoint below discharges these premises, not axiomatizes them. *)
Theorem mdp_encode_mdp_state
    (Htotal : forall s a, sem_total (mdp_successors (mdp_transition D s a)))
    (Hsupport : forall s a, sem_ae (mdp_successors (mdp_transition D s a))
      (fun h => exists t, h = mdp_encode_head t)) :
  forall s, mdp_state (MF := MF) (mdp_encode s).
Proof.
  assert (Hhead : forall s, mdp_head (MF := MF) (mdp_encode_head s)).
  { intro s. eapply mdp_head_coinduction with
      (P := fun h => exists t, h = mdp_encode_head t).
    - intros h [t ->]. intro a.
      exists (mdp_successors (mdp_transition D t a)).
      split; [apply mdp_encode_step|]. split; [apply Htotal|apply Hsupport].
    - exists s. reflexivity. }
  intro s. eapply mdp_state_of_hitting; [apply mdp_encode_hitting| |apply Hhead].
  apply sem_eq_refl.
Qed.

Theorem mdp_bisim_head_sound s t :
  mdp_bisim s t -> head_bisim (MF := MF) eq (mdp_encode_head s) (mdp_encode_head t).
Proof.
  intro H. eapply head_bisim_coinduction with
    (sim := fun h k => exists s t, h = mdp_encode_head s /\
      k = mdp_encode_head t /\ mdp_bisim s t).
  - intros h k [u [v [-> [-> Huv]]]].
    destruct (mdp_bisim_unfold Huv) as [Hobs Hsteps].
    unfold head_bisimF, mdp_encode_head. rewrite Hobs. constructor. intro a.
    eapply stable_hitting_match_of_hitting_lift;
      [apply mdp_sample_hitting|apply mdp_sample_hitting|].
    eapply mixed_lift_bind; [exact (Hsteps a)|].
    intros x y Hxy. apply sem_lift_ret. exists x, y. auto.
  - exists s, t. auto.
Qed.

(** The two forms are proof states only: a selected encoded state, or an
    action's sampled successor distribution. They do not define semantics. *)
Inductive mdp_encoding_candidate :
    ptree' (mdpE (mdp_observations D) (mdp_actions D)) MN unit ->
    ptree' (mdpE (mdp_observations D) (mdp_actions D)) MN unit -> Prop :=
  | MECState s t : mdp_bisim s t ->
      mdp_encoding_candidate (observe (mdp_encode s)) (observe (mdp_encode t))
  | MECSample mu nu : sem_lift mdp_bisim mu nu ->
      mdp_encoding_candidate (ProbF mu mdp_encode) (ProbF nu mdp_encode).

Lemma mdp_encoding_head_related s t : mdp_bisim s t ->
  ptree_stable_head_rel eq mdp_encoding_candidate
    (mdp_encode_head s) (mdp_encode_head t).
Proof.
  intro H. destruct (mdp_bisim_unfold H) as [Hobs Hsteps].
  unfold ptree_stable_head_rel, mdp_encode_head. rewrite Hobs.
  constructor. intro a. constructor. exact (Hsteps a).
Qed.

Theorem mdp_bisim_peutt_sound s t :
  mdp_bisim s t -> peutt (MF := MF) eq (mdp_encode s) (mdp_encode t).
Proof.
  intro H. eapply peutt_coinduction with (sim := mdp_encoding_candidate).
  - intros u v Huv. destruct Huv as [u v Huv|mu nu Hlift].
    + eapply stable_hitting_match_of_hitting_lift;
        [apply mdp_encode_hitting|apply mdp_encode_hitting|].
      apply sem_lift_ret. apply mdp_encoding_head_related. exact Huv.
    + eapply stable_hitting_match_of_hitting_lift;
        [apply mdp_sample_hitting|apply mdp_sample_hitting|].
      eapply mixed_lift_bind; [exact Hlift|].
      intros x y Hxy. apply sem_lift_ret. apply mdp_encoding_head_related. exact Hxy.
  - constructor. exact H.
Qed.
End Behavior.
End Source.
