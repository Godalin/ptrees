(** Role: Comparison semantics. Depends on canonical theory; not the canonical peutt relation or interpreter theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Program Morphisms.
From Coq.Relations Require Import Relation_Definitions.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel StableHittingRelation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A visible action includes both the dependent event and its response.
    It is not a marginal observation of a distribution of current heads. *)
Inductive obs_label (E : Type -> Type) : Type :=
  | Obs {X : Type} (e : E X) (x : X).
Arguments Obs {E X} _ _.

Section HeadTransition.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

(** State-based transition: the current head is already selected.  Only
    the continuation after the chosen response is run to its next stable
    distribution. Ret has no action. On probability backends targets are
    subdistributions; totality is deliberately not required here. *)
Inductive head_step {R} :
    stable_head E MN R -> obs_label E -> MF (stable_head E MN R) -> Prop :=
  | HeadStepVis {X} (e : E X) k x out :
      ptree_stable_hitting (MF := MF) (observe (k x)) out ->
      head_step (FHVis e k) (Obs e x) out.

Lemma head_step_vis_iff {R X} (e : E X) (k : X -> ptree E MN R) x out :
  head_step (FHVis e k) (Obs e x) out <->
  ptree_stable_hitting (MF := MF) (observe (k x)) out.
Proof.
  split; intro H.
  - dependent destruction H. exact H.
  - constructor. exact H.
Qed.

Lemma head_step_ret {R} (r : R) label out :
  ~ head_step (FHRet r) label out.
Proof. intro H. inversion H. Qed.

Lemma head_step_vis_label {R X} (e : E X) (k : X -> ptree E MN R) label out :
  head_step (FHVis e k) label out ->
  exists x, label = Obs e x /\
    ptree_stable_hitting (MF := MF) (observe (k x)) out.
Proof. intro H. dependent destruction H. eauto. Qed.

Lemma head_step_unique `{FOL : @SemanticOmegaLaws MF FI FO}
    {R} (h : stable_head E MN R) label out1 out2 :
  head_step h label out1 -> head_step h label out2 -> sem_eq out1 out2.
Proof.
  intros H1 H2. destruct H1. apply head_step_vis_iff in H2.
  eapply stable_hitting_unique; eassumption.
Qed.

Lemma head_step_exists
    `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
    `{FOL : @SemanticOmegaLaws MF FI FO}
    {R X} (e : E X) (k : X -> ptree E MN R) x :
  exists out, head_step (FHVis e k) (Obs e x) out.
Proof.
  destruct (stable_hitting_exists
    (@ptree_primitive_kernel E MN MF FI MX R) (observe (k x)))
    as [out Hout]. exists out. constructor. exact Hout.
Qed.

End HeadTransition.

Section HeadBisimulation.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Local Notation head1 := (stable_head E MN R1).
Local Notation head2 := (stable_head E MN R2).
Local Notation K R := (@ptree_primitive_kernel E MN MF FI MX R).

(** Reuse complete, bidirectional hitting matching. The recursive candidate
    relates successor HEADS, not the intermediate continuation trees. The
    dummy state relation is unused by the constant head lifting. This is
    witness-independent without choosing a canonical measure representative. *)
Definition head_successor_match (sim : head1 -> head2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) : Prop :=
  stable_hitting_match (K R1) (K R2) (fun _ => sim)
    (fun _ _ => False) (observe t1) (observe t2).

Lemma head_successor_match_mono sim1 sim2 :
  (forall h1 h2, sim1 h1 h2 -> sim2 h1 h2) ->
  forall t1 t2, head_successor_match sim1 t1 t2 ->
    head_successor_match sim2 t1 t2.
Proof.
  intros Hsub t1 t2 [Hf Hb]. split.
  - intros out1 H1. destruct (Hf out1 H1) as [out2 [H2 Hlift]].
    exists out2. split; [exact H2|]. eapply sem_lift_mono; eauto.
  - intros out2 H2. destruct (Hb out2 H2) as [out1 [H1 Hlift]].
    exists out1. split; [exact H1|]. eapply sem_lift_mono; eauto.
Qed.

(** Return values are compared by RR. Visible heads must expose the same
    event; for each response their successor distributions are coupled
    using the recursive candidate. There are no Tau/Prob/AST constructors. *)
Definition head_bisimF (sim : head1 -> head2 -> Prop) : head1 -> head2 -> Prop :=
  stable_head_rel RR (head_successor_match sim).

Lemma head_bisimF_mono sim1 sim2 :
  (forall h1 h2, sim1 h1 h2 -> sim2 h1 h2) ->
  forall h1 h2, head_bisimF sim1 h1 h2 -> head_bisimF sim2 h1 h2.
Proof.
  intro Hsub. apply stable_head_rel_mono.
  exact (head_successor_match_mono Hsub).
Qed.

Program Definition fhead_bisim : mon (head1 -> head2 -> Prop) :=
  {| body := head_bisimF |}.
Next Obligation.
  intros sim1 sim2 Hsub h1 h2 Hrel. eapply head_bisimF_mono; eauto.
Qed.

Definition head_bisim : head1 -> head2 -> Prop := gfp fhead_bisim.

Lemma head_bisim_unfold h1 h2 :
  head_bisim h1 h2 -> head_bisimF head_bisim h1 h2.
Proof. intro H. apply (gfp_pfp fhead_bisim) in H. exact H. Qed.

Lemma head_bisim_fold h1 h2 :
  head_bisimF head_bisim h1 h2 -> head_bisim h1 h2.
Proof. intro H. unfold head_bisim. apply (gfp_fp fhead_bisim). exact H. Qed.

Theorem head_bisim_coinduction (sim : head1 -> head2 -> Prop)
    (Hpost : forall h1 h2, sim h1 h2 -> head_bisimF sim h1 h2) :
  forall h1 h2, sim h1 h2 -> head_bisim h1 h2.
Proof.
  intros h1 h2 Hsim. unfold head_bisim.
  eapply (@leq_gfp _ _ fhead_bisim sim); eauto.
Qed.

Lemma head_bisim_ret_iff r1 r2 :
  head_bisim (FHRet r1) (FHRet r2) <-> RR r1 r2.
Proof.
  split; intro H.
  - apply head_bisim_unfold in H. inversion H. assumption.
  - apply head_bisim_fold. constructor. exact H.
Qed.

Lemma head_bisim_vis_iff {X} (e : E X)
    (k1 : X -> ptree E MN R1) (k2 : X -> ptree E MN R2) :
  head_bisim (FHVis e k1) (FHVis e k2) <->
  forall x, head_successor_match head_bisim (k1 x) (k2 x).
Proof.
  split; intro H.
  - apply head_bisim_unfold in H. dependent destruction H. exact H.
  - apply head_bisim_fold. constructor. exact H.
Qed.

Lemma head_bisim_ret_vis {X} r (e : E X) k :
  ~ head_bisim (FHRet r) (FHVis e k).
Proof. intro H. apply head_bisim_unfold in H. inversion H. Qed.

Lemma head_bisim_vis_ret {X} (e : E X) k r :
  ~ head_bisim (FHVis e k) (FHRet r).
Proof. intro H. apply head_bisim_unfold in H. inversion H. Qed.

(** Bisimilar states match the same dependent action, before coupling its
    successors. This does not average together distinct current states. *)
Theorem head_bisim_step_match h1 h2 label out1 :
  head_bisim h1 h2 -> head_step h1 label out1 ->
  exists out2, head_step h2 label out2 /\ sem_lift head_bisim out1 out2.
Proof.
  intros Hrel Hstep. apply head_bisim_unfold in Hrel.
  dependent destruction Hrel.
  - exfalso. eapply head_step_ret. exact Hstep.
  - dependent destruction Hstep.
    destruct (proj1 (H x) _ H0) as [out2 [Hhit Hlift]].
    exists out2. split; [constructor; exact Hhit|exact Hlift].
Qed.

(** At chosen complete hitting witnesses the generator is exactly the
    familiar per-action coupling formula. Only existing limit uniqueness
    and coupling properness are used; no node-to-frontier reflection law. *)
Theorem head_bisim_vis_hitting_iff
    `{FOL : @SemanticOmegaLaws MF FI FO}
    {X} (e : E X) (k1 : X -> ptree E MN R1) (k2 : X -> ptree E MN R2)
    (front1 : X -> MF head1) (front2 : X -> MF head2)
    (H1 : forall x, ptree_stable_hitting (MF := MF) (observe (k1 x)) (front1 x))
    (H2 : forall x, ptree_stable_hitting (MF := MF) (observe (k2 x)) (front2 x)) :
  head_bisim (FHVis e k1) (FHVis e k2) <->
  forall x, sem_lift head_bisim (front1 x) (front2 x).
Proof.
  rewrite head_bisim_vis_iff. split; intros H x.
  - exact (stable_hitting_match_hitting_lift (H x) (H1 x) (H2 x)).
  - eapply stable_hitting_match_of_hitting_lift; [apply H1|apply H2|apply H].
Qed.

(** The existential endpoint needs existence as well as uniqueness.  In
    particular, no assumed family of chosen H(k x) values is hidden here. *)
Theorem head_bisim_vis_exists_iff
    `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
    `{FOL : @SemanticOmegaLaws MF FI FO}
    {X} (e : E X) (k1 : X -> ptree E MN R1) (k2 : X -> ptree E MN R2) :
  head_bisim (FHVis e k1) (FHVis e k2) <->
  forall x, exists out1 out2,
    ptree_stable_hitting (MF := MF) (observe (k1 x)) out1 /\
    ptree_stable_hitting (MF := MF) (observe (k2 x)) out2 /\
    sem_lift head_bisim out1 out2.
Proof.
  rewrite head_bisim_vis_iff. split; intros H x.
  - destruct (stable_hitting_exists (K R1) (observe (k1 x))) as [out1 H1].
    destruct (proj1 (H x) out1 H1) as [out2 [H2 Hlift]].
    exists out1, out2. auto.
  - destruct (H x) as [out1 [out2 [H1 [H2 Hlift]]]].
    eapply stable_hitting_match_of_hitting_lift; eassumption.
Qed.

End HeadBisimulation.

(** The existing CoreLaws package already contains coupling converse and
    composition. Equivalence requires no additional gluing axiom, bind
    law, totality, finite support, or limit-existence assumption. *)
Section HeadBisimulationEquivalence.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R : Type}.
Local Notation hb := (@head_bisim E MN MF FI FC MX FO R R eq).

Theorem head_bisim_refl : Reflexive hb.
Proof.
  intro h. eapply head_bisim_coinduction with (sim := eq); [|reflexivity].
  intros h1 h2 ->. destruct h2 as [r|X e k]; constructor.
  - reflexivity.
  - intro x. split; intros out Hhit; exists out; split; [exact Hhit| |exact Hhit|];
      apply sem_lift_refl; intros head; reflexivity.
Qed.

Theorem head_bisim_sym : Symmetric hb.
Proof.
  intros h1 h2 H12.
  eapply head_bisim_coinduction with (sim := fun a b => hb b a); [|exact H12].
  intros a b Hab. apply head_bisim_unfold in Hab.
  dependent destruction Hab; constructor.
  - reflexivity.
  - intro x. destruct (H x) as [Hf Hb]. split.
    + intros out2 H2. destruct (Hb out2 H2) as [out1 [H1 Hl]].
      exists out1. split; [exact H1|]. apply sem_lift_sym. exact Hl.
    + intros out1 H1. destruct (Hf out1 H1) as [out2 [H2 Hl]].
      exists out2. split; [exact H2|]. apply sem_lift_sym. exact Hl.
Qed.

Theorem head_bisim_trans : Transitive hb.
Proof.
  intros h1 h2 h3 H12 H23.
  eapply head_bisim_coinduction with
    (sim := fun a c => exists b, hb a b /\ hb b c); [|eauto].
  intros a c [b [Hab Hbc]]. apply head_bisim_unfold in Hab, Hbc.
  dependent destruction Hab; dependent destruction Hbc; constructor.
  - congruence.
  - intro x. destruct (H x) as [H12f H12b]. destruct (H0 x) as [H23f H23b].
    split.
    + intros out1 H1. destruct (H12f out1 H1) as [out2 [H2 Hl12]].
      destruct (H23f out2 H2) as [out3 [H3 Hl23]].
      exists out3. split; [exact H3|]. eapply sem_lift_comp; eassumption.
    + intros out3 H3. destruct (H23b out3 H3) as [out2 [H2 Hl23]].
      destruct (H12b out2 H2) as [out1 [H1 Hl12]].
      exists out1. split; [exact H1|]. eapply sem_lift_comp; eassumption.
Qed.

#[global] Instance head_bisim_equivalence : Equivalence hb.
Proof. split; [apply head_bisim_refl|apply head_bisim_sym|apply head_bisim_trans]. Qed.

End HeadBisimulationEquivalence.
