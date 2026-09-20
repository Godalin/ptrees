Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program Classes.RelationClasses.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import HeadTransition TreeTransition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Re-enter the RAW-TREE candidate at a successor stable head. This is
    neither head_bisim nor a whole-continuation stable_head_rel lifting.
    In particular the candidate itself decides how to compare Vis trees. *)
Definition stable_head_tree {E MN R} (h : stable_head E MN R) : ptree E MN R :=
  match h with FHRet r => Ret r | @FHVis _ _ _ _ e k => Vis e k end.

Definition tree_trans_head_rel {E MN R1 R2}
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (h1 : stable_head E MN R1) (h2 : stable_head E MN R2) : Prop :=
  sim (stable_head_tree h1) (stable_head_tree h2).

(** Bidirectional matching of measure witnesses, without choosing a
    representative or interpreting existence of a zero transition as
    enabledness. Used for all three observable components below. *)
Section MeasureMatch.
Context {MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}.
Context {A B : Type}.
Definition tree_measure_match (rel : A -> B -> Prop)
    (left : MF A -> Prop) (right : MF B -> Prop) : Prop :=
  (forall mu, left mu -> exists nu, right nu /\ sem_lift rel mu nu) /\
  (forall nu, right nu -> exists mu, left mu /\ sem_lift rel mu nu).

Lemma tree_measure_match_mono rel1 rel2 left right :
  (forall a b, rel1 a b -> rel2 a b) ->
  tree_measure_match rel1 left right -> tree_measure_match rel2 left right.
Proof.
  intros Hsub [Hf Hb]. split.
  - intros mu Hmu. destruct (Hf mu Hmu) as [nu [Hnu Hlift]].
    exists nu. split; [exact Hnu|]. eapply sem_lift_mono; eauto.
  - intros nu Hnu. destruct (Hb nu Hnu) as [mu [Hmu Hlift]].
    exists mu. split; [exact Hmu|]. eapply sem_lift_mono; eauto.
Qed.

(** Equality-coupling uniqueness suffices: no sem_lift-equality reflection
    is assumed when consuming arbitrary observation/transition witnesses. *)
Lemma tree_measure_match_witnesses rel left right mu nu :
  (forall nu1 nu2, right nu1 -> right nu2 -> sem_lift eq nu1 nu2) ->
  tree_measure_match rel left right -> left mu -> right nu -> sem_lift rel mu nu.
Proof.
  intros Hunique [Hf _] Hmu Hnu.
  destruct (Hf mu Hmu) as [nu' [Hnu' Hlift]].
  eapply sem_lift_mono; [|eapply sem_lift_comp; [exact Hlift|exact (Hunique _ _ Hnu' Hnu)]].
  intros a b [c [Hac ->]]. exact Hac.
Qed.

(** Construct a full match from convenient representatives. Equality
    couplings, rather than equality reflection, transport other witnesses. *)
Lemma tree_measure_match_of_witnesses rel left right mu nu :
  (forall mu1 mu2, left mu1 -> left mu2 -> sem_lift eq mu1 mu2) ->
  (forall nu1 nu2, right nu1 -> right nu2 -> sem_lift eq nu1 nu2) ->
  left mu -> right nu -> sem_lift rel mu nu -> tree_measure_match rel left right.
Proof.
  intros Hu Hv Hmu Hnu Hlift. split.
  - intros mu' Hmu'. exists nu. split; [exact Hnu|].
    eapply sem_lift_mono; [|eapply sem_lift_comp; [exact (Hu _ _ Hmu' Hmu)|exact Hlift]].
    intros a b [c [-> Hcb]]. exact Hcb.
  - intros nu' Hnu'. exists mu. split; [exact Hmu|].
    eapply sem_lift_mono; [|eapply sem_lift_comp; [exact Hlift|exact (Hv _ _ Hnu Hnu')]].
    intros a b [c [Hac ->]]. exact Hac.
Qed.
End MeasureMatch.

Section Bisimulation.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Local Notation tree1 := (ptree E MN R1).
Local Notation tree2 := (ptree E MN R2).

(** All three conjuncts are essential. Totalized action subkernels alone
    cannot distinguish distinct Empty_set events, or an offered event with
    divergent continuations from an event not offered at all. Current
    observations retain their original mass, just like the transitions.
    For homogeneous behavioral comparison, instantiate RR with equality. *)
Definition tree_trans_bisimF (sim : tree1 -> tree2 -> Prop) (t : tree1) (u : tree2) : Prop :=
  tree_measure_match RR (tree_return_observation (MF := MF) t)
    (tree_return_observation (MF := MF) u) /\
  tree_measure_match eq (tree_offered_event_observation (MF := MF) t)
    (tree_offered_event_observation (MF := MF) u) /\
  forall label, tree_measure_match (tree_trans_head_rel sim)
    (tree_trans (MF := MF) t label) (tree_trans (MF := MF) u label).

Lemma tree_trans_bisimF_mono sim1 sim2 :
  (forall t u, sim1 t u -> sim2 t u) ->
  forall t u, tree_trans_bisimF sim1 t u -> tree_trans_bisimF sim2 t u.
Proof.
  intros Hsub t u [Hret [Hevent Htrans]]. split; [exact Hret|].
  split; [exact Hevent|]. intro label.
  eapply tree_measure_match_mono; [|exact (Htrans label)].
  intros h k H. exact (Hsub _ _ H).
Qed.

Program Definition ftree_trans_bisim : mon (tree1 -> tree2 -> Prop) :=
  {| body := tree_trans_bisimF |}.
Next Obligation.
  intros sim1 sim2 Hsub t u H. eapply tree_trans_bisimF_mono; eauto.
Qed.

Definition tree_trans_bisim : tree1 -> tree2 -> Prop := gfp ftree_trans_bisim.
Lemma tree_trans_bisim_unfold t u :
  tree_trans_bisim t u -> tree_trans_bisimF tree_trans_bisim t u.
Proof. intro H. apply (gfp_pfp ftree_trans_bisim) in H. exact H. Qed.
Lemma tree_trans_bisim_fold t u :
  tree_trans_bisimF tree_trans_bisim t u -> tree_trans_bisim t u.
Proof. intro H. unfold tree_trans_bisim. apply (gfp_fp ftree_trans_bisim). exact H. Qed.
Theorem tree_trans_bisim_coinduction (sim : tree1 -> tree2 -> Prop)
    (Hpost : forall t u, sim t u -> tree_trans_bisimF sim t u) :
  forall t u, sim t u -> tree_trans_bisim t u.
Proof.
  intros t u Hsim. unfold tree_trans_bisim.
  eapply (@leq_gfp _ _ ftree_trans_bisim sim); eauto.
Qed.

Section Witnesses.
Context `{FB : @SemanticMeasureBindLaws MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Lemma tree_trans_bisim_return_observations t u mu nu :
  tree_trans_bisim t u -> tree_return_observation t mu ->
  tree_return_observation u nu -> sem_lift RR mu nu.
Proof.
  intros Hb Hmu Hnu. apply tree_trans_bisim_unfold in Hb.
  eapply tree_measure_match_witnesses; [|exact (proj1 Hb)|exact Hmu|exact Hnu].
  intros. eapply tree_head_observation_unique; eassumption.
Qed.
Lemma tree_trans_bisim_offered_observations t u mu nu :
  tree_trans_bisim t u -> tree_offered_event_observation t mu ->
  tree_offered_event_observation u nu -> sem_lift eq mu nu.
Proof.
  intros Hb Hmu Hnu. apply tree_trans_bisim_unfold in Hb.
  eapply tree_measure_match_witnesses; [|exact (proj1 (proj2 Hb))|exact Hmu|exact Hnu].
  intros. eapply tree_head_observation_unique; eassumption.
Qed.
Lemma tree_trans_bisim_transitions
    `{FCAE : @SemanticMeasureCouplingAELaws MF FI} t u label mu nu :
  tree_trans_bisim t u -> tree_trans t label mu -> tree_trans u label nu ->
  sem_lift (tree_trans_head_rel tree_trans_bisim) mu nu.
Proof.
  intros Hb Hmu Hnu. apply tree_trans_bisim_unfold in Hb.
  eapply tree_measure_match_witnesses; [|exact (proj2 (proj2 Hb) label)|exact Hmu|exact Hnu].
  intros. eapply tree_trans_unique; eassumption.
Qed.
End Witnesses.
End Bisimulation.

Section Reflexivity.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Context {R : Type}.

Theorem tree_trans_bisim_refl :
  Reflexive (@tree_trans_bisim E MN MF FI FC MX FO R R eq).
Proof.
  intro t. eapply tree_trans_bisim_coinduction with (sim := eq); [|reflexivity].
  intros t1 t2 ->. split.
  - split; intros out Hout; exists out; split; try exact Hout;
      apply sem_lift_refl; intro x; reflexivity.
  - split.
    + split; intros out Hout; exists out; split; try exact Hout;
        apply sem_lift_refl; intro x; reflexivity.
    + intro label. split; intros out Hout; exists out; split; try exact Hout;
        apply sem_lift_refl; intro h; reflexivity.
Qed.
End Reflexivity.
