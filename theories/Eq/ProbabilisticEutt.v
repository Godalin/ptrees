Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import
  PrimitiveStableHitting UnifiedFrontier UnifiedPWeak
  OperationalProbabilisticPTS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The canonical behavioral generator compares the complete
    subprobabilistic stable-hitting limits of two primitive kernels.  It has
    no syntax-specific, AST, bounded-execution, or one-sided silent case. *)
Section StableHittingBisimulation.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Hypothesis AR_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR sim1 a1 a2 -> AR sim2 a1 a2.

Definition stable_hitting_match (sim : S1 -> S2 -> Prop)
    (s1 : S1) (s2 : S2) : Prop :=
  (forall out1, stable_hitting_weak kernel1 s1 out1 ->
    exists out2, stable_hitting_weak kernel2 s2 out2 /\
      sem_lift (AR sim) out1 out2) /\
  (forall out2, stable_hitting_weak kernel2 s2 out2 ->
    exists out1, stable_hitting_weak kernel1 s1 out1 /\
      sem_lift (AR sim) out1 out2).

Lemma stable_hitting_match_mono sim1 sim2 :
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall s1 s2, stable_hitting_match sim1 s1 s2 ->
    stable_hitting_match sim2 s1 s2.
Proof.
  intros Hsim s1 s2 Hmatch.
  unfold stable_hitting_match in Hmatch |- *.
  destruct Hmatch as [Hforward Hbackward]. split.
  - intros out1 Hhit1. destruct (Hforward out1 Hhit1)
      as [out2 [Hhit2 Hlift]]. exists out2. split; [exact Hhit2|].
    eapply sem_lift_mono; [|exact Hlift]. exact (AR_mono Hsim).
  - intros out2 Hhit2. destruct (Hbackward out2 Hhit2)
      as [out1 [Hhit1 Hlift]]. exists out1. split; [exact Hhit1|].
    eapply sem_lift_mono; [|exact Hlift]. exact (AR_mono Hsim).
Qed.

Program Definition fstable_hitting_bisim : mon (S1 -> S2 -> Prop) :=
  {| body := stable_hitting_match |}.
Next Obligation.
  intros sim1 sim2 Hsub s1 s2 Hmatch.
  eapply stable_hitting_match_mono; eauto.
Qed.

Definition stable_hitting_bisim : S1 -> S2 -> Prop :=
  gfp fstable_hitting_bisim.

Lemma stable_hitting_bisim_unfold s1 s2 :
  stable_hitting_bisim s1 s2 ->
  stable_hitting_match stable_hitting_bisim s1 s2.
Proof.
  intro H. apply (gfp_pfp fstable_hitting_bisim) in H. exact H.
Qed.

Lemma stable_hitting_bisim_fold s1 s2 :
  stable_hitting_match stable_hitting_bisim s1 s2 ->
  stable_hitting_bisim s1 s2.
Proof.
  intro H. unfold stable_hitting_bisim.
  apply (gfp_fp fstable_hitting_bisim). exact H.
Qed.

End StableHittingBisimulation.

(** PTree instantiation.  PTree syntax occurs only in the primitive kernel
    and in the relation on stable Ret/Vis heads. *)
Section ProbabilisticEutt.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition ptree_stable_head_rel
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop) :
    frontier_head E MN R1 -> frontier_head E MN R2 -> Prop :=
  frontier_head_rel RR
    (fun t1 t2 => sim (observe t1) (observe t2)).

Lemma ptree_stable_head_rel_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2, ptree_stable_head_rel sim1 h1 h2 ->
    ptree_stable_head_rel sim2 h1 h2.
Proof.
  intro Hsim. apply frontier_head_rel_mono.
  intros t1 t2 Hrel. exact (Hsim _ _ Hrel).
Qed.

Definition probabilistic_eutt_state :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  @stable_hitting_bisim MF FI FC FO
    (ptree' E MN R1) (ptree' E MN R2)
    (frontier_head E MN R1) (frontier_head E MN R2)
    (@ptree_primitive_kernel E MN MF FI MX R1)
    (@ptree_primitive_kernel E MN MF FI MX R2)
    ptree_stable_head_rel ptree_stable_head_rel_mono.

Definition probabilistic_eutt
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) : Prop :=
  probabilistic_eutt_state (observe t1) (observe t2).

Definition pbisim := probabilistic_eutt.

Lemma probabilistic_eutt_unfold t1 t2 :
  probabilistic_eutt t1 t2 ->
  stable_hitting_match
    (@ptree_primitive_kernel E MN MF FI MX R1)
    (@ptree_primitive_kernel E MN MF FI MX R2)
    ptree_stable_head_rel probabilistic_eutt_state
    (observe t1) (observe t2).
Proof.
  exact (stable_hitting_bisim_unfold (s1 := observe t1)
    (s2 := observe t2)).
Qed.

Lemma probabilistic_eutt_fold t1 t2 :
  stable_hitting_match
    (@ptree_primitive_kernel E MN MF FI MX R1)
    (@ptree_primitive_kernel E MN MF FI MX R2)
    ptree_stable_head_rel probabilistic_eutt_state
    (observe t1) (observe t2) ->
  probabilistic_eutt t1 t2.
Proof.
  exact (stable_hitting_bisim_fold (s1 := observe t1)
    (s2 := observe t2)).
Qed.

End ProbabilisticEutt.
