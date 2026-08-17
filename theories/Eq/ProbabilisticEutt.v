Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coq Require Import Logic.ClassicalChoice Morphisms.
From Coinduction Require Import all.
From mathcomp Require Import ssreflect.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import
  PrimitiveStableHitting UnifiedFrontier
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

(** Generic corecursive proof rule.  A structured or program-specific
    relation need only be closed by matching the complete stable-hitting
    limits.  Syntax such as [Iter] belongs in the candidate [sim] (or in a
    certificate used to establish [Hpost]), never in the canonical
    behavioral generator. *)
Theorem stable_hitting_bisim_coinduction
    (sim : S1 -> S2 -> Prop)
    (Hpost : forall s1 s2, sim s1 s2 ->
      stable_hitting_match sim s1 s2) :
  forall s1 s2, sim s1 s2 -> stable_hitting_bisim s1 s2.
Proof.
  intros s1 s2 Hsim. unfold stable_hitting_bisim.
  eapply (@leq_gfp _ _ fstable_hitting_bisim sim); eauto.
Qed.

End StableHittingBisimulation.

Section StableHittingMatchEndpoint.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.

(** Generator-level endpoint rule.  A pair of complete hitting witnesses and
    one coupling between them determine the full bidirectional match: all
    other complete witnesses are transported to these by uniqueness. *)
Lemma stable_hitting_match_of_hitting_lift
    (sim : S1 -> S2 -> Prop) s1 s2 out1 out2 :
  stable_hitting_weak kernel1 s1 out1 ->
  stable_hitting_weak kernel2 s2 out2 ->
  sem_lift (AR sim) out1 out2 ->
  stable_hitting_match kernel1 kernel2 AR sim s1 s2.
Proof.
  intros Hhit1 Hhit2 Hlift. unfold stable_hitting_match. split.
  - intros out1' Hhit1'. exists out2. split; [exact Hhit2|].
    eapply sem_lift_proper_l; [|exact Hlift].
    eapply stable_hitting_weak_unique; [exact Hhit1|exact Hhit1'].
  - intros out2' Hhit2'. exists out1. split; [exact Hhit1|].
    eapply sem_lift_proper_r; [|exact Hlift].
    eapply stable_hitting_weak_unique; [exact Hhit2|exact Hhit2'].
Qed.

End StableHittingMatchEndpoint.

Section StableHittingBisimulationReflexivity.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).
Variable AR : (S -> S -> Prop) -> A -> A -> Prop.
Hypothesis AR_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR sim1 a1 a2 -> AR sim2 a1 a2.
Hypothesis AR_refl : forall sim, Reflexive sim -> Reflexive (AR sim).

Theorem stable_hitting_bisim_refl :
  Reflexive (@stable_hitting_bisim MF FI FC FO S S A A
    kernel kernel AR AR_mono).
Proof.
  intro state. revert state. unfold stable_hitting_bisim.
  coinduction CH CIH. intro state.
  unfold stable_hitting_match. split.
  - intros out Hhit. exists out. split; [exact Hhit|].
    apply sem_lift_refl. apply AR_refl. exact CIH.
  - intros out Hhit. exists out. split; [exact Hhit|].
    apply sem_lift_refl. apply AR_refl. exact CIH.
Qed.

End StableHittingBisimulationReflexivity.

Section StableHittingBisimulationConverse.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 A1 A2 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable AR12 : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Variable AR21 : (S2 -> S1 -> Prop) -> A2 -> A1 -> Prop.
Hypothesis AR12_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR12 sim1 a1 a2 -> AR12 sim2 a1 a2.
Hypothesis AR21_mono : forall sim1 sim2,
  (forall s2 s1, sim1 s2 s1 -> sim2 s2 s1) ->
  forall a2 a1, AR21 sim1 a2 a1 -> AR21 sim2 a2 a1.
Hypothesis AR_converse : forall sim a1 a2,
  AR12 sim a1 a2 ->
  AR21 (fun s2 s1 => sim s1 s2) a2 a1.

Theorem stable_hitting_bisim_converse : forall s1 s2,
  @stable_hitting_bisim MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 ->
  @stable_hitting_bisim MF FI FC FO S2 S1 A2 A1
    kernel2 kernel1 AR21 AR21_mono s2 s1.
Proof.
  unfold stable_hitting_bisim at 2. coinduction CH CIH.
  intros s1 s2 Hrel.
  pose proof (@stable_hitting_bisim_unfold MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 Hrel) as Hmatch.
  unfold stable_hitting_match in Hmatch |- *.
  destruct Hmatch as [Hforward Hbackward]. split.
  - intros out2 Hhit2. destruct (Hbackward out2 Hhit2)
      as [out1 [Hhit1 Hlift]]. exists out1. split; [exact Hhit1|].
    apply sem_lift_sym in Hlift. eapply sem_lift_mono; [|exact Hlift].
    intros a2 a1 Har. eapply AR21_mono.
    + intros x2 x1 H12. exact (CIH _ _ H12).
    + exact (AR_converse Har).
  - intros out1 Hhit1. destruct (Hforward out1 Hhit1)
      as [out2 [Hhit2 Hlift]]. exists out2. split; [exact Hhit2|].
    apply sem_lift_sym in Hlift. eapply sem_lift_mono; [|exact Hlift].
    intros a2 a1 Har. eapply AR21_mono.
    + intros x2 x1 H12. exact (CIH _ _ H12).
    + exact (AR_converse Har).
Qed.

End StableHittingBisimulationConverse.

Section StableHittingBisimulationComposition.
Context {MF : Type -> Type}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S1 S2 S3 A1 A2 A3 : Type}.
Variable kernel1 : S1 -> MF (stable_target S1 A1).
Variable kernel2 : S2 -> MF (stable_target S2 A2).
Variable kernel3 : S3 -> MF (stable_target S3 A3).
Variable AR12 : (S1 -> S2 -> Prop) -> A1 -> A2 -> Prop.
Variable AR23 : (S2 -> S3 -> Prop) -> A2 -> A3 -> Prop.
Variable AR13 : (S1 -> S3 -> Prop) -> A1 -> A3 -> Prop.
Hypothesis AR12_mono : forall sim1 sim2,
  (forall s1 s2, sim1 s1 s2 -> sim2 s1 s2) ->
  forall a1 a2, AR12 sim1 a1 a2 -> AR12 sim2 a1 a2.
Hypothesis AR23_mono : forall sim1 sim2,
  (forall s2 s3, sim1 s2 s3 -> sim2 s2 s3) ->
  forall a2 a3, AR23 sim1 a2 a3 -> AR23 sim2 a2 a3.
Hypothesis AR13_mono : forall sim1 sim2,
  (forall s1 s3, sim1 s1 s3 -> sim2 s1 s3) ->
  forall a1 a3, AR13 sim1 a1 a3 -> AR13 sim2 a1 a3.

Local Definition HB12 := @stable_hitting_bisim MF FI FC FO
  S1 S2 A1 A2 kernel1 kernel2 AR12 AR12_mono.
Local Definition HB23 := @stable_hitting_bisim MF FI FC FO
  S2 S3 A2 A3 kernel2 kernel3 AR23 AR23_mono.
Local Definition HB13 := @stable_hitting_bisim MF FI FC FO
  S1 S3 A1 A3 kernel1 kernel3 AR13 AR13_mono.

Hypothesis AR_comp : forall sim12 sim23 sim13,
  (forall s1 s3, (exists s2, sim12 s1 s2 /\ sim23 s2 s3) ->
    sim13 s1 s3) ->
  forall a1 a3, (exists a2, AR12 sim12 a1 a2 /\ AR23 sim23 a2 a3) ->
    AR13 sim13 a1 a3.

Theorem stable_hitting_bisim_compose_rel : forall s1 s3,
  (exists s2, HB12 s1 s2 /\ HB23 s2 s3) -> HB13 s1 s3.
Proof.
  unfold HB13. unfold stable_hitting_bisim at 1. coinduction CH CIH.
  intros s1 s3 [s2 [H12 H23]].
  pose proof (@stable_hitting_bisim_unfold MF FI FC FO S1 S2 A1 A2
    kernel1 kernel2 AR12 AR12_mono s1 s2 H12) as HM12.
  pose proof (@stable_hitting_bisim_unfold MF FI FC FO S2 S3 A2 A3
    kernel2 kernel3 AR23 AR23_mono s2 s3 H23) as HM23.
  unfold stable_hitting_match in HM12, HM23 |- *.
  destruct HM12 as [H12f H12b]. destruct HM23 as [H23f H23b]. split.
  - intros out1 Hhit1. destruct (H12f out1 Hhit1)
      as [out2 [Hhit2 Hl12]].
    destruct (H23f out2 Hhit2) as [out3 [Hhit3 Hl23]].
    exists out3. split; [exact Hhit3|].
    pose proof (sem_lift_comp Hl12 Hl23) as Hcomp.
    eapply sem_lift_mono; [|exact Hcomp].
    intros a1 a3 [a2 [Ha12 Ha23]]. eapply AR_comp.
    + intros x1 x3 [x2 [Hx12 Hx23]].
      exact (CIH _ _ (ex_intro _ x2 (conj Hx12 Hx23))).
    + eauto.
  - intros out3 Hhit3. destruct (H23b out3 Hhit3)
      as [out2 [Hhit2 Hl23]].
    destruct (H12b out2 Hhit2) as [out1 [Hhit1 Hl12]].
    exists out1. split; [exact Hhit1|].
    pose proof (sem_lift_comp Hl12 Hl23) as Hcomp.
    eapply sem_lift_mono; [|exact Hcomp].
    intros a1 a3 [a2 [Ha12 Ha23]]. eapply AR_comp.
    + intros x1 x3 [x2 [Hx12 Hx23]].
      exact (CIH _ _ (ex_intro _ x2 (conj Hx12 Hx23))).
    + eauto.
Qed.

Corollary stable_hitting_bisim_compose : forall s1 s2 s3,
  HB12 s1 s2 -> HB23 s2 s3 -> HB13 s1 s3.
Proof. intros s1 s2 s3 H12 H23. apply stable_hitting_bisim_compose_rel. eauto. Qed.

End StableHittingBisimulationComposition.

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

(** PTree-facing specialization of the generic corecursive rule. *)
Theorem probabilistic_eutt_coinduction
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop)
    (Hpost : forall s1 s2, sim s1 s2 ->
      stable_hitting_match
        (@ptree_primitive_kernel E MN MF FI MX R1)
        (@ptree_primitive_kernel E MN MF FI MX R2)
        ptree_stable_head_rel
        sim s1 s2) :
  forall t1 t2, sim (observe t1) (observe t2) ->
    probabilistic_eutt t1 t2.
Proof.
  intros t1 t2 Hsim.
  eapply stable_hitting_bisim_coinduction; eauto.
Qed.

(** Coinduction up to the canonical equivalence.  Recursive obligations may
    either remain in the user candidate or close with an equivalence that has
    already been established.  This is the basic sound guarded-context API;
    it changes only the proof principle, never the behavioral generator. *)
Theorem probabilistic_eutt_coinduction_upto
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop)
    (Hpost : forall s1 s2, sim s1 s2 ->
      stable_hitting_match
        (@ptree_primitive_kernel E MN MF FI MX R1)
        (@ptree_primitive_kernel E MN MF FI MX R2)
        ptree_stable_head_rel
        (fun x1 x2 => sim x1 x2 \/ probabilistic_eutt_state x1 x2)
        s1 s2) :
  forall t1 t2, sim (observe t1) (observe t2) ->
    probabilistic_eutt t1 t2.
Proof.
  intros t1 t2 Hsim.
  eapply probabilistic_eutt_coinduction with
    (sim := fun x1 x2 => sim x1 x2 \/ probabilistic_eutt_state x1 x2).
  - intros s1 s2 [Hcandidate|Hknown].
    + exact (Hpost _ _ Hcandidate).
    + apply stable_hitting_bisim_unfold in Hknown.
      eapply stable_hitting_match_mono.
      * apply ptree_stable_head_rel_mono.
      * intros x1 x2 Hrel. right. exact Hrel.
      * exact Hknown.
  - left. exact Hsim.
Qed.

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

(** Public notation for the canonical behavioral equivalence.  It lives in
    [type_scope], matching ITree's [≈] convention while retaining a visible
    probabilistic subscript.  The bracketed form supports heterogeneous
    return relations. *)
Notation "t ≈ₚ[ RR ] u" := (probabilistic_eutt RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.
Notation "t ≈ₚ u" := (probabilistic_eutt eq t u)
  (at level 70, no associativity) : type_scope.

Section ProbabilisticEuttEndpoint.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

(** Extensional proof rule: implementations may have unrelated finite
    schedules (including bounded versus unbounded ones); only their complete
    stable-hitting limits are coupled. *)
Lemma probabilistic_eutt_of_hitting_lift
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
  sem_lift (ptree_stable_head_rel RR
    (@probabilistic_eutt_state E MN MF FI FC MX FO R1 R2 RR)) out1 out2 ->
  probabilistic_eutt RR t1 t2.
Proof.
  intros Hhit1 Hhit2 Hlift. apply probabilistic_eutt_fold.
  eapply stable_hitting_match_of_hitting_lift; eauto.
Qed.

Lemma probabilistic_eutt_preserves_hitting_mass
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  probabilistic_eutt RR t1 t2 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
  sem_same_mass out1 out2.
Proof.
  intros Hrel Hhit1 Hhit2.
  apply probabilistic_eutt_unfold in Hrel.
  destruct Hrel as [Hforward _].
  destruct (Hforward out1 Hhit1) as [out2' [Hhit2' Hlift]].
  apply sem_lift_same_mass in Hlift.
  unfold sem_same_mass in Hlift |- *.
  eapply sem_lift_proper_r; [|exact Hlift].
  eapply stable_hitting_weak_unique; [exact Hhit2'|exact Hhit2].
Qed.

Lemma probabilistic_eutt_hitting_lift
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  probabilistic_eutt RR t1 t2 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
  sem_lift (ptree_stable_head_rel RR
    (@probabilistic_eutt_state E MN MF FI FC MX FO R1 R2 RR)) out1 out2.
Proof.
  intros Hrel Hhit1 Hhit2. apply probabilistic_eutt_unfold in Hrel.
  destruct Hrel as [Hforward _].
  destruct (Hforward out1 Hhit1) as [out2' [Hhit2' Hlift]].
  eapply sem_lift_proper_r; [|exact Hlift].
  eapply stable_hitting_weak_unique; eassumption.
Qed.

Corollary probabilistic_eutt_not_of_mass_mismatch
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
  ~ sem_same_mass out1 out2 ->
  ~ probabilistic_eutt RR t1 t2.
Proof.
  intros Hhit1 Hhit2 Hmass Hrel. apply Hmass.
  eapply probabilistic_eutt_preserves_hitting_mass; eassumption.
Qed.

End ProbabilisticEuttEndpoint.

Section ProbabilisticEuttProbCongruence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

Lemma stable_hitting_weak_prob {R X}
    (mu : MN X) (k : X -> ptree E MN R)
    (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
  sem_ae mu Good ->
  (forall x, Good x -> stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (k x)) (front x)) ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (Prob mu k)) (mixed_bind mu front).
Proof.
  intros Hae Hfront. change (operational_weak (MF := MF)
    (observe (Prob mu k)) (mixed_bind mu front)).
  eapply operational_weak_prob; eassumption.
Qed.

Theorem probabilistic_eutt_prob {R X1 X2}
    (XR : X1 -> X2 -> Prop) (mu1 : MN X1) (mu2 : MN X2)
    (k1 : X1 -> ptree E MN R) (k2 : X2 -> ptree E MN R) :
  sem_lift XR mu1 mu2 ->
  (forall x1 x2, XR x1 x2 -> probabilistic_eutt eq (k1 x1) (k2 x2)) ->
  probabilistic_eutt eq (Prob mu1 k1) (Prob mu2 k2).
Proof.
  intros Hmu Hk.
  assert (Hexists1 : forall x1, exists out,
      stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX R)
        (observe (k1 x1)) out).
  { intro x1. apply stable_hitting_weak_exists. }
  assert (Hexists2 : forall x2, exists out,
      stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX R)
        (observe (k2 x2)) out).
  { intro x2. apply stable_hitting_weak_exists. }
  destruct (choice _ Hexists1) as [front1 Hfront1].
  destruct (choice _ Hexists2) as [front2 Hfront2].
  eapply probabilistic_eutt_of_hitting_lift.
  - eapply stable_hitting_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. exact (Hfront1 x).
  - eapply stable_hitting_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. exact (Hfront2 x).
  - eapply mixed_lift_bind; [exact Hmu|].
    intros x1 x2 Hx.
    eapply probabilistic_eutt_hitting_lift;
      [exact (Hk x1 x2 Hx)|exact (Hfront1 x1)|exact (Hfront2 x2)].
Qed.

End ProbabilisticEuttProbCongruence.

Section PTreeStableHittingEquations.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma stable_hitting_weak_ret {R} (r : R) :
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) (RetF r)
    (sem_ret (FHRet r)).
Proof.
  unfold stable_hitting_weak.
  eapply sem_lub_chain_proper with
      (chain := fun _ => sem_ret (FHRet r)).
  - intro fuel. apply sem_eq_sym.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE. apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.

Lemma stable_hitting_weak_vis {R X} (e : E X)
    (k : X -> ptree E MN R) :
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R) (VisF e k)
    (sem_ret (FHVis e k)).
Proof.
  unfold stable_hitting_weak.
  eapply sem_lub_chain_proper with
      (chain := fun _ => sem_ret (FHVis e k)).
  - intro fuel. apply sem_eq_sym.
    eapply sem_eq_trans; [apply sem_bind_ret_l|].
    rewrite stable_target_stableE. apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.

(** A common visible guard closes one native bisimulation step.  Besides the
    continuation obligation, this rule hides the complete-hitting witnesses,
    their uniqueness transport, and the Dirac coupling at the visible head. *)
Lemma stable_hitting_match_vis {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree' E MN R1 -> ptree' E MN R2 -> Prop)
    {X : Type} (e : E X)
    (k1 : X -> ptree E MN R1) (k2 : X -> ptree E MN R2) :
  (forall x, sim (observe (k1 x)) (observe (k2 x))) ->
  stable_hitting_match
    (@ptree_primitive_kernel E MN MF FI MX R1)
    (@ptree_primitive_kernel E MN MF FI MX R2)
    (@ptree_stable_head_rel E MN R1 R2 RR) sim
    (VisF e k1) (VisF e k2).
Proof.
  intro Hk. unfold stable_hitting_match. split.
  - intros out1 Hhit1.
    exists (sem_ret (FHVis e k2)). split.
    + apply stable_hitting_weak_vis.
    + eapply sem_lift_proper_l.
      * eapply stable_hitting_weak_unique;
          [exact (stable_hitting_weak_vis e k1)|exact Hhit1].
      * apply sem_lift_ret. apply FHRVis. exact Hk.
  - intros out2 Hhit2.
    exists (sem_ret (FHVis e k1)). split.
    + apply stable_hitting_weak_vis.
    + eapply sem_lift_proper_r.
      * eapply stable_hitting_weak_unique;
          [exact (stable_hitting_weak_vis e k2)|exact Hhit2].
      * apply sem_lift_ret. apply FHRVis. exact Hk.
Qed.

Lemma stable_hitting_tau_chain {R} (t : ptree E MN R) fuel :
  sem_eq
    (stable_hitting_approx
      (@ptree_primitive_kernel E MN MF FI MX R) fuel (TauF t))
    (sem_zero_prefix (fun n => stable_hitting_approx
      (@ptree_primitive_kernel E MN MF FI MX R) n (observe t)) fuel).
Proof.
  unfold stable_hitting_approx, ptree_primitive_kernel.
  rewrite sem_bind_ret_l.
  destruct fuel; [apply sem_eq_refl|apply sem_eq_refl].
Qed.

Theorem stable_hitting_weak_tau_iff {R} (t : ptree E MN R) out :
  stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) (TauF t) out <->
  stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R) (observe t) out.
Proof.
  unfold stable_hitting_weak. split; intro Hhit.
  - apply (proj2 (sem_lub_zero_prefix
      (fun n => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF FI MX R) n (observe t)) out)).
    eapply sem_lub_chain_proper; [|exact Hhit].
    intro fuel. exact (stable_hitting_tau_chain t fuel).
  - eapply sem_lub_chain_proper with
      (chain := sem_zero_prefix (fun n => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF FI MX R) n (observe t))).
    + intro fuel. apply sem_eq_sym. exact (stable_hitting_tau_chain t fuel).
    + apply (proj1 (sem_lub_zero_prefix
        (fun n => stable_hitting_approx
          (@ptree_primitive_kernel E MN MF FI MX R) n (observe t)) out)).
      exact Hhit.
Qed.

End PTreeStableHittingEquations.

Section PTreeStableHittingBind.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

(** Stable hitting composes with bind under the local global/diagonal fuel
    cofinality obligation.  This theorem mentions neither behavioral
    relation nor structured frontier derivations. *)
Theorem stable_hitting_weak_bind {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    hs (front : A -> MF (frontier_head E MN R)) :
  operational_bind_cofinal (MF := MF) t k ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX A) (observe t) hs ->
  (forall a, stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (k a)) (front a)) ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R)
    (observe (PTree.bind t k))
    (sem_bind hs (frontier_head_bind_front k front)).
Proof.
  intros Hcofinal Hsource Hfront.
  eapply operational_weak_bind.
  - exact Hcofinal.
  - exact Hsource.
  - exact Hfront.
Qed.

End PTreeStableHittingBind.

Section ProbabilisticEuttEquivalence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R : Type}.

Lemma ptree_stable_head_rel_refl
    (sim : ptree' E MN R -> ptree' E MN R -> Prop) :
  Reflexive sim -> Reflexive (@ptree_stable_head_rel E MN R R eq sim).
Proof.
  intros Hsim [r|X e k].
  - constructor. reflexivity.
  - constructor. intro x. exact (Hsim (observe (k x))).
Qed.

Lemma ptree_stable_head_rel_converse
    (sim : ptree' E MN R -> ptree' E MN R -> Prop) :
  forall h1 h2, ptree_stable_head_rel eq sim h1 h2 ->
    ptree_stable_head_rel eq (fun s2 s1 => sim s1 s2) h2 h1.
Proof.
  intros h1 h2 Hrel. dependent destruction Hrel.
  - constructor. reflexivity.
  - constructor. intro x. auto.
Qed.

Lemma ptree_stable_head_rel_compose
    (sim12 sim23 sim13 : ptree' E MN R -> ptree' E MN R -> Prop)
    (Hsim : forall s1 s3, (exists s2, sim12 s1 s2 /\ sim23 s2 s3) ->
      sim13 s1 s3) :
  forall h1 h3,
    (exists h2, ptree_stable_head_rel eq sim12 h1 h2 /\
      ptree_stable_head_rel eq sim23 h2 h3) ->
    ptree_stable_head_rel eq sim13 h1 h3.
Proof.
  intros h1 h3 [h2 [H12 H23]].
  dependent destruction H12; dependent destruction H23.
  - constructor. congruence.
  - constructor. intro x. apply Hsim. eauto.
Qed.

Theorem probabilistic_eutt_state_refl :
  Reflexive (@probabilistic_eutt_state E MN MF FI FC MX FO R R eq).
Proof.
  unfold probabilistic_eutt_state.
  apply stable_hitting_bisim_refl.
  intros sim Hsim. exact (ptree_stable_head_rel_refl Hsim).
Qed.

Theorem probabilistic_eutt_refl :
  Reflexive (@probabilistic_eutt E MN MF FI FC MX FO R R eq).
Proof.
  intro t. apply probabilistic_eutt_state_refl.
Qed.

Theorem probabilistic_eutt_sym :
  Symmetric (@probabilistic_eutt E MN MF FI FC MX FO R R eq).
Proof.
  intros t1 t2 Hrel.
  unfold probabilistic_eutt, probabilistic_eutt_state in Hrel |- *.
  eapply stable_hitting_bisim_converse; [|exact Hrel].
  intros sim a1 a2 Har. exact (ptree_stable_head_rel_converse Har).
Qed.

Theorem probabilistic_eutt_trans :
  Transitive (@probabilistic_eutt E MN MF FI FC MX FO R R eq).
Proof.
  intros t1 t2 t3 H12 H23.
  unfold probabilistic_eutt, probabilistic_eutt_state in H12, H23 |- *.
  eapply stable_hitting_bisim_compose; [|exact H12|exact H23].
  intros sim12 sim23 sim13 Hsim a1 a3 Hheads.
  exact (ptree_stable_head_rel_compose Hsim Hheads).
Qed.

Global Instance probabilistic_eutt_equivalence :
  Equivalence (@probabilistic_eutt E MN MF FI FC MX FO R R eq) :=
  {| Equivalence_Reflexive := probabilistic_eutt_refl;
     Equivalence_Symmetric := probabilistic_eutt_sym;
     Equivalence_Transitive := probabilistic_eutt_trans |}.

End ProbabilisticEuttEquivalence.

Section ProbabilisticEuttStructuralLaws.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}.

Lemma probabilistic_eutt_tau_l {R} (t : ptree E MN R) :
  @probabilistic_eutt E MN MF FI FC MX FO R R eq (Tau t) t.
Proof.
  apply probabilistic_eutt_fold. unfold stable_hitting_match. split.
  - intros out Htau. exists out. split.
    + apply (proj1 (stable_hitting_weak_tau_iff t out)). exact Htau.
    + apply sem_lift_refl. apply ptree_stable_head_rel_refl.
      exact probabilistic_eutt_state_refl.
  - intros out Ht. exists out. split.
    + apply (proj2 (stable_hitting_weak_tau_iff t out)). exact Ht.
    + apply sem_lift_refl. apply ptree_stable_head_rel_refl.
      exact probabilistic_eutt_state_refl.
Qed.

Lemma probabilistic_eutt_tau_r {R} (t : ptree E MN R) :
  @probabilistic_eutt E MN MF FI FC MX FO R R eq t (Tau t).
Proof.
  apply probabilistic_eutt_sym. apply probabilistic_eutt_tau_l.
Qed.

Lemma probabilistic_eutt_ret {R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 ->
  @probabilistic_eutt E MN MF FI FC MX FO R1 R2 RR (Ret r1) (Ret r2).
Proof.
  intro Hrr. apply probabilistic_eutt_fold.
  unfold stable_hitting_match. split.
  - intros out1 Hhit1. exists (sem_ret (FHRet r2)). split.
    + apply stable_hitting_weak_ret.
    + eapply sem_lift_proper_l.
      * eapply stable_hitting_weak_unique;
          [apply stable_hitting_weak_ret|exact Hhit1].
      * apply sem_lift_ret. constructor. exact Hrr.
  - intros out2 Hhit2. exists (sem_ret (FHRet r1)). split.
    + apply stable_hitting_weak_ret.
    + eapply sem_lift_proper_r.
      * eapply stable_hitting_weak_unique;
          [apply stable_hitting_weak_ret|exact Hhit2].
      * apply sem_lift_ret. constructor. exact Hrr.
Qed.

Lemma probabilistic_eutt_vis {R1 R2 X} (RR : R1 -> R2 -> Prop)
    (e : E X) (k1 : X -> ptree E MN R1) (k2 : X -> ptree E MN R2) :
  (forall x, @probabilistic_eutt E MN MF FI FC MX FO R1 R2 RR
      (k1 x) (k2 x)) ->
  @probabilistic_eutt E MN MF FI FC MX FO R1 R2 RR
    (Vis e k1) (Vis e k2).
Proof.
  intro Hk. apply probabilistic_eutt_fold.
  apply stable_hitting_match_vis. exact Hk.
Qed.

#[global] Instance probabilistic_eutt_tau_Proper {R} :
  Proper (probabilistic_eutt eq ==> probabilistic_eutt eq)
    (fun t : ptree E MN R => Tau t).
Proof.
  intros t1 t2 Ht. eapply probabilistic_eutt_trans.
  - apply probabilistic_eutt_tau_l.
  - eapply probabilistic_eutt_trans; [exact Ht|].
    apply probabilistic_eutt_tau_r.
Qed.

#[global] Instance probabilistic_eutt_vis_Proper {R X} (e : E X) :
  Proper (pointwise_relation X (probabilistic_eutt eq) ==>
    probabilistic_eutt eq)
    (fun k : X -> ptree E MN R => Vis e k).
Proof.
  intros k1 k2 Hk. apply probabilistic_eutt_vis. exact Hk.
Qed.

End ProbabilisticEuttStructuralLaws.

Section ProbabilisticEuttProbRewriting.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.

(** Transport a sampling node across an extensional coupling of its node
    measures.  This is the canonical measure-equivalence rewriting rule;
    list or representation equality is neither required nor exposed. *)
Corollary probabilistic_eutt_prob_measure {R X}
    (mu1 mu2 : MN X) (k : X -> ptree E MN R) :
  sem_lift eq mu1 mu2 ->
  probabilistic_eutt eq (Prob mu1 k) (Prob mu2 k).
Proof.
  intro Hmu. eapply probabilistic_eutt_prob with (XR := eq).
  - exact Hmu.
  - intros x1 x2 ->. apply probabilistic_eutt_refl.
Qed.

(** Dirac elimination is available exactly for backends whose two-level
    semantic quotient declares node return to be a mixed-bind left unit. *)
Theorem probabilistic_eutt_prob_ret {R X}
    `{MU : @MixedMeasureUnitLaws MN MF NI FI MX}
    (x : X) (k : X -> ptree E MN R) :
  probabilistic_eutt eq (Prob (sem_ret x) k) (k x).
Proof.
  assert (Hexists : forall y, exists out,
      stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX R)
        (observe (k y)) out).
  { intro y. apply stable_hitting_weak_exists. }
  destruct (choice _ Hexists) as [front Hfront].
  eapply probabilistic_eutt_of_hitting_lift.
  - eapply stable_hitting_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros y _. exact (Hfront y).
  - exact (Hfront x).
  - eapply sem_lift_mono.
    + intros h1 h2 ->. destruct h2.
      * constructor. reflexivity.
      * constructor. intro y. apply probabilistic_eutt_refl.
    + apply mixed_bind_ret_l.
Qed.

(** Flatten two consecutive sampling nodes when node-level Kleisli
    composition is compatible with mixed binding into behavioral measures. *)
Theorem probabilistic_eutt_prob_flatten {R X Y}
    `{NB : @MixedMeasureNodeBindLaws MN MF NI FI MX}
    (mu : MN X) (h : X -> MN Y) (k : Y -> ptree E MN R) :
  probabilistic_eutt eq
    (Prob mu (fun x => Prob (h x) k))
    (Prob (sem_bind mu h) k).
Proof.
  assert (Hexists : forall y, exists out,
      stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX R)
        (observe (k y)) out).
  { intro y. apply stable_hitting_weak_exists. }
  destruct (choice _ Hexists) as [front Hfront].
  eapply probabilistic_eutt_of_hitting_lift.
  - eapply stable_hitting_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. eapply stable_hitting_weak_prob with
          (Good := fun _ => True).
      * apply sem_ae_true.
      * intros y _. exact (Hfront y).
  - eapply stable_hitting_weak_prob with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros y _. exact (Hfront y).
  - eapply sem_lift_mono.
    + intros h1 h2 ->. destruct h2.
      * constructor. reflexivity.
      * constructor. intro z. apply probabilistic_eutt_refl.
    + apply mixed_bind_node_assoc.
Qed.

#[global] Instance probabilistic_eutt_prob_Proper {R X} (mu : MN X) :
  Proper (pointwise_relation X (probabilistic_eutt eq) ==>
    probabilistic_eutt eq) (fun k : X -> ptree E MN R => Prob mu k).
Proof.
  intros k1 k2 Hk. eapply probabilistic_eutt_prob with (XR := eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

End ProbabilisticEuttProbRewriting.

Section ProbabilisticEuttBindCongruence.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.

Lemma stable_hitting_front_choice {A R} (k : A -> ptree E MN R) :
  exists front : A -> MF (frontier_head E MN R),
    forall a, stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R)
      (observe (k a)) (front a).
Proof.
  assert (Hexists : forall a : A,
      exists out : MF (frontier_head E MN R),
        stable_hitting_weak
          (@ptree_primitive_kernel E MN MF FI MX R)
          (observe (k a)) out).
  { intro a. apply stable_hitting_weak_exists. }
  exact (choice
    (fun a out => stable_hitting_weak
      (@ptree_primitive_kernel E MN MF FI MX R)
      (observe (k a)) out) Hexists).
Qed.

Lemma probabilistic_eutt_state_hitting_lift {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (s1 : ptree' E MN R1) (s2 : ptree' E MN R2) out1 out2 :
  probabilistic_eutt_state RR s1 s2 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R1) s1 out1 ->
  stable_hitting_weak
    (@ptree_primitive_kernel E MN MF FI MX R2) s2 out2 ->
  sem_lift (ptree_stable_head_rel RR
    (@probabilistic_eutt_state E MN MF FI FC MX FO R1 R2 RR)) out1 out2.
Proof.
  intros Hrel Hhit1 Hhit2.
  apply stable_hitting_bisim_unfold in Hrel.
  destruct Hrel as [Hforward _].
  destruct (Hforward out1 Hhit1) as [out2' [Hhit2' Hlift]].
  eapply sem_lift_proper_r; [|exact Hlift].
  eapply stable_hitting_weak_unique; [exact Hhit2'|exact Hhit2].
Qed.

(** The coinduction candidate contains the already established greatest
    fixed point as well as bind closure.  The first summand is the standard
    coinduction-up-to-gfp device needed when a source return enters an
    arbitrary related continuation. *)
Definition bind_bisim_candidate (A : Type)
    (s1 s2 : ptree' E MN A) : Prop :=
  probabilistic_eutt_state eq s1 s2 \/
  exists (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN A),
    s1 = observe (PTree.bind t1 k1) /\
    s2 = observe (PTree.bind t2 k2) /\
    probabilistic_eutt RR t1 t2 /\
    (forall r1 r2, RR r1 r2 -> probabilistic_eutt eq (k1 r1) (k2 r2)).

Lemma bind_bisim_candidate_postfixed A :
  forall s1 s2, bind_bisim_candidate (A := A) s1 s2 ->
    stable_hitting_match
      (@ptree_primitive_kernel E MN MF FI MX A)
      (@ptree_primitive_kernel E MN MF FI MX A)
      (@ptree_stable_head_rel E MN A A eq)
      (bind_bisim_candidate (A := A)) s1 s2.
Proof.
  intros s1 s2 [Hknown|Hbind].
  - apply stable_hitting_bisim_unfold in Hknown.
    unfold stable_hitting_match in Hknown |- *.
    destruct Hknown as [Hforward Hbackward]. split.
    + intros out1 Hhit1. destruct (Hforward out1 Hhit1)
        as [out2 [Hhit2 Hlift]]. exists out2. split; [exact Hhit2|].
      eapply sem_lift_mono; [|exact Hlift].
      apply ptree_stable_head_rel_mono.
      intros x1 x2 Hrel. left. exact Hrel.
    + intros out2 Hhit2. destruct (Hbackward out2 Hhit2)
        as [out1 [Hhit1 Hlift]]. exists out1. split; [exact Hhit1|].
      eapply sem_lift_mono; [|exact Hlift].
      apply ptree_stable_head_rel_mono.
      intros x1 x2 Hrel. left. exact Hrel.
  - destruct Hbind as
      [R1 [R2 [RR [t1 [t2 [k1 [k2 [-> [-> [Hsource Hk]]]]]]]]]].
    apply probabilistic_eutt_unfold in Hsource.
    unfold stable_hitting_match in Hsource |- *.
    destruct Hsource as [Hforward Hbackward]. split.
    + intros hs1 Hhit1.
      destruct (stable_hitting_weak_exists
        (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1))
        as [source1 Hsource1].
      destruct (Hforward source1 Hsource1)
        as [source2 [Hsource2 Hlift]].
      destruct (stable_hitting_front_choice k1) as [front1 Hfront1].
      destruct (stable_hitting_front_choice k2) as [front2 Hfront2].
      assert (Hbound1 : stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX A)
        (observe (PTree.bind t1 k1))
        (sem_bind source1 (frontier_head_bind_front k1 front1))).
      { eapply stable_hitting_weak_bind;
          [apply bind_cofinality|exact Hsource1|exact Hfront1]. }
      assert (Hbound2 : stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX A)
        (observe (PTree.bind t2 k2))
        (sem_bind source2 (frontier_head_bind_front k2 front2))).
      { eapply stable_hitting_weak_bind;
          [apply bind_cofinality|exact Hsource2|exact Hfront2]. }
      exists (sem_bind source2 (frontier_head_bind_front k2 front2)). split.
      * exact Hbound2.
      * eapply sem_lift_proper_l.
        -- eapply stable_hitting_weak_unique; [exact Hbound1|exact Hhit1].
        -- eapply sem_lift_bind; [exact Hlift|].
        intros h1 h2 Hhead. dependent destruction Hhead.
        -- eapply sem_lift_mono.
           ++ apply ptree_stable_head_rel_mono.
              intros x1 x2 Hrel. left. exact Hrel.
           ++ apply probabilistic_eutt_state_hitting_lift
                with (s1 := observe (k1 r1)) (s2 := observe (k2 r2));
                [exact (Hk r1 r2 H)|exact (Hfront1 r1)|exact (Hfront2 r2)].
        -- apply sem_lift_ret. constructor. intro x. right.
           exists R1, R2, RR, (k0 x), (k3 x), k1, k2.
           repeat split; try reflexivity.
           ++ exact (H x).
           ++ exact Hk.
    + intros hs2 Hhit2.
      destruct (stable_hitting_weak_exists
        (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2))
        as [source2 Hsource2].
      destruct (Hbackward source2 Hsource2)
        as [source1 [Hsource1 Hlift]].
      destruct (stable_hitting_front_choice k1) as [front1 Hfront1].
      destruct (stable_hitting_front_choice k2) as [front2 Hfront2].
      assert (Hbound1 : stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX A)
        (observe (PTree.bind t1 k1))
        (sem_bind source1 (frontier_head_bind_front k1 front1))).
      { eapply stable_hitting_weak_bind;
          [apply bind_cofinality|exact Hsource1|exact Hfront1]. }
      assert (Hbound2 : stable_hitting_weak
        (@ptree_primitive_kernel E MN MF FI MX A)
        (observe (PTree.bind t2 k2))
        (sem_bind source2 (frontier_head_bind_front k2 front2))).
      { eapply stable_hitting_weak_bind;
          [apply bind_cofinality|exact Hsource2|exact Hfront2]. }
      exists (sem_bind source1 (frontier_head_bind_front k1 front1)). split.
      * exact Hbound1.
      * eapply sem_lift_proper_r.
        -- eapply stable_hitting_weak_unique; [exact Hbound2|exact Hhit2].
        -- eapply sem_lift_bind; [exact Hlift|].
        intros h1 h2 Hhead. dependent destruction Hhead.
        -- eapply sem_lift_mono.
           ++ apply ptree_stable_head_rel_mono.
              intros x1 x2 Hrel. left. exact Hrel.
           ++ apply probabilistic_eutt_state_hitting_lift
                with (s1 := observe (k1 r1)) (s2 := observe (k2 r2));
                [exact (Hk r1 r2 H)|exact (Hfront1 r1)|exact (Hfront2 r2)].
        -- apply sem_lift_ret. constructor. intro x. right.
           exists R1, R2, RR, (k0 x), (k3 x), k1, k2.
           repeat split; try reflexivity.
           ++ exact (H x).
           ++ exact Hk.
Qed.

(** Monadic congruence.  The only syntax-specific premise is the current
    global form of the global/diagonal fuel cofinality theorem; it is used as
    a proof-side scheduling fact by [stable_hitting_weak_bind], never by the
    definition of [probabilistic_eutt]. *)
Theorem probabilistic_eutt_bind : forall A R1 R2
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN A),
  probabilistic_eutt RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> probabilistic_eutt eq (k1 r1) (k2 r2)) ->
  probabilistic_eutt eq (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intros A R1 R2 RR t1 t2 k1 k2 Hsource Hk.
  unfold probabilistic_eutt, probabilistic_eutt_state,
    stable_hitting_bisim.
  eapply (@leq_gfp _ _ (fstable_hitting_bisim
    (@ptree_primitive_kernel E MN MF FI MX A)
    (@ptree_primitive_kernel E MN MF FI MX A)
    (@ptree_stable_head_rel_mono E MN A A eq))
    (bind_bisim_candidate (A := A))).
  - exact (bind_bisim_candidate_postfixed (A := A)).
  - right. exists R1, R2, RR, t1, t2, k1, k2.
    repeat split; try reflexivity; assumption.
Qed.

End ProbabilisticEuttBindCongruence.

Section ProbabilisticEuttFrontierRule.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmegaInterface MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Variable bind_cofinality : forall A R
    (t : ptree E MN A) (k : A -> ptree E MN R),
    operational_bind_cofinal (MF := MF) t k.

Variable iter_productivity : forall I R
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I),
    (forall j, operational_weak (MF := MF) (observe (step j))
      (mixed_bind (transition j)
        (fun next => sem_ret (FHRet next)))) ->
    sem_increasing (fun fuel => mixed_iter_approx fuel transition i) /\
    operational_iter_cofinal (MF := MF) step transition i.

(** Structured frontiers are proof certificates for the canonical
    stable-hitting semantics, not a second behavioral relation. *)
Lemma probabilistic_eutt_of_frontiers {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  frontier (observe t1) out1 ->
  frontier (observe t2) out2 ->
  sem_lift (ptree_stable_head_rel RR
    (@probabilistic_eutt_state E MN MF FI FC MX FO R1 R2 RR)) out1 out2 ->
  probabilistic_eutt RR t1 t2.
Proof.
  intros Hfront1 Hfront2 Hlift.
  eapply probabilistic_eutt_of_hitting_lift.
  - exact (frontier_to_primitive_stable_weak
      bind_cofinality iter_productivity Hfront1).
  - exact (frontier_to_primitive_stable_weak
      bind_cofinality iter_productivity Hfront2).
  - exact Hlift.
Qed.

(** [PTree.iter] instance of the structured/corecursive proof discipline.
    Iteration is discharged by two semantic frontier certificates and a
    coupling of their completed result measures; it is not a constructor of
    [probabilistic_eutt]. *)
Lemma probabilistic_eutt_of_iter_certificates
    {I1 I2 R1 R2} (RR : R1 -> R2 -> Prop)
    (step1 : I1 -> ptree E MN (I1 + R1))
    (step2 : I2 -> ptree E MN (I2 + R2))
    (transition1 : I1 -> MN (I1 + R1))
    (transition2 : I2 -> MN (I2 + R2))
    (i1 : I1) (i2 : I2) out1 out2 :
  (forall j,
    frontier (observe (step1 j))
      (mixed_bind (transition1 j)
        (fun next => sem_ret (FHRet next)))) ->
  mixed_iter transition1 i1 out1 ->
  sem_total out1 ->
  (forall j,
    frontier (observe (step2 j))
      (mixed_bind (transition2 j)
        (fun next => sem_ret (FHRet next)))) ->
  mixed_iter transition2 i2 out2 ->
  sem_total out2 ->
  sem_lift (ptree_stable_head_rel RR
    (@probabilistic_eutt_state E MN MF FI FC MX FO R1 R2 RR))
    (sem_bind out1 (fun r => sem_ret (FHRet r)))
    (sem_bind out2 (fun r => sem_ret (FHRet r))) ->
  probabilistic_eutt RR (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intros Hstep1 Hiter1 Htotal1 Hstep2 Hiter2 Htotal2 Hlift.
  eapply probabilistic_eutt_of_frontiers; [| |exact Hlift].
  - eapply frontier_iter_intro; eassumption.
  - eapply frontier_iter_intro; eassumption.
Qed.

End ProbabilisticEuttFrontierRule.
