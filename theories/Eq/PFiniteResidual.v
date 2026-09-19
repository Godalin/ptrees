Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program RelationClasses.
From Coq Require Import Relations.Relation_Operators.
From Coinduction Require Import all.
From mathcomp Require Import ssreflect.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import FiniteInternal PStruct PStrong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Notation "` R" := (elem R) (at level 10).

(** Candidate replacement for the stable-frontier-based finite relation.
    Kept separate until the unconditional FreeOmega soundness theorem has
    been proved.  There is deliberately no semantic soundness premise
    hidden in this definition, and no stable hitting or omega interface. *)
Section ResidualFinite.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition pfinite_guard
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) t1 t2 :=
  pstrongF RR sim (observe t1) (observe t2).

Variant pfinite_residualF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  | PFiniteResidualStep t1 t2 out1 out2 :
      finite_internal t1 out1 -> finite_internal t2 out2 ->
      sem_lift (pfinite_guard sim) out1 out2 ->
      pfinite_residualF sim t1 t2.

Lemma pfinite_residualF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall t1 t2, pfinite_residualF sim1 t1 t2 ->
    pfinite_residualF sim2 t1 t2.
Proof.
  intros Hsub t1 t2 Hstep. destruct Hstep.
  eapply PFiniteResidualStep; [exact H|exact H0|].
  eapply sem_lift_mono; [|exact H1].
  intros u1 u2 Hu. unfold pfinite_guard in *.
  eapply pstrongF_monotone; eauto.
Qed.

Program Definition fpfinite_residual :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := pfinite_residualF |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply pfinite_residualF_monotone; eauto.
Qed.

Definition pfinite_residual_rel := gfp fpfinite_residual.

Lemma pfinite_residual_unfold t1 t2 :
  pfinite_residual_rel t1 t2 ->
  pfinite_residualF pfinite_residual_rel t1 t2.
Proof. intro H. apply (gfp_pfp fpfinite_residual) in H. exact H. Qed.

Lemma pfinite_residual_fold t1 t2 :
  pfinite_residualF pfinite_residual_rel t1 t2 ->
  pfinite_residual_rel t1 t2.
Proof. intro H. apply (gfp_fp fpfinite_residual). exact H. Qed.

End ResidualFinite.

Section ResidualFiniteFacts.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}.

Theorem pstrong_pfinite_residual_rel {A B} (RR : A -> B -> Prop) :
  forall t1 t2, pstrong RR t1 t2 ->
    @pfinite_residual_rel E MN MF NI NC FI FC MX A B RR t1 t2.
Proof.
  unfold pfinite_residual_rel. coinduction CH CIH.
  intros t1 t2 Hrel.
  eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
  apply sem_lift_ret. unfold pfinite_guard.
  eapply pstrongF_monotone; [|apply pstrong_unfold; exact Hrel].
  intros u1 u2 Hu. apply CIH. exact Hu.
Qed.

Theorem pfinite_residual_converse {A B} (RR : A -> B -> Prop) :
  forall t1 t2,
    @pfinite_residual_rel E MN MF NI NC FI FC MX A B RR t1 t2 ->
    @pfinite_residual_rel E MN MF NI NC FI FC MX B A
      (fun y x => RR x y) t2 t1.
Proof.
  unfold pfinite_residual_rel at 2. coinduction CH CIH.
  intros t1 t2 Hrel. destruct (pfinite_residual_unfold Hrel).
  eapply PFiniteResidualStep; [exact H0|exact H|].
  eapply sem_lift_mono; [|apply sem_lift_sym; exact H1].
  intros u2 u1 Hguard. unfold pfinite_guard in *.
  remember (observe u1) as o1 in Hguard |- *.
  remember (observe u2) as o2 in Hguard |- *.
  destruct Hguard.
  - constructor. exact H2.
  - constructor. apply CIH. exact H2.
  - constructor. intro x. apply CIH. apply H2.
  - constructor. eapply sem_lift_mono; [|apply sem_lift_sym; exact H2].
    intros x y Hxy. apply CIH. exact Hxy.
Qed.

Theorem pfinite_residual_rel_mono {A B} (RR SS : A -> B -> Prop)
    (Hsub : forall a b, RR a b -> SS a b) :
  forall t1 t2,
    @pfinite_residual_rel E MN MF NI NC FI FC MX A B RR t1 t2 ->
    @pfinite_residual_rel E MN MF NI NC FI FC MX A B SS t1 t2.
Proof.
  unfold pfinite_residual_rel at 2. coinduction CH CIH.
  intros t1 t2 Hrel. destruct (pfinite_residual_unfold Hrel).
  eapply PFiniteResidualStep; [exact H|exact H0|].
  eapply sem_lift_mono; [|exact H1].
  intros u1 u2 Hguard. unfold pfinite_guard in *.
  remember (observe u1) as o1 in Hguard |- *.
  remember (observe u2) as o2 in Hguard |- *.
  destruct Hguard.
  - constructor. apply Hsub. exact H2.
  - constructor. apply CIH. exact H2.
  - constructor. intro x. apply CIH. apply H2.
  - constructor. eapply sem_lift_mono; [|exact H2].
    intros x y Hxy. apply CIH. exact Hxy.
Qed.

Lemma pfinite_residual_refl {R} :
  Reflexive (@pfinite_residual_rel E MN MF NI NC FI FC MX R R eq).
Proof. intro t. apply pstrong_pfinite_residual_rel. apply pstrong_refl. Qed.

Lemma pfinite_residual_sym {R} :
  Symmetric (@pfinite_residual_rel E MN MF NI NC FI FC MX R R eq).
Proof.
  intros t1 t2 Hrel. apply pfinite_residual_converse in Hrel.
  eapply pfinite_residual_rel_mono; [|exact Hrel].
  intros x y Hxy. symmetry. exact Hxy.
Qed.

Lemma pfinite_residual_guard_refl {R} (t : ptree E MN R) :
  @pfinite_guard E MN NI R R eq
    (@pfinite_residual_rel E MN MF NI NC FI FC MX R R eq) t t.
Proof.
  unfold pfinite_guard. eapply pstrongF_monotone.
  - intros u v Huv. apply pstrong_pfinite_residual_rel. exact Huv.
  - apply pstrong_unfold. apply pstrong_refl.
Qed.

Lemma pfinite_residual_same_frontier {R} (t1 t2 : ptree E MN R) out :
  finite_internal t1 out -> finite_internal t2 out ->
  @pfinite_residual_rel E MN MF NI NC FI FC MX R R eq t1 t2.
Proof.
  intros H1 H2. apply pfinite_residual_fold.
  eapply PFiniteResidualStep; [exact H1|exact H2|].
  apply sem_lift_refl. intro t. apply pfinite_residual_guard_refl.
Qed.

Lemma pfinite_residual_tau_prefix {R} n (t : ptree E MN R) :
  @pfinite_residual_rel E MN MF NI NC FI FC MX R R eq (tau_prefix n t) t.
Proof.
  eapply pfinite_residual_same_frontier.
  - apply finite_internal_tau_prefix.
  - apply FIStop.
Qed.

(** Branch depths can be unbounded over the sampling carrier. *)
Lemma pfinite_residual_prob_tau_prefix {R X} (mu : MN X)
    (depth : X -> nat) (k : X -> ptree E MN R) :
  @pfinite_residual_rel E MN MF NI NC FI FC MX R R eq
    (Prob mu (fun x => tau_prefix (depth x) (k x))) (Prob mu k).
Proof.
  eapply pfinite_residual_same_frontier.
  - apply finite_internal_prob_tau_prefix.
  - apply FIProb. intro x. apply FIStop.
Qed.

End ResidualFiniteFacts.

(** As for the current homogeneous API, equivalence is provided by a finite
    reflexive-symmetric-transitive closure.  This does not assert that the
    raw heterogeneous greatest fixed point is itself transitive. *)
Section ResidualFiniteEquivalence.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} {R : Type}.

Definition pfinite_residual : relation (ptree E MN R) :=
  clos_refl_sym_trans _
    (@pfinite_residual_rel E MN MF NI NC FI FC MX R R eq).

Lemma pfinite_residual_of_rel t1 t2 :
  @pfinite_residual_rel E MN MF NI NC FI FC MX R R eq t1 t2 ->
  pfinite_residual t1 t2.
Proof. apply rst_step. Qed.

#[global] Instance pfinite_residual_equivalence : Equivalence pfinite_residual.
Proof.
  split.
  - intro t. apply rst_refl.
  - intros t u H. apply rst_sym. exact H.
  - intros t u v Htu Huv. eapply rst_trans; eassumption.
Qed.

Lemma pstruct_pfinite_residual t1 t2 :
  pstruct eq t1 t2 -> pfinite_residual t1 t2.
Proof.
  intro H. apply pfinite_residual_of_rel.
  apply pstrong_pfinite_residual_rel. now apply pstruct_pstrong.
Qed.

End ResidualFiniteEquivalence.

(** This law is about a supplied equivalence candidate, not a claim that
    the raw residual greatest fixed point is transitive.  It permits finite
    support class-coding of a guard relation when that hypothesis is known. *)
Section GuardEquivalence.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI} {A : Type}.
Variable sim : relation (ptree E MN A).

Lemma pfinite_guard_equivalence : Equivalence sim -> Equivalence (pfinite_guard eq sim).
Proof.
  intros [Hrefl Hsym Htrans]. split; unfold pfinite_guard.
  - intro t. destruct (observe t); constructor.
    + reflexivity.
    + apply Hrefl.
    + intro x. apply Hrefl.
    + apply sem_lift_refl. intro x. apply Hrefl.
  - intros t u H.
    remember (observe t) as ot in H |- *.
    remember (observe u) as ou in H |- *.
    destruct H; constructor.
    + symmetry. exact H.
    + apply Hsym. exact H.
    + intro x. apply Hsym, H.
    + eapply sem_lift_mono; [|apply sem_lift_sym; exact H].
      intros x y Hxy. apply Hsym. exact Hxy.
  - intros t u v Htu Huv.
    set ot := observe t in Htu |- *.
    set ou := observe u in Htu Huv.
    set ov := observe v in Huv |- *.
    destruct ou.
    + dependent destruction Htu. dependent destruction Huv.
      rewrite <- x0, <- x. constructor. reflexivity.
    + dependent destruction Htu. dependent destruction Huv.
      rewrite <- x0, <- x. constructor. eapply Htrans; eassumption.
    + dependent destruction Htu. dependent destruction Huv.
      rewrite <- x0, <- x. constructor. intro y. eapply Htrans; [apply H|apply H0].
    + dependent destruction Htu. dependent destruction Huv.
      rewrite <- x0, <- x. constructor.
      eapply sem_lift_mono; [|exact (sem_lift_comp H H0)].
      intros a b [z [Ha Hb]]. eapply Htrans; eassumption.
Qed.
End GuardEquivalence.
