Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program RelationClasses Morphisms.
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

(** Finite internal compression followed by one guarded strong match.
    Induction makes each internal compression well-founded; coinduction
    allows recurring interaction and synchronized internal computation.
    No fuel, stable hitting, omega interface, or soundness premise occurs
    in the definition. *)
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

Variant pfiniteF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  | PFiniteStep t1 t2 out1 out2 :
      finite_internal t1 out1 -> finite_internal t2 out2 ->
      sem_lift (pfinite_guard sim) out1 out2 ->
      pfiniteF sim t1 t2.

Lemma pfiniteF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall t1 t2, pfiniteF sim1 t1 t2 ->
    pfiniteF sim2 t1 t2.
Proof.
  intros Hsub t1 t2 Hstep. destruct Hstep.
  eapply PFiniteStep; [exact H|exact H0|].
  eapply sem_lift_mono; [|exact H1].
  intros u1 u2 Hu. unfold pfinite_guard in *.
  eapply pstrongF_monotone; eauto.
Qed.

Program Definition fpfinite :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := pfiniteF |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply pfiniteF_monotone; eauto.
Qed.

Definition pfinite_rel := gfp fpfinite.

Lemma pfinite_rel_unfold t1 t2 :
  pfinite_rel t1 t2 ->
  pfiniteF pfinite_rel t1 t2.
Proof. intro H. apply (gfp_pfp fpfinite) in H. exact H. Qed.

Lemma pfinite_rel_fold t1 t2 :
  pfiniteF pfinite_rel t1 t2 ->
  pfinite_rel t1 t2.
Proof. intro H. apply (gfp_fp fpfinite). exact H. Qed.

End ResidualFinite.

Section ResidualFiniteFacts.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}.

Theorem pstrong_pfinite_rel {A B} (RR : A -> B -> Prop) :
  forall t1 t2, pstrong RR t1 t2 ->
    @pfinite_rel E MN MF NI NC FI FC MX A B RR t1 t2.
Proof.
  unfold pfinite_rel. coinduction CH CIH.
  intros t1 t2 Hrel.
  eapply PFiniteStep; [apply FIStop|apply FIStop|].
  apply sem_lift_ret. unfold pfinite_guard.
  eapply pstrongF_monotone; [|apply pstrong_unfold; exact Hrel].
  intros u1 u2 Hu. apply CIH. exact Hu.
Qed.

Theorem pfinite_rel_converse {A B} (RR : A -> B -> Prop) :
  forall t1 t2,
    @pfinite_rel E MN MF NI NC FI FC MX A B RR t1 t2 ->
    @pfinite_rel E MN MF NI NC FI FC MX B A
      (fun y x => RR x y) t2 t1.
Proof.
  unfold pfinite_rel at 2. coinduction CH CIH.
  intros t1 t2 Hrel. destruct (pfinite_rel_unfold Hrel).
  eapply PFiniteStep; [exact H0|exact H|].
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

Theorem pfinite_rel_mono {A B} (RR SS : A -> B -> Prop)
    (Hsub : forall a b, RR a b -> SS a b) :
  forall t1 t2,
    @pfinite_rel E MN MF NI NC FI FC MX A B RR t1 t2 ->
    @pfinite_rel E MN MF NI NC FI FC MX A B SS t1 t2.
Proof.
  unfold pfinite_rel at 2. coinduction CH CIH.
  intros t1 t2 Hrel. destruct (pfinite_rel_unfold Hrel).
  eapply PFiniteStep; [exact H|exact H0|].
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

Lemma pfinite_rel_refl {R} :
  Reflexive (@pfinite_rel E MN MF NI NC FI FC MX R R eq).
Proof. intro t. apply pstrong_pfinite_rel. apply pstrong_refl. Qed.

Lemma pfinite_rel_sym {R} :
  Symmetric (@pfinite_rel E MN MF NI NC FI FC MX R R eq).
Proof.
  intros t1 t2 Hrel. apply pfinite_rel_converse in Hrel.
  eapply pfinite_rel_mono; [|exact Hrel].
  intros x y Hxy. symmetry. exact Hxy.
Qed.

Lemma pfinite_guard_refl {R} (t : ptree E MN R) :
  @pfinite_guard E MN NI R R eq
    (@pfinite_rel E MN MF NI NC FI FC MX R R eq) t t.
Proof.
  unfold pfinite_guard. eapply pstrongF_monotone.
  - intros u v Huv. apply pstrong_pfinite_rel. exact Huv.
  - apply pstrong_unfold. apply pstrong_refl.
Qed.

Lemma pfinite_rel_same_residual {R} (t1 t2 : ptree E MN R) out :
  finite_internal t1 out -> finite_internal t2 out ->
  @pfinite_rel E MN MF NI NC FI FC MX R R eq t1 t2.
Proof.
  intros H1 H2. apply pfinite_rel_fold.
  eapply PFiniteStep; [exact H1|exact H2|].
  apply sem_lift_refl. intro t. apply pfinite_guard_refl.
Qed.

Lemma pfinite_rel_tau_prefix {R} n (t : ptree E MN R) :
  @pfinite_rel E MN MF NI NC FI FC MX R R eq (tau_prefix n t) t.
Proof.
  eapply pfinite_rel_same_residual.
  - apply finite_internal_tau_prefix.
  - apply FIStop.
Qed.

(** Branch depths can be unbounded over the sampling carrier. *)
Lemma pfinite_rel_prob_tau_prefix {R X} (mu : MN X)
    (depth : X -> nat) (k : X -> ptree E MN R) :
  @pfinite_rel E MN MF NI NC FI FC MX R R eq
    (Prob mu (fun x => tau_prefix (depth x) (k x))) (Prob mu k).
Proof.
  eapply pfinite_rel_same_residual.
  - apply finite_internal_prob_tau_prefix.
  - apply FIProb. intro x. apply FIStop.
Qed.

End ResidualFiniteFacts.

Section StrongerSubrelations.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} {R : Type}.

#[global] Instance pstrong_pfinite_rel_subrelation :
  subrelation (pstrong eq) (@pfinite_rel E MN MF NI NC FI FC MX R R eq).
Proof. intros t u H. apply pstrong_pfinite_rel, H. Qed.

#[global] Instance pstruct_pfinite_rel_subrelation :
  subrelation (pstruct eq) (@pfinite_rel E MN MF NI NC FI FC MX R R eq).
Proof. intros t u H. apply pstrong_pfinite_rel, pstruct_pstrong, H. Qed.
End StrongerSubrelations.

(** Homogeneous equivalence is provided by a finite
    reflexive-symmetric-transitive closure.  This does not assert that the
    raw heterogeneous greatest fixed point is itself transitive. *)
Section ResidualFiniteEquivalence.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} {R : Type}.

Definition pfinite : relation (ptree E MN R) :=
  clos_refl_sym_trans _
    (@pfinite_rel E MN MF NI NC FI FC MX R R eq).

Lemma pfinite_of_rel t1 t2 :
  @pfinite_rel E MN MF NI NC FI FC MX R R eq t1 t2 ->
  pfinite t1 t2.
Proof. apply rst_step. Qed.

#[global] Instance pfinite_equivalence : Equivalence pfinite.
Proof.
  split.
  - intro t. apply rst_refl.
  - intros t u H. apply rst_sym. exact H.
  - intros t u v Htu Huv. eapply rst_trans; eassumption.
Qed.

Lemma pfinite_refl : Reflexive pfinite.
Proof. intro t. apply rst_refl. Qed.

Lemma pfinite_sym : Symmetric pfinite.
Proof. intros t u H. apply rst_sym, H. Qed.

Lemma pfinite_trans : Transitive pfinite.
Proof. intros t u v Htu Huv. eapply rst_trans; eassumption. Qed.

Lemma pstrong_pfinite t u : pstrong eq t u -> pfinite t u.
Proof. intro H. apply pfinite_of_rel, pstrong_pfinite_rel, H. Qed.

Lemma pfinite_tau_l (t : ptree E MN R) : pfinite (Tau t) t.
Proof. apply pfinite_of_rel. exact (pfinite_rel_tau_prefix 1 t). Qed.

Lemma pfinite_tau_r (t : ptree E MN R) : pfinite t (Tau t).
Proof. apply pfinite_sym, pfinite_tau_l. Qed.

Lemma pfinite_prob_tau_prefix {X} (mu : MN X) (depth : X -> nat)
    (k : X -> ptree E MN R) :
  pfinite (Prob mu (fun x => tau_prefix (depth x) (k x))) (Prob mu k).
Proof. apply pfinite_of_rel, pfinite_rel_prob_tau_prefix. Qed.

Lemma pstruct_pfinite t1 t2 :
  pstruct eq t1 t2 -> pfinite t1 t2.
Proof.
  intro H. apply pfinite_of_rel.
  apply pstrong_pfinite_rel. now apply pstruct_pstrong.
Qed.

#[global] Instance pstrong_pfinite_subrelation : subrelation (pstrong eq) pfinite.
Proof. intros t u H. apply pstrong_pfinite, H. Qed.

#[global] Instance pstruct_pfinite_subrelation : subrelation (pstruct eq) pfinite.
Proof. intros t u H. apply pstruct_pfinite, H. Qed.

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
