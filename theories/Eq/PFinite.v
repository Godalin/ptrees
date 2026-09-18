Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8 Program RelationClasses.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import PStrong PrimitiveStableHitting
  OperationalProbabilisticPTS UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "` R" := (elem R) (at level 10).

(** A stable observation is finitely available when the complete hitting
    measure is already attained by one finite approximant.  This is a local
    condition on the next stable observation, not termination of the whole
    tree: a visible continuation may again run forever. *)
Section FiniteStableHitting.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FO : @SemanticOmega MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

Definition finite_stable_hitting (state : S) (out : MF A) : Prop :=
  stable_hitting kernel state out /\
  exists fuel, sem_eq (stable_hitting_approx kernel fuel state) out.

Lemma finite_stable_hitting_stable state out :
  finite_stable_hitting state out -> stable_hitting kernel state out.
Proof. by move=> []. Qed.

End FiniteStableHitting.

(** Finite weak probabilistic equivalence.  Every coinductive round may
    either take one lockstep strong transition, discard one [Tau] on either
    side, or collapse a finite internal prefix whose complete stable hitting
    measure has already been reached.  The coinduction itself is unbounded;
    only each individual weak compression must be finite. *)
Section PFinite.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

(** An inductive, hence genuinely finite, closure removing Tau prefixes on
    either side.  Keeping this outside the greatest fixed point prevents an
    infinite one-sided Tau loop from proving an arbitrary equivalence. *)
Inductive finite_tau_closure
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  | FTBase t1 t2 : sim t1 t2 -> finite_tau_closure sim t1 t2
  | FTTauL t1 t2 :
      finite_tau_closure sim t1 t2 ->
      finite_tau_closure sim (Tau t1) t2
  | FTTauR t1 t2 :
      finite_tau_closure sim t1 t2 ->
      finite_tau_closure sim t1 (Tau t2).

Lemma finite_tau_closure_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall t1 t2,
    finite_tau_closure sim1 t1 t2 ->
    finite_tau_closure sim2 t1 t2.
Proof.
  intros Hsub t1 t2 Hfinite. induction Hfinite.
  - apply FTBase. now apply Hsub.
  - apply FTTauL. exact IHHfinite.
  - apply FTTauR. exact IHHfinite.
Qed.

Variant pfiniteF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  | PFiniteStrong t1 t2 :
      pstrong RR t1 t2 -> pfiniteF sim t1 t2
  | PFiniteCollapse t1 t2 out1 out2 :
      finite_stable_hitting
        (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
      finite_stable_hitting
        (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
      sem_lift (frontier_head_rel RR (finite_tau_closure sim)) out1 out2 ->
      pfiniteF sim t1 t2.

Lemma pfiniteF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall t1 t2, pfiniteF sim1 t1 t2 -> pfiniteF sim2 t1 t2.
Proof.
  intros Hsub t1 t2 Hstep. inversion Hstep; subst.
  - apply PFiniteStrong. exact H.
  - eapply PFiniteCollapse; [eassumption|eassumption|].
    eapply sem_lift_mono; [|eassumption].
    intros h1 h2 Hh. eapply frontier_head_rel_mono; [|exact Hh].
    intros u1 u2 Hu. eapply finite_tau_closure_mono; eauto.
Qed.

Program Definition fpfinite :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := pfiniteF |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply pfiniteF_monotone; eauto.
Qed.

Definition pfinite_core : ptree E MN R1 -> ptree E MN R2 -> Prop :=
  gfp fpfinite.

Lemma pfinite_core_unfold t1 t2 :
  pfinite_core t1 t2 -> pfiniteF pfinite_core t1 t2.
Proof. intro H. apply (gfp_pfp fpfinite) in H. exact H. Qed.

Lemma pfinite_core_fold t1 t2 :
  pfiniteF pfinite_core t1 t2 -> pfinite_core t1 t2.
Proof. intro H. unfold pfinite_core. apply (gfp_fp fpfinite). exact H. Qed.

Definition pfinite : ptree E MN R1 -> ptree E MN R2 -> Prop :=
  finite_tau_closure pfinite_core.

Theorem pstrong_pfinite : forall t1 t2,
  pstrong RR t1 t2 -> pfinite t1 t2.
Proof.
  intros t1 t2 H. apply FTBase. apply pfinite_core_fold.
  now apply PFiniteStrong.
Qed.

End PFinite.

Section FiniteTauClosureConverse.
Context {E : Type -> Type} {MN : Type -> Type} {R1 R2 : Type}.

Lemma finite_tau_closure_converse
    (sim1 : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (sim2 : ptree E MN R2 -> ptree E MN R1 -> Prop)
    (Hsim : forall t1 t2, sim1 t1 t2 -> sim2 t2 t1) :
  forall t1 t2,
    finite_tau_closure sim1 t1 t2 ->
    finite_tau_closure sim2 t2 t1.
Proof.
  intros t1 t2 Hfinite. induction Hfinite.
  - apply FTBase. now apply Hsim.
  - apply FTTauR. exact IHHfinite.
  - apply FTTauL. exact IHHfinite.
Qed.

End FiniteTauClosureConverse.

Section PFiniteConverse.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Theorem pfinite_core_converse : forall t1 t2,
  @pfinite_core E MN MF NI NC FI FC MX FO R1 R2 RR t1 t2 ->
  @pfinite_core E MN MF NI NC FI FC MX FO R2 R1
    (fun y x => RR x y) t2 t1.
Proof.
  unfold pfinite_core at 2. coinduction CH CIH.
  intros t1 t2 Hrel. pose proof (pfinite_core_unfold Hrel) as Hstep.
  inversion Hstep as
      [u1 u2 Hstrong|u1 u2 out1 out2 Hhit1 Hhit2 Hlift]; subst.
  - apply PFiniteStrong. now apply pstrong_sym.
  - eapply PFiniteCollapse; [exact Hhit2|exact Hhit1|].
    eapply sem_lift_mono; [|apply sem_lift_sym; exact Hlift].
    intros h2 h1 Hhead. dependent destruction Hhead.
    + constructor. exact H.
    + constructor. intro x.
      eapply finite_tau_closure_converse; [|exact (H x)].
      intros v1 v2 Hv. exact (CIH _ _ Hv).
Qed.

Theorem pfinite_converse : forall t1 t2,
  @pfinite E MN MF NI NC FI FC MX FO R1 R2 RR t1 t2 ->
  @pfinite E MN MF NI NC FI FC MX FO R2 R1
    (fun y x => RR x y) t2 t1.
Proof.
  intros t1 t2 Hrel.
  eapply finite_tau_closure_converse; [|exact Hrel].
  intros u1 u2 Hu. now apply pfinite_core_converse.
Qed.

End PFiniteConverse.

Section PFiniteRelationMonotonicity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {R1 R2 : Type}.

Theorem pfinite_core_rel_mono (RR SS : R1 -> R2 -> Prop)
    (Hsub : forall r1 r2, RR r1 r2 -> SS r1 r2) : forall t1 t2,
  @pfinite_core E MN MF NI NC FI FC MX FO R1 R2 RR t1 t2 ->
  @pfinite_core E MN MF NI NC FI FC MX FO R1 R2 SS t1 t2.
Proof.
  unfold pfinite_core at 2. coinduction CH CIH.
  intros t1 t2 Hrel. pose proof (pfinite_core_unfold Hrel) as Hstep.
  inversion Hstep as
      [u1 u2 Hstrong|u1 u2 out1 out2 Hhit1 Hhit2 Hlift]; subst.
  - apply PFiniteStrong. eapply pstrong_rel_mono; eauto.
  - eapply PFiniteCollapse; [exact Hhit1|exact Hhit2|].
    eapply sem_lift_mono; [|exact Hlift].
    intros h1 h2 Hhead. dependent destruction Hhead.
    + constructor. now apply Hsub.
    + constructor. intro x.
      eapply finite_tau_closure_mono; [|exact (H x)].
      intros v1 v2 Hv. exact (CIH _ _ Hv).
Qed.

Theorem pfinite_rel_mono (RR SS : R1 -> R2 -> Prop)
    (Hsub : forall r1 r2, RR r1 r2 -> SS r1 r2) : forall t1 t2,
  @pfinite E MN MF NI NC FI FC MX FO R1 R2 RR t1 t2 ->
  @pfinite E MN MF NI NC FI FC MX FO R1 R2 SS t1 t2.
Proof.
  intros t1 t2 Hrel. eapply finite_tau_closure_mono; [|exact Hrel].
  intros u1 u2 Hu. eapply pfinite_core_rel_mono; eauto.
Qed.

End PFiniteRelationMonotonicity.

Section PFiniteFacts.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Lemma pfinite_refl {R} :
  Reflexive (@pfinite E MN MF NI NC FI FC MX FO R R eq).
Proof. intro t. apply pstrong_pfinite. apply pstrong_refl. Qed.

Lemma pfinite_sym {R} :
  Symmetric (@pfinite E MN MF NI NC FI FC MX FO R R eq).
Proof.
  intros t1 t2 Hrel. eapply pfinite_converse in Hrel.
  eapply pfinite_rel_mono; [|exact Hrel].
  intros x y Hxy. symmetry. exact Hxy.
Qed.

Lemma pfinite_tau_l {R} (t : ptree E MN R) :
  @pfinite E MN MF NI NC FI FC MX FO R R eq (Tau t) t.
Proof. apply FTTauL. apply pfinite_refl. Qed.

Lemma pfinite_tau_r {R} (t : ptree E MN R) :
  @pfinite E MN MF NI NC FI FC MX FO R R eq t (Tau t).
Proof. apply FTTauR. apply pfinite_refl. Qed.

Lemma pfinite_collapse {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) out1 out2 :
  finite_stable_hitting
    (@ptree_primitive_kernel E MN MF FI MX R1) (observe t1) out1 ->
  finite_stable_hitting
    (@ptree_primitive_kernel E MN MF FI MX R2) (observe t2) out2 ->
  sem_lift (frontier_head_rel RR
    (@pfinite E MN MF NI NC FI FC MX FO R1 R2 RR)) out1 out2 ->
  @pfinite E MN MF NI NC FI FC MX FO R1 R2 RR t1 t2.
Proof.
  intros H1 H2 Hl. apply FTBase. apply pfinite_core_fold.
  eapply PFiniteCollapse; eauto.
Qed.

#[global] Instance pstrong_pfinite_subrelation {R} :
  subrelation (@pstrong E MN NI NC R R eq)
    (@pfinite E MN MF NI NC FI FC MX FO R R eq).
Proof. intros t1 t2. apply pstrong_pfinite. Qed.

#[global] Instance pstruct_pfinite_subrelation {R} :
  subrelation (@pstruct E MN R R eq)
    (@pfinite E MN MF NI NC FI FC MX FO R R eq).
Proof. intros t1 t2 H. apply pstrong_pfinite. apply pstruct_pstrong. exact H. Qed.

End PFiniteFacts.
