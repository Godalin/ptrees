From PTree.Eq Require Import StableHittingRelation.
(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From PTree.Eq.FreeOmega Require Import Base.
Section FreeOmegaTranslate.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.

Local Notation MF := (FreeOmega MN).

Section TranslateApproximants.
Context {F : Type -> Type}.
Variable rename : forall X, E X -> F X.

Definition translate_cont {R X}
    (k : X -> ptree E MN R) (x : X) : ptree F MN R :=
  PTree.bind (Ret x) (fun y => PTree.translate rename (k y)).

Inductive translate_head_rel {R} :
    stable_head E MN R -> stable_head F MN R -> Prop :=
  | FTHRet r : translate_head_rel (FHRet r) (FHRet r)
  | FTHVis {X} (e : E X) (k : X -> ptree E MN R) :
      translate_head_rel (FHVis e k)
        (FHVis (@rename X e) (translate_cont k)).

Lemma translate_approx_forward {R} fuel (t : ptree E MN R) :
  free_omega_approx translate_head_rel
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_hitting_approx (MF := MF) (S fuel)
      (observe (PTree.translate rename t))).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold PTree.translate; rewrite observe_interp;
    remember (observe t) as ot eqn:Hot;
    destruct ot as [r|t'|X e k|X mu k]; cbn.
  all: cbn [ptree_hitting_approx ptree_primitive_kernel
    ptree_primitive_kernel stable_hitting_approx stable_target_approx].
  - constructor.
  - constructor. constructor.
  - constructor. constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - constructor. constructor.
  - apply IH.
  - constructor. constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Lemma translate_approx_backward {R} fuel (t : ptree E MN R) :
  free_omega_approx
    (fun hF hE => translate_head_rel hE hF)
    (ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t)))
    (ptree_hitting_approx (MF := MF) fuel (observe t)).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold PTree.translate; rewrite observe_interp;
    remember (observe t) as ot eqn:Hot;
    destruct ot as [r|t'|X e k|X mu k]; cbn.
  all: cbn [ptree_hitting_approx ptree_primitive_kernel
    ptree_primitive_kernel stable_hitting_approx stable_target_approx].
  - constructor. constructor.
  - constructor.
  - constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - constructor. constructor.
  - apply IH.
  - rewrite stable_target_stableE. constructor. constructor.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Lemma translate_hitting_cofinal {R} (t : ptree E MN R) :
  free_omega_chains_cofinal translate_head_rel
    (fun fuel => ptree_hitting_approx (MF := MF) fuel (observe t))
    (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t))).
Proof.
  split.
  - intro n. exists (S n). apply translate_approx_forward.
  - intro n. exists n. apply translate_approx_backward.
Qed.

Lemma translate_canonical_lift {R} (t : ptree E MN R) :
  free_omega_qlift translate_head_rel
    (FOLub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe t)))
    (FOLub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t)))).
Proof.
  apply FOQLCofinal.
  - intro n. apply ptree_hitting_mono. apply Nat.le_succ_diag_r.
  - intro n. exact (@PTreeKernel.ptree_hitting_mono F MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
      FreeOmegaObservableSemanticMeasureOrderLaws R
      (observe (PTree.translate rename t)) n (S n) (Nat.le_succ_diag_r n)).
  - apply translate_hitting_cofinal.
Qed.

Lemma translate_hitting_lift {R} (t : ptree E MN R) out out' :
  @stable_hitting MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega
    (ptree' E MN R) (stable_head E MN R)
    (@ptree_primitive_kernel E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure R) (observe t) out ->
  @stable_hitting MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega
    (ptree' F MN R) (stable_head F MN R)
    (@ptree_primitive_kernel F MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaMixedMeasure R)
    (observe (PTree.translate rename t)) out' ->
  free_omega_qlift translate_head_rel out out'.
Proof.
  intros Hout Hout'.
  unfold stable_hitting in Hout, Hout'.
  cbn [FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasure] in Hout, Hout'.
  unfold sem_lub in Hout, Hout'.
  change (@sem_eq MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) _
    out
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R) fuel (observe t)))) in Hout.
  change (@sem_eq MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) _
    out'
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasure
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R) fuel
      (observe (PTree.translate rename t))))) in Hout'.
  change (free_omega_qlift eq out
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R) fuel (observe t)))) in Hout.
  change (free_omega_qlift eq out'
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasure
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R) fuel
      (observe (PTree.translate rename t))))) in Hout'.
  assert (Hadequate : free_omega_qlift eq
      (FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF
          (FreeOmegaObservableSemanticMeasure
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasure R) fuel (observe t)))
      (FOLub (fun fuel => ptree_hitting_approx (MF := MF) fuel
        (observe t)))).
  { apply FOQLLub. intro fuel.
    exact (ptree_primitive_hitting_adequate
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (MX := FreeOmegaMixedMeasure) fuel (observe t)). }
  assert (Hadequate' : free_omega_qlift eq
      (FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel F MN MF
          (FreeOmegaObservableSemanticMeasure
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasure R) fuel
        (observe (PTree.translate rename t))))
      (FOLub (fun fuel => ptree_hitting_approx (MF := MF) fuel
        (observe (PTree.translate rename t))))).
  { apply FOQLLub. intro fuel.
    exact (ptree_primitive_hitting_adequate
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (MX := FreeOmegaMixedMeasure) fuel
      (observe (PTree.translate rename t))). }
  eapply FOQLComp with (T := eq) (U := translate_head_rel)
      (mid := FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF
          (FreeOmegaObservableSemanticMeasure
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasure R) fuel (observe t))).
  - exact Hout.
  - eapply FOQLComp with (T := translate_head_rel) (U := eq)
        (mid := FOLub (fun fuel => stable_hitting_approx
          (@ptree_primitive_kernel F MN MF
            (FreeOmegaObservableSemanticMeasure
              (NI := NI) (NO := NO))
            FreeOmegaMixedMeasure R) fuel
          (observe (PTree.translate rename t)))).
    + eapply FOQLComp with (T := eq) (U := translate_head_rel)
          (mid := FOLub (fun fuel => ptree_hitting_approx (MF := MF)
            fuel (observe t))).
      * exact Hadequate.
      * eapply FOQLComp with (T := translate_head_rel) (U := eq)
            (mid := FOLub (fun fuel => ptree_hitting_approx (MF := MF)
              fuel (observe (PTree.translate rename t)))).
        -- apply translate_canonical_lift.
        -- apply FOQLSym. eapply FOQLMono; [exact Hadequate'|].
           intros x y ->. reflexivity.
        -- intros x z [y [Hxy ->]]. exact Hxy.
      * intros x z [y [-> Hyz]]. exact Hyz.
    + apply FOQLSym. eapply FOQLMono; [exact Hout'|].
      intros x y ->. reflexivity.
    + intros x z [y [Hxy ->]]. exact Hxy.
  - intros x z [y [-> Hyz]]. exact Hyz.
Qed.

End TranslateApproximants.

Section TranslatePreservation.
Context {F : Type -> Type}.
Variable rename : forall X, E X -> F X.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Inductive translate_bisim_state :
    ptree' F MN R1 -> ptree' F MN R2 -> Prop :=
  | FTBSMain (t1 : ptree E MN R1) (t2 : ptree E MN R2) :
      @peutt E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega R1 R2 RR t1 t2 ->
      translate_bisim_state
        (observe (PTree.translate rename t1))
        (observe (PTree.translate rename t2)).

Lemma translate_head_comp
    (hT1 : stable_head F MN R1) (hT2 : stable_head F MN R2) :
  (exists hS2,
    (exists hS1,
      translate_head_rel (F := F) rename hS1 hT1 /\
      @ptree_stable_head_rel E MN R1 R2 RR
        (@peutt_state E MN MF
          (FreeOmegaObservableSemanticMeasure
            (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasure
          FreeOmegaObservableSemanticOmega R1 R2 RR) hS1 hS2) /\
    translate_head_rel (F := F) rename hS2 hT2) ->
  @ptree_stable_head_rel F MN R1 R2 RR translate_bisim_state hT1 hT2.
Proof.
  intros [hS2 [[hS1 [Hmap1 Hsource]] Hmap2]].
  dependent destruction Hsource.
  - dependent destruction Hmap1. dependent destruction Hmap2.
    constructor. exact H.
  - dependent destruction Hmap1. dependent destruction Hmap2.
    constructor. intro x.
    unfold translate_cont. rewrite !observe_bind. cbn.
    constructor. exact (H x).
Qed.

Theorem peutt_translate {t1 : ptree E MN R1}
    {t2 : ptree E MN R2} :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR t1 t2 ->
  @peutt F MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R1 R2 RR
    (PTree.translate rename t1) (PTree.translate rename t2).
Proof.
  intro Hsource. eapply peutt_coinduction with
    (sim := translate_bisim_state).
  - intros s1 s2 Hsim. dependent destruction Hsim.
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R1) (observe t0)) as [outS1 HS1].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R2) (observe t3)) as [outS2 HS2].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R1)
      (observe (PTree.translate rename t0))) as [outT1 HT1].
    destruct (stable_hitting_exists
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaMixedMeasure R2)
      (observe (PTree.translate rename t3))) as [outT2 HT2].
    eapply stable_hitting_match_of_hitting_lift; [exact HT1|exact HT2|].
    pose proof (peutt_hitting_lift H HS1 HS2) as HsourceLift.
    pose proof (translate_hitting_lift HS1 HT1) as Hmap1.
    pose proof (translate_hitting_lift HS2 HT2) as Hmap2.
    eapply FOQLComp with
      (T := fun hT hS => translate_head_rel rename hS hT)
      (U := fun hS1 hT2 => exists hS2,
        @ptree_stable_head_rel E MN R1 R2 RR
          (@peutt_state E MN MF
            (FreeOmegaObservableSemanticMeasure
              (NI := NI) (NO := NO))
            FreeOmegaObservableSemanticMeasureCoreLaws
            FreeOmegaMixedMeasure
            FreeOmegaObservableSemanticOmega R1 R2 RR) hS1 hS2 /\
        translate_head_rel rename hS2 hT2)
      (mid := outS1).
    + apply FOQLSym. exact Hmap1.
    + eapply FOQLComp with
        (T := @ptree_stable_head_rel E MN R1 R2 RR
          (@peutt_state E MN MF
            (FreeOmegaObservableSemanticMeasure
              (NI := NI) (NO := NO))
            FreeOmegaObservableSemanticMeasureCoreLaws
            FreeOmegaMixedMeasure
            FreeOmegaObservableSemanticOmega R1 R2 RR))
        (U := translate_head_rel rename)
        (mid := outS2).
      * exact HsourceLift.
      * exact Hmap2.
      * intros hS1 hT2 [hS2 [Hrel Hmap]].
        exists hS2. split; assumption.
    + intros hT1 hT2 [hS1 [Hmap1' [hS2 [Hsource' Hmap2']]]].
      apply translate_head_comp.
      exists hS2. split; [exists hS1; split|]; assumption.
  - constructor. exact Hsource.
Qed.

End TranslatePreservation.
End FreeOmegaTranslate.
