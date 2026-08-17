Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List Arith.PeanoNat FunctionalExtensionality Lia
  Logic.ClassicalChoice
  Program.Equality Morphisms.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum TwoLevelMeasure
  TwoLevelMeasureEnum FreeOmegaMeasure MeasureIteration.
From PTree.Eq Require Import ShallowNew UnifiedFrontier PrimitiveStableHitting
  OperationalProbabilisticPTS ProbabilisticEutt PStrong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaOperationalCofinality.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

Lemma free_operational_hitting_mono {R} (ot : ptree' E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) n ot)
    (operational_hitting_approx (MF := MF) m ot).
Proof.
  apply (operational_hitting_mono
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface)).
Qed.

Section TranslateApproximants.
Context {F : Type -> Type}.
Variable rename : forall X, E X -> F X.

Definition free_translate_cont {R X}
    (k : X -> ptree E MN R) (x : X) : ptree F MN R :=
  PTree.bind (Ret x) (fun y => PTree.translate rename (k y)).

Inductive free_translate_head_rel {R} :
    frontier_head E MN R -> frontier_head F MN R -> Prop :=
  | FTHRet r : free_translate_head_rel (FHRet r) (FHRet r)
  | FTHVis {X} (e : E X) (k : X -> ptree E MN R) :
      free_translate_head_rel (FHVis e k)
        (FHVis (@rename X e) (free_translate_cont k)).

Lemma free_translate_approx_forward {R} fuel (t : ptree E MN R) :
  free_omega_approx free_translate_head_rel
    (operational_hitting_approx (MF := MF) fuel (observe t))
    (operational_hitting_approx (MF := MF) (S fuel)
      (observe (PTree.translate rename t))).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold PTree.translate; rewrite observe_interp;
    remember (observe t) as ot eqn:Hot;
    destruct ot as [r|t'|X e k|X mu k]; cbn.
  all: cbn [operational_hitting_approx operational_kernel
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

Lemma free_translate_approx_backward {R} fuel (t : ptree E MN R) :
  free_omega_approx
    (fun hF hE => free_translate_head_rel hE hF)
    (operational_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t)))
    (operational_hitting_approx (MF := MF) fuel (observe t)).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold PTree.translate; rewrite observe_interp;
    remember (observe t) as ot eqn:Hot;
    destruct ot as [r|t'|X e k|X mu k]; cbn.
  all: cbn [operational_hitting_approx operational_kernel
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

Lemma free_translate_hitting_cofinal {R} (t : ptree E MN R) :
  free_omega_chains_cofinal free_translate_head_rel
    (fun fuel => operational_hitting_approx (MF := MF) fuel (observe t))
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t))).
Proof.
  split.
  - intro n. exists (S n). apply free_translate_approx_forward.
  - intro n. exists n. apply free_translate_approx_backward.
Qed.

Lemma free_translate_canonical_lift {R} (t : ptree E MN R) :
  free_omega_qlift free_translate_head_rel
    (FOLub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe t)))
    (FOLub (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.translate rename t)))).
Proof.
  apply FOQLCofinal. apply free_translate_hitting_cofinal.
Qed.

Lemma free_translate_hitting_lift {R} (t : ptree E MN R) out out' :
  @stable_hitting_weak MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' E MN R) (frontier_head E MN R)
    (@ptree_primitive_kernel E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface R) (observe t) out ->
  @stable_hitting_weak MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface
    (ptree' F MN R) (frontier_head F MN R)
    (@ptree_primitive_kernel F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface R)
    (observe (PTree.translate rename t)) out' ->
  free_omega_qlift free_translate_head_rel out out'.
Proof.
  intros Hout Hout'.
  unfold stable_hitting_weak in Hout, Hout'.
  cbn [FreeOmegaObservableSemanticOmegaInterface
    FreeOmegaObservableSemanticMeasureInterface] in Hout, Hout'.
  unfold sem_lub in Hout, Hout'.
  change (@sem_eq MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)) _
    out
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) fuel (observe t)))) in Hout.
  change (@sem_eq MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO)) _
    out'
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) fuel
      (observe (PTree.translate rename t))))) in Hout'.
  change (free_omega_qlift eq out
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) fuel (observe t)))) in Hout.
  change (free_omega_qlift eq out'
    (FOLub (fun fuel => stable_hitting_approx
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface
          (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) fuel
      (observe (PTree.translate rename t))))) in Hout'.
  assert (Hadequate : free_omega_qlift eq
      (FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF
          (FreeOmegaObservableSemanticMeasureInterface
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasureInterface R) fuel (observe t)))
      (FOLub (fun fuel => operational_hitting_approx (MF := MF) fuel
        (observe t)))).
  { apply FOQLLub. intro fuel.
    exact (ptree_primitive_hitting_adequate
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (MX := FreeOmegaMixedMeasureInterface) fuel (observe t)). }
  assert (Hadequate' : free_omega_qlift eq
      (FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel F MN MF
          (FreeOmegaObservableSemanticMeasureInterface
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasureInterface R) fuel
        (observe (PTree.translate rename t))))
      (FOLub (fun fuel => operational_hitting_approx (MF := MF) fuel
        (observe (PTree.translate rename t))))).
  { apply FOQLLub. intro fuel.
    exact (ptree_primitive_hitting_adequate
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (MX := FreeOmegaMixedMeasureInterface) fuel
      (observe (PTree.translate rename t))). }
  eapply FOQLComp with (T := eq) (U := free_translate_head_rel)
      (mid := FOLub (fun fuel => stable_hitting_approx
        (@ptree_primitive_kernel E MN MF
          (FreeOmegaObservableSemanticMeasureInterface
            (NI := NI) (NO := NO))
          FreeOmegaMixedMeasureInterface R) fuel (observe t))).
  - exact Hout.
  - eapply FOQLComp with (T := free_translate_head_rel) (U := eq)
        (mid := FOLub (fun fuel => stable_hitting_approx
          (@ptree_primitive_kernel F MN MF
            (FreeOmegaObservableSemanticMeasureInterface
              (NI := NI) (NO := NO))
            FreeOmegaMixedMeasureInterface R) fuel
          (observe (PTree.translate rename t)))).
    + eapply FOQLComp with (T := eq) (U := free_translate_head_rel)
          (mid := FOLub (fun fuel => operational_hitting_approx (MF := MF)
            fuel (observe t))).
      * exact Hadequate.
      * eapply FOQLComp with (T := free_translate_head_rel) (U := eq)
            (mid := FOLub (fun fuel => operational_hitting_approx (MF := MF)
              fuel (observe (PTree.translate rename t)))).
        -- apply free_translate_canonical_lift.
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

Inductive free_translate_bisim_state :
    ptree' F MN R1 -> ptree' F MN R2 -> Prop :=
  | FTBSMain (t1 : ptree E MN R1) (t2 : ptree E MN R2) :
      @probabilistic_eutt E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface R1 R2 RR t1 t2 ->
      free_translate_bisim_state
        (observe (PTree.translate rename t1))
        (observe (PTree.translate rename t2)).

Lemma free_translate_head_comp
    (hT1 : frontier_head F MN R1) (hT2 : frontier_head F MN R2) :
  (exists hS2,
    (exists hS1,
      free_translate_head_rel (F := F) rename hS1 hT1 /\
      @ptree_stable_head_rel E MN R1 R2 RR
        (@probabilistic_eutt_state E MN MF
          (FreeOmegaObservableSemanticMeasureInterface
            (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasureInterface
          FreeOmegaObservableSemanticOmegaInterface R1 R2 RR) hS1 hS2) /\
    free_translate_head_rel (F := F) rename hS2 hT2) ->
  @ptree_stable_head_rel F MN R1 R2 RR free_translate_bisim_state hT1 hT2.
Proof.
  intros [hS2 [[hS1 [Hmap1 Hsource]] Hmap2]].
  dependent destruction Hsource.
  - dependent destruction Hmap1. dependent destruction Hmap2.
    constructor. exact H.
  - dependent destruction Hmap1. dependent destruction Hmap2.
    constructor. intro x.
    unfold free_translate_cont. rewrite !observe_bind. cbn.
    constructor. exact (H x).
Qed.

Theorem free_probabilistic_eutt_translate {t1 : ptree E MN R1}
    {t2 : ptree E MN R2} :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR t1 t2 ->
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.translate rename t1) (PTree.translate rename t2).
Proof.
  intro Hsource. eapply probabilistic_eutt_coinduction with
    (sim := free_translate_bisim_state).
  - intros s1 s2 Hsim. dependent destruction Hsim.
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R1) (observe t0)) as [outS1 HS1].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R2) (observe t3)) as [outS2 HS2].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R1)
      (observe (PTree.translate rename t0))) as [outT1 HT1].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R2)
      (observe (PTree.translate rename t3))) as [outT2 HT2].
    eapply stable_hitting_match_of_hitting_lift; [exact HT1|exact HT2|].
    pose proof (probabilistic_eutt_hitting_lift H HS1 HS2) as HsourceLift.
    pose proof (free_translate_hitting_lift HS1 HT1) as Hmap1.
    pose proof (free_translate_hitting_lift HS2 HT2) as Hmap2.
    eapply FOQLComp with
      (T := fun hT hS => free_translate_head_rel rename hS hT)
      (U := fun hS1 hT2 => exists hS2,
        @ptree_stable_head_rel E MN R1 R2 RR
          (@probabilistic_eutt_state E MN MF
            (FreeOmegaObservableSemanticMeasureInterface
              (NI := NI) (NO := NO))
            FreeOmegaObservableSemanticMeasureCoreLaws
            FreeOmegaMixedMeasureInterface
            FreeOmegaObservableSemanticOmegaInterface R1 R2 RR) hS1 hS2 /\
        free_translate_head_rel rename hS2 hT2)
      (mid := outS1).
    + apply FOQLSym. exact Hmap1.
    + eapply FOQLComp with
        (T := @ptree_stable_head_rel E MN R1 R2 RR
          (@probabilistic_eutt_state E MN MF
            (FreeOmegaObservableSemanticMeasureInterface
              (NI := NI) (NO := NO))
            FreeOmegaObservableSemanticMeasureCoreLaws
            FreeOmegaMixedMeasureInterface
            FreeOmegaObservableSemanticOmegaInterface R1 R2 RR))
        (U := free_translate_head_rel rename)
        (mid := outS2).
      * exact HsourceLift.
      * exact Hmap2.
      * intros hS1 hT2 [hS2 [Hrel Hmap]].
        exists hS2. split; assumption.
    + intros hT1 hT2 [hS1 [Hmap1' [hS2 [Hsource' Hmap2']]]].
      apply free_translate_head_comp.
      exists hS2. split; [exists hS1; split|]; assumption.
  - constructor. exact Hsource.
Qed.

End TranslatePreservation.

Section TranslateProper.
Context {F : Type -> Type}.
Variable rename : forall X, E X -> F X.

#[global] Instance free_probabilistic_eutt_translate_Proper {R} :
  Proper
    (@probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface R R eq ==>
     @probabilistic_eutt F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface R R eq)
    (PTree.translate rename).
Proof.
  intros t1 t2 Ht. apply free_probabilistic_eutt_translate.
  exact Ht.
Qed.

End TranslateProper.

Section TranslateIdentity.

Definition free_identity_rename (X : Type) (e : E X) : E X := e.

Inductive free_translate_id_state {R} :
    ptree' E MN R -> ptree' E MN R -> Prop :=
  | FTISMain (t : ptree E MN R) :
      free_translate_id_state
        (observe (PTree.translate free_identity_rename t)) (observe t).

Lemma free_translate_id_head_comp {R}
    (hT hS : frontier_head E MN R) :
  free_translate_head_rel free_identity_rename hS hT ->
  @ptree_stable_head_rel E MN R R eq free_translate_id_state hT hS.
Proof.
  intro Hmap. dependent destruction Hmap.
  - constructor. reflexivity.
  - constructor. intro x.
    unfold free_translate_cont. rewrite observe_bind. cbn.
    constructor.
Qed.

(** Renaming by the identity handler is a behavioral unit.  This is not a
    structural law: guarded interpretation inserts an administrative Tau at
    every visible event. *)
Theorem free_probabilistic_eutt_translate_id {R} (t : ptree E MN R) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.translate free_identity_rename t) t.
Proof.
  eapply probabilistic_eutt_coinduction with
    (sim := @free_translate_id_state R).
  - intros sT sS Hsim. dependent destruction Hsim.
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) (observe t0)) as [outS HS].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R)
      (observe (PTree.translate free_identity_rename t0))) as [outT HT].
    eapply stable_hitting_match_of_hitting_lift; [exact HT|exact HS|].
    pose proof (free_translate_hitting_lift
      (rename := free_identity_rename) HS HT) as Hmap.
    eapply FOQLMono.
    + apply FOQLSym. exact Hmap.
    + intros hT hS Hrel. apply free_translate_id_head_comp. exact Hrel.
  - constructor.
Qed.

(** [interp trigger] is the identity interpretation, stated using the public
    handler operation rather than its [translate] abbreviation. *)
Corollary free_probabilistic_eutt_interp_trigger {R} (t : ptree E MN R) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp (fun X e => @PTree.trigger E MN X e) t) t.
Proof.
  change (@probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.translate free_identity_rename t) t).
  apply free_probabilistic_eutt_translate_id.
Qed.

End TranslateIdentity.

End FreeOmegaOperationalCofinality.

Section TranslateComposition.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).
Context {F G : Type -> Type}.
Variable rename1 : forall X, E X -> F X.
Variable rename2 : forall X, F X -> G X.

Definition free_compose_rename (X : Type) (e : E X) : G X :=
  @rename2 X (@rename1 X e).

Inductive free_translate_comp_state {R} :
    ptree' G MN R -> ptree' G MN R -> Prop :=
  | FTCSMain (t : ptree E MN R) :
      free_translate_comp_state
        (observe (PTree.translate rename2 (PTree.translate rename1 t)))
        (observe (PTree.translate free_compose_rename t)).

Lemma free_translate_comp_head {R}
    (hL hR : frontier_head G MN R) :
  (exists hS : frontier_head E MN R,
    (exists hM : frontier_head F MN R,
      free_translate_head_rel rename1 hS hM /\
      @free_translate_head_rel F MN G rename2 R hM hL) /\
    free_translate_head_rel free_compose_rename hS hR) ->
  @ptree_stable_head_rel G MN R R eq free_translate_comp_state hL hR.
Proof.
  intros [hS [[hM [Hsm Hml]] Hsr]].
  dependent destruction Hsm; dependent destruction Hml;
    dependent destruction Hsr.
  - constructor. reflexivity.
  - constructor. intro x.
    unfold free_translate_cont. rewrite !observe_bind. cbn.
    change (free_translate_comp_state
      (observe (PTree.translate rename2 (PTree.translate rename1 (k x))))
      (observe (PTree.translate free_compose_rename (k x)))).
    constructor.
Qed.

(** Pure event renaming is functorial up to the canonical weak
    equivalence.  The proof glues source-to-intermediate-to-left hitting
    transport against the direct source-to-right transport. *)
Theorem free_probabilistic_eutt_translate_compose {R}
    (t : ptree E MN R) :
  @probabilistic_eutt G MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.translate rename2 (PTree.translate rename1 t))
    (PTree.translate free_compose_rename t).
Proof.
  eapply probabilistic_eutt_coinduction with
    (sim := @free_translate_comp_state R).
  - intros sL sR Hsim. dependent destruction Hsim.
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R) (observe t0)) as [outS HS].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R)
      (observe (PTree.translate rename1 t0))) as [outM HM].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel G MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R)
      (observe (PTree.translate rename2
        (PTree.translate rename1 t0)))) as [outL HL].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel G MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface R)
      (observe (PTree.translate free_compose_rename t0))) as [outR HR].
    eapply stable_hitting_match_of_hitting_lift; [exact HL|exact HR|].
    pose proof (free_translate_hitting_lift
      (rename := rename1) HS HM) as Hsm.
    pose proof (free_translate_hitting_lift
      (rename := rename2) HM HL) as Hml.
    pose proof (free_translate_hitting_lift
      (rename := free_compose_rename) HS HR) as Hsr.
    eapply FOQLComp
      with (T := fun hL hS => exists hM,
          free_translate_head_rel rename1 hS hM /\
          @free_translate_head_rel F MN G rename2 R hM hL)
        (U := free_translate_head_rel free_compose_rename)
        (mid := outS).
    + apply FOQLSym.
      eapply FOQLComp with
        (T := free_translate_head_rel rename1)
        (U := @free_translate_head_rel F MN G rename2 R) (mid := outM).
      * exact Hsm.
      * exact Hml.
      * intros hS hL [hM [H1 H2]]. exists hM. split; assumption.
    + exact Hsr.
    + intros hL hR [hS [[hM [H1 H2]] H3]].
      apply free_translate_comp_head.
      exists hS. split; [exists hM; split|]; assumption.
  - constructor.
Qed.

End TranslateComposition.

Section FreeOmegaOperationalCofinalityContinuation.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).

Lemma free_operational_hitting_pstructural {A B}
    (RR : A -> B -> Prop) fuel (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstructural RR t1 t2 ->
  free_omega_lift (frontier_head_rel RR (pstructural RR))
    (operational_hitting_approx (MF := MF) fuel (observe t1))
    (operational_hitting_approx (MF := MF) fuel (observe t2)).
Proof.
  revert t1 t2. induction fuel as [|fuel IH]; intros t1 t2 Hstruct.
  all: pose proof (pstructural_unfold Hstruct) as Hstep;
    dependent destruction Hstep.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [operational_hitting_approx operational_kernel]. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstructural E MN A B RR))
      (FOSample mu (fun _ => FOZero))
      (FOSample mu (fun _ => FOZero))).
    eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros z. reflexivity.
    + intros z z' ->. constructor.
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    cbn [operational_hitting_approx operational_kernel].
    exact (IH _ _ H).
  - rewrite <- x0, <- x. constructor. constructor. exact H.
  - rewrite <- x0, <- x.
    change (free_omega_lift
      (@frontier_head_rel E MN A B RR (@pstructural E MN A B RR))
      (FOSample mu (fun z => operational_hitting_approx (MF := MF)
        fuel (observe (k1 z))))
      (FOSample mu (fun z => operational_hitting_approx (MF := MF)
        fuel (observe (k2 z))))).
    eapply FOLSample with (S := eq).
    + apply sem_lift_refl. intros z. reflexivity.
    + intros z z' ->. apply IH. exact (H z').
Qed.

(** State-level closure used to interpret syntax-sensitive structural
    equivalence inside the canonical stable-hitting coinduction principle. *)
Definition free_pstructural_state {A B} (RR : A -> B -> Prop)
    (s1 : ptree' E MN A) (s2 : ptree' E MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe t1 /\ s2 = observe t2 /\ pstructural RR t1 t2.

(** Structural probabilistic bisimulation is sound for the canonical weak
    equivalence.  Pointwise structural couplings of all finite hitting
    approximants are closed by the FreeOmega limit constructor; visible
    continuations re-enter the coinduction candidate. *)
Theorem free_probabilistic_eutt_of_pstructural {A B}
    (RR : A -> B -> Prop) (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstructural RR t1 t2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2.
Proof.
  intro Hstruct. eapply probabilistic_eutt_coinduction with
    (sim := free_pstructural_state RR).
  - intros s1 s2 [u1 [u2 [-> [-> Hs]]]].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface A) (observe u1)) as [out1 Hout1].
    destruct (stable_hitting_weak_exists
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (@ptree_primitive_kernel E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface B) (observe u2)) as [out2 Hout2].
    eapply stable_hitting_match_of_hitting_lift;
      [exact Hout1|exact Hout2|].
    eapply FOQLMono.
    + unfold stable_hitting_weak in Hout1, Hout2.
      cbn in Hout1, Hout2.
      eapply FOQLComp with (T := eq)
        (U := frontier_head_rel RR (pstructural RR))
        (mid := FOLub (fun fuel => operational_hitting_approx
          (MF := MF) fuel (observe u1))).
      * exact Hout1.
      * eapply FOQLComp with
          (T := frontier_head_rel RR (pstructural RR))
          (U := eq)
          (mid := FOLub (fun fuel => operational_hitting_approx
            (MF := MF) fuel (observe u2))).
        -- apply FOQLLub. intro fuel.
           apply FOQLStructural.
           exact (free_operational_hitting_pstructural
             (RR := RR) fuel Hs).
        -- apply FOQLSym. eapply FOQLMono; [exact Hout2|].
           intros x y ->. reflexivity.
        -- intros x z [y [Hxy ->]]. exact Hxy.
      * intros x z [y [-> Hyz]]. exact Hyz.
    + intros h1 h2 Hhead. dependent destruction Hhead.
      * constructor. exact H.
      * constructor. intro x. exists (k1 x), (k2 x).
        repeat split; try reflexivity. exact (H x).
  - exists t1, t2. repeat split; try reflexivity. exact Hstruct.
Qed.

Lemma free_operational_hitting_pstructural_no_event {A}
    (no_event : forall X, E X -> False) fuel
    (t1 t2 : ptree E MN A) :
  pstructural eq t1 t2 ->
  free_omega_lift eq
    (operational_hitting_approx (MF := MF) fuel (observe t1))
    (operational_hitting_approx (MF := MF) fuel (observe t2)).
Proof.
  intro Hstruct. eapply free_omega_lift_mono with
    (R := frontier_head_rel eq (pstructural eq)).
  - intros h1 h2 Hhead.
    destruct h1 as [a1|X1 e1 k1];
      destruct h2 as [a2|X2 e2 k2].
    + inversion Hhead; subst. reflexivity.
    + exfalso. exact (@no_event X2 e2).
    + exfalso. exact (@no_event X1 e1).
    + exfalso. exact (@no_event X1 e1).
  - exact (free_operational_hitting_pstructural
      (RR := eq) fuel Hstruct).
Qed.

Theorem free_operational_weak_pstructural_no_event {A}
    (no_event : forall X, E X -> False)
    (t1 t2 : ptree E MN A) :
  pstructural eq t1 t2 ->
  forall out,
    @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A (observe t1) out <->
    @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A (observe t2) out.
Proof.
  intros Hstruct out. unfold operational_weak. split; intro Hlim.
  - eapply sem_lub_chain_proper; [|exact Hlim]. intro fuel.
    apply FOQLStructural.
    exact (free_operational_hitting_pstructural_no_event
      no_event fuel Hstruct).
  - eapply sem_lub_chain_proper; [|exact Hlim]. intro fuel.
    apply FOQLStructural.
    apply free_omega_lift_sym.
    eapply free_omega_lift_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (free_operational_hitting_pstructural_no_event
        no_event fuel Hstruct).
Qed.

Corollary free_operational_weak_bind_assoc_no_event {A B C}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) out :
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C
    (observe (PTree.bind (PTree.bind t k) h)) out <->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C
    (observe (PTree.bind t (fun a => PTree.bind (k a) h))) out.
Proof.
  apply free_operational_weak_pstructural_no_event; [exact no_event|].
  apply pstructural_bind_assoc.
Qed.

Lemma free_operational_bind_diagonal_mono {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n m :
  Peano.le n m ->
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF) m t k).
Proof.
  apply (operational_bind_diagonal_mono
    (FI := FreeOmegaObservableSemanticMeasureInterface)
    (FO := FreeOmegaObservableSemanticOmegaInterface)
    (MX := FreeOmegaMixedMeasureInterface)).
Qed.

(** A concrete, finite obligation replacing the abstract Bind lub equality:
    every global-fuel approximant is contained in some diagonal approximant,
    and conversely. *)
Definition free_operational_bind_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (fun fuel => operational_bind_diagonal_approx (MF := MF) fuel t k).

Theorem free_operational_bind_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t k.
Proof.
  intros Hcofinal out. unfold operational_bind_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

Lemma free_operational_bind_ret_approx_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal (Ret a) k.
Proof.
  split; intro n; exists n.
  all: rewrite (observing_observe (bind_ret_ a k)).
  all:
    unfold free_operational_bind_approx_cofinal,
      operational_bind_diagonal_approx,
      operational_head_bind_approx,
      operational_hitting_approx, operational_kernel;
    cbn.
  all: rewrite !stable_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary free_operational_bind_ret_cofinal {A R}
    (a : A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Ret a) k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_ret_approx_cofinal.
Qed.

(** Binding a pure continuation does not introduce a second unbounded
    computation.  Stable heads are mapped immediately, so global primitive
    fuel and diagonal bind fuel coincide rather than merely being cofinal. *)
Definition free_pure_head_bind {A R} (f : A -> R)
    (h : frontier_head E MN A) : frontier_head E MN R :=
  match h with
  | FHRet a => FHRet (f a)
  | @FHVis _ _ _ X e c =>
      FHVis e (fun x => PTree.bind (c x) (fun a => Ret (f a)))
  end.

Lemma free_operational_hitting_bind_ret_map {A R}
    (t : ptree E MN A) (f : A -> R) fuel :
  operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t (fun a => Ret (f a)))) =
  free_omega_bind
    (operational_hitting_approx (MF := MF) fuel (observe t))
    (fun h => FORet (free_pure_head_bind f h)).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t;
    rewrite observe_bind; remember (observe t) as ot eqn:Hot;
    destruct ot as [a|u|X e c|X mu c].
  - reflexivity.
  - cbn [operational_hitting_approx operational_kernel].
    reflexivity.
  - reflexivity.
  - change (FOSample mu (fun _ : X => FOZero) =
      free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (fun h => FORet (free_pure_head_bind f h))).
    reflexivity.
  - reflexivity.
  - cbn [observe operational_hitting_approx operational_kernel].
    exact (IH u).
  - reflexivity.
  - change (FOSample mu (fun x => operational_hitting_approx (MF := MF)
        fuel (observe (PTree.bind (c x) (fun a => Ret (f a))))) =
      free_omega_bind
        (FOSample mu (fun x => operational_hitting_approx (MF := MF)
          fuel (observe (c x))))
        (fun h => FORet (free_pure_head_bind f h))).
    cbn [free_omega_bind].
    f_equal. apply functional_extensionality. intro x.
    exact (IH (c x)).
Qed.

Lemma free_operational_head_bind_ret_map {A R}
    (f : A -> R) fuel (h : frontier_head E MN A) :
  operational_head_bind_approx (MF := MF) fuel
    (fun a => Ret (f a)) h = FORet (free_pure_head_bind f h).
Proof.
  destruct h as [a|X e c].
  - cbn [operational_head_bind_approx free_pure_head_bind].
    assert (Hret : observe (Ret (f a) : ptree E MN R) = RetF (f a))
      by reflexivity.
    rewrite Hret. unfold operational_hitting_approx, operational_kernel.
    cbn. rewrite stable_target_stableE. reflexivity.
  - reflexivity.
Qed.

Lemma free_operational_bind_ret_diagonal_map {A R}
    (t : ptree E MN A) (f : A -> R) fuel :
  operational_bind_diagonal_approx (MF := MF) fuel t
      (fun a => Ret (f a)) =
  free_omega_bind
    (operational_hitting_approx (MF := MF) fuel (observe t))
    (fun h => FORet (free_pure_head_bind f h)).
Proof.
  unfold operational_bind_diagonal_approx.
  change (free_omega_bind
    (operational_hitting_approx (MF := MF) fuel (observe t))
    (operational_head_bind_approx (MF := MF) fuel
      (fun a => Ret (f a))) =
    free_omega_bind
      (operational_hitting_approx (MF := MF) fuel (observe t))
      (fun h => FORet (free_pure_head_bind f h))).
  f_equal. apply functional_extensionality. intro h.
  apply free_operational_head_bind_ret_map.
Qed.

Theorem free_operational_bind_ret_map_approx_cofinal {A R}
    (t : ptree E MN A) (f : A -> R) :
  free_operational_bind_approx_cofinal t (fun a => Ret (f a)).
Proof.
  split; intro fuel; exists fuel.
  - rewrite free_operational_hitting_bind_ret_map,
      free_operational_bind_ret_diagonal_map.
    apply free_omega_approx_refl. intros h. reflexivity.
  - rewrite free_operational_hitting_bind_ret_map,
      free_operational_bind_ret_diagonal_map.
    apply free_omega_approx_refl. intros h. reflexivity.
Qed.

Corollary free_operational_bind_ret_map_cofinal {A R}
    (t : ptree E MN A) (f : A -> R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t
    (fun a => Ret (f a)).
Proof.
  apply free_operational_bind_cofinal.
  exact (free_operational_bind_ret_map_approx_cofinal t f).
Qed.

(** A shared global primitive budget is contained in the more generous
    diagonal allocation that gives the same budget to the source and to the
    continuation. *)
Lemma free_operational_bind_hitting_le_diagonal {A R}
    (fuel : nat) (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind t k)))
    (operational_bind_diagonal_approx (MF := MF) fuel t k).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  - rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c];
      unfold operational_bind_diagonal_approx; rewrite <- Hot.
    + change (free_omega_approx eq
        (operational_hitting_approx (MF := MF) 0 (observe (k a)))
        (free_omega_bind (FORet (FHRet a))
          (operational_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + constructor.
    + change (free_omega_approx eq
        (FORet (FHVis e (fun x => PTree.bind (c x) k)))
        (free_omega_bind (FORet (FHVis e c))
          (operational_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + change (free_omega_approx eq
        (FOSample mu (fun _ : X => FOZero))
        (free_omega_bind (FOSample mu (fun _ : X => FOZero))
          (operational_head_bind_approx (MF := MF) 0 k))).
      cbn [free_omega_bind].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. constructor.
  - rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + unfold operational_bind_diagonal_approx. rewrite <- Hot.
      cbn [operational_hitting_approx operational_kernel
        operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + unfold operational_bind_diagonal_approx. rewrite <- Hot.
      cbn [operational_hitting_approx operational_kernel
        operational_head_bind_approx].
      eapply free_omega_approx_trans.
      * apply IH.
      * unfold operational_bind_diagonal_approx.
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros x. reflexivity.
        -- intros h1 h2 ->.
           destruct h2; cbn [operational_head_bind_approx].
           ++ apply free_operational_hitting_mono. apply le_S, le_n.
           ++ apply free_omega_approx_refl. intros z. reflexivity.
    + unfold operational_bind_diagonal_approx. rewrite <- Hot.
      cbn [operational_hitting_approx operational_kernel
        operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + unfold operational_bind_diagonal_approx. rewrite <- Hot.
      change (free_omega_approx eq
        (FOSample mu (fun x => operational_hitting_approx (MF := MF)
          fuel (observe (PTree.bind (c x) k))))
        (free_omega_bind
          (FOSample mu (fun x => operational_hitting_approx (MF := MF)
            fuel (observe (c x))))
          (operational_head_bind_approx (MF := MF)
            (S fuel) k))).
      cbn [free_omega_bind].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. eapply free_omega_approx_trans.
        -- apply IH.
        -- unfold operational_bind_diagonal_approx.
           eapply free_omega_approx_bind with (R := eq) (T := eq).
           ++ apply free_omega_approx_refl. intros z. reflexivity.
           ++ intros h1 h2 ->.
              destruct h2; cbn [operational_head_bind_approx].
              ** apply free_operational_hitting_mono. apply le_S, le_n.
              ** apply free_omega_approx_refl. intros z. reflexivity.
Qed.

(** Split-budget form of a bind approximation.  It is useful for proving
    that sequentially spending [source_fuel] and [continuation_fuel] is
    implementable by their sum in the primitive global machine. *)
Definition free_operational_bind_split_approx {A R}
    (source_fuel continuation_fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
    MF (frontier_head E MN R) :=
  free_omega_bind
    (operational_hitting_approx (MF := MF) source_fuel (observe t))
    (operational_head_bind_approx (MF := MF) continuation_fuel k).

Lemma free_operational_bind_split_le_hitting {A R}
    (source_fuel continuation_fuel : nat)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (free_operational_bind_split_approx
      source_fuel continuation_fuel t k)
    (operational_hitting_approx (MF := MF)
      (source_fuel + continuation_fuel)
      (observe (PTree.bind t k))).
Proof.
  revert t. induction source_fuel as [|source_fuel IH]; intro t.
  - unfold free_operational_bind_split_approx.
    rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + change (free_omega_approx eq
        (free_omega_bind (FORet (FHRet a))
          (operational_head_bind_approx (MF := MF)
            continuation_fuel k))
        (operational_hitting_approx (MF := MF)
          continuation_fuel (observe (k a)))).
      cbn [free_omega_bind operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + constructor.
    + assert (Hvis : observe (Vis e (fun x => PTree.bind (c x) k)) =
          VisF e (fun x => PTree.bind (c x) k)).
      { reflexivity. }
      rewrite Hvis.
      cbv [operational_hitting_approx operational_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasureInterface free_omega_bind
        FreeOmegaSemanticMeasureInterface
        operational_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      cbn [observe].
      rewrite !stable_target_stableE.
      cbv [sem_ret FreeOmegaObservableSemanticMeasureInterface
        FreeOmegaSemanticMeasureInterface free_omega_bind].
      cbn [free_omega_bind operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + cbv [operational_hitting_approx operational_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasureInterface free_omega_bind
        FreeOmegaSemanticMeasureInterface
        operational_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. constructor.
  - unfold free_operational_bind_split_approx.
    rewrite observe_bind. remember (observe t) as ot eqn:Hot.
    destruct ot as [a|u|X e c|X mu c].
    + change (free_omega_approx eq
        (operational_hitting_approx (MF := MF)
          continuation_fuel (observe (k a)))
        (operational_hitting_approx (MF := MF)
          (S source_fuel + continuation_fuel) (observe (k a)))).
      apply free_operational_hitting_mono. lia.
    + change (free_omega_approx eq
        (free_operational_bind_split_approx
          source_fuel continuation_fuel u k)
        (operational_hitting_approx (MF := MF)
          (source_fuel + continuation_fuel)
          (observe (PTree.bind u k)))).
      apply IH.
    + assert (Hvis : observe (Vis e (fun x => PTree.bind (c x) k)) =
          VisF e (fun x => PTree.bind (c x) k)).
      { reflexivity. }
      rewrite Hvis.
      cbv [operational_hitting_approx operational_kernel sem_bind sem_ret
        FreeOmegaObservableSemanticMeasureInterface free_omega_bind
        FreeOmegaSemanticMeasureInterface
        operational_target_approx stable_hitting_approx
        ptree_primitive_kernel observe].
      cbn [observe].
      rewrite !stable_target_stableE.
      cbv [sem_ret FreeOmegaObservableSemanticMeasureInterface
        FreeOmegaSemanticMeasureInterface free_omega_bind].
      cbn [free_omega_bind operational_head_bind_approx].
      apply free_omega_approx_refl. intros x. reflexivity.
    + change (free_omega_approx eq
        (FOSample mu (fun x => free_operational_bind_split_approx
          source_fuel continuation_fuel (c x) k))
        (FOSample mu (fun x => operational_hitting_approx (MF := MF)
          (source_fuel + continuation_fuel)
          (observe (PTree.bind (c x) k))))).
      eapply FOApproxSample with (S := eq).
      * apply sem_lift_refl. intros x. reflexivity.
      * intros x y ->. apply IH.
Qed.

Lemma free_operational_bind_diagonal_le_hitting {A R}
    (fuel : nat) (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF) fuel t k)
    (operational_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.bind t k))).
Proof.
  change (free_omega_approx eq
    (free_operational_bind_split_approx fuel fuel t k)
    (operational_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.bind t k)))).
  replace (2 * fuel) with (fuel + fuel) by lia.
  apply free_operational_bind_split_le_hitting.
Qed.

Theorem free_operational_bind_approx_cofinal_all {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k.
Proof.
  split.
  - intro fuel. exists fuel.
    apply free_operational_bind_hitting_le_diagonal.
  - intro fuel. exists (2 * fuel).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply free_operational_bind_diagonal_le_hitting.
Qed.

Corollary free_operational_bind_cofinal_all {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_approx_cofinal_all.
Qed.

Section FreeOperationalInterpCofinality.
Context {F : Type -> Type}.
Variable handler : forall X, E X -> ptree F MN X.

Definition free_operational_interp_approx_cofinal {R}
    (t : ptree E MN R) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (fun fuel => operational_interp_diagonal_approx fuel handler t).

Lemma free_operational_interp_hitting_le_diagonal {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t)))
    (operational_interp_diagonal_approx fuel handler t).
Proof.
  revert t. induction fuel as [|fuel IH]; intro t.
  all: unfold operational_interp_diagonal_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [operational_hitting_approx operational_kernel
      operational_interp_head_approx operational_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - constructor.
  - change (free_omega_approx eq
      (FOSample mu (fun _ : X => FOZero))
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (operational_interp_head_approx (MF := MF) (R := R) 0 handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - cbn [operational_hitting_approx operational_kernel
      operational_interp_head_approx operational_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [operational_hitting_approx operational_kernel].
    eapply free_omega_approx_trans; [apply IH|].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intro h. reflexivity.
    + intros h1 h2 ->. apply free_operational_hitting_mono. lia.
  - cbn [operational_hitting_approx operational_kernel
      operational_interp_head_approx free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (FOSample mu (fun x => operational_hitting_approx (MF := MF)
        fuel (observe (PTree.interp handler (k x)))))
      (free_omega_bind
        (FOSample mu (fun x => operational_hitting_approx (MF := MF)
          fuel (observe (k x))))
        (operational_interp_head_approx (MF := MF) (R := R)
          (S fuel) handler))).
    cbn [free_omega_bind]. eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. eapply free_omega_approx_trans; [apply IH|].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intro h. reflexivity.
      * intros h1 h2 ->. apply free_operational_hitting_mono. lia.
Qed.

Definition free_operational_interp_split_approx {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
    MF (frontier_head F MN R) :=
  free_omega_bind
    (operational_hitting_approx (MF := MF) source_fuel (observe t))
    (operational_interp_head_approx (MF := MF) (R := R)
      head_fuel handler).

Lemma free_operational_interp_split_le_hitting {R}
    (source_fuel head_fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (free_operational_interp_split_approx source_fuel head_fuel t)
    (operational_hitting_approx (MF := MF) (source_fuel + head_fuel)
      (observe (PTree.interp handler t))).
Proof.
  revert t. induction source_fuel as [|source_fuel IH]; intro t.
  all: unfold free_operational_interp_split_approx;
    rewrite observe_interp; remember (observe t) as ot eqn:Hot;
    destruct ot as [r|u|X e k|X mu k].
  - cbn [operational_hitting_approx operational_kernel
      operational_interp_head_approx operational_interp_head_tree
      free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - constructor.
  - cbn [free_omega_bind operational_interp_head_approx
      operational_interp_head_tree].
    apply free_omega_approx_refl. intro h. reflexivity.
  - change (free_omega_approx eq
      (free_omega_bind (FOSample mu (fun _ : X => FOZero))
        (operational_interp_head_approx (MF := MF) (R := R)
          head_fuel handler))
      (operational_hitting_approx (MF := MF) head_fuel
        (observe (Prob mu (fun x => PTree.interp handler (k x)))))).
    cbn [free_omega_bind operational_hitting_approx operational_kernel].
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. constructor.
  - unfold operational_hitting_approx, operational_kernel,
      operational_interp_head_approx, operational_interp_head_tree.
    cbn. rewrite !stable_target_stableE. cbn [free_omega_bind].
    apply free_omega_approx_refl. intro h. reflexivity.
  - cbn [operational_hitting_approx operational_kernel]. apply IH.
  - cbn [free_omega_bind operational_interp_head_approx
      operational_interp_head_tree].
    apply free_operational_hitting_mono. lia.
  - change (free_omega_approx eq
      (FOSample mu (fun x => free_operational_interp_split_approx
        source_fuel head_fuel (k x)))
      (FOSample mu (fun x => operational_hitting_approx (MF := MF)
        (source_fuel + head_fuel)
        (observe (PTree.interp handler (k x)))))).
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Lemma free_operational_interp_diagonal_le_hitting {R}
    (fuel : nat) (t : ptree E MN R) :
  free_omega_approx eq
    (operational_interp_diagonal_approx fuel handler t)
    (operational_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t))).
Proof.
  change (free_omega_approx eq
    (free_operational_interp_split_approx fuel fuel t)
    (operational_hitting_approx (MF := MF) (2 * fuel)
      (observe (PTree.interp handler t)))).
  replace (2 * fuel) with (fuel + fuel) by lia.
  apply free_operational_interp_split_le_hitting.
Qed.

Theorem free_operational_interp_approx_cofinal_all {R}
    (t : ptree E MN R) : free_operational_interp_approx_cofinal t.
Proof.
  split.
  - intro fuel. exists fuel.
    apply free_operational_interp_hitting_le_diagonal.
  - intro fuel. exists (2 * fuel).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply free_operational_interp_diagonal_le_hitting.
Qed.

Corollary free_operational_interp_cofinal_all {R}
    (t : ptree E MN R) :
  @operational_interp_cofinal E F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R handler t.
Proof.
  intro out. unfold operational_interp_cofinal.
  apply free_omega_cofinal_lub_iff.
  apply free_operational_interp_approx_cofinal_all.
Qed.

End FreeOperationalInterpCofinality.

Definition frontier_head_is_ret {R}
    (h : frontier_head E MN R) : Prop :=
  match h with
  | FHRet _ => True
  | @FHVis _ _ _ X e k => False
  end.

Definition frontier_head_ret_bind_front {A R}
    (front : A -> MF (frontier_head E MN R))
    (h : frontier_head E MN A) : MF (frontier_head E MN R) :=
  match h with
  | FHRet a => front a
  | @FHVis _ _ _ X e k => FOZero
  end.

(** Lift a coupling of closed-source heads through Ret-only continuations.
    Related returns use the supplied continuation coupling; related visible
    heads are discarded on both sides.  Thus clients do not need to unfold
    [FOQLBind] merely to place a closed sampler before an eventful context. *)
Theorem free_sem_lift_ret_bind_front
    {A1 A2 R1 R2}
    (RA : A1 -> A2 -> Prop)
    (simA : ptree E MN A1 -> ptree E MN A2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (simR : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (hs1 : MF (frontier_head E MN A1))
    (hs2 : MF (frontier_head E MN A2))
    (front1 : A1 -> MF (frontier_head E MN R1))
    (front2 : A2 -> MF (frontier_head E MN R2)) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _ (frontier_head_rel RA simA) hs1 hs2 ->
  (forall a1 a2, RA a1 a2 ->
    @sem_lift MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      _ _ (frontier_head_rel RR simR) (front1 a1) (front2 a2)) ->
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _ (frontier_head_rel RR simR)
    (free_omega_bind hs1 (frontier_head_ret_bind_front front1))
    (free_omega_bind hs2 (frontier_head_ret_bind_front front2)).
Proof.
  intros Hsource Hfront. eapply FOQLBind; [exact Hsource|].
  intros h1 h2 Hhead. inversion Hhead; subst; clear Hhead.
  - cbn [frontier_head_ret_bind_front]. apply Hfront. exact H.
  - cbn [frontier_head_ret_bind_front].
    apply FOQLStructural. constructor.
Qed.

(** If the complete source behavior is almost everywhere a return head,
    bind may discard the unreachable visible-head branch.  This is the
    generic composition rule needed when a closed sampler is embedded in an
    eventful client. *)
Theorem free_stable_hitting_weak_bind_ret_only
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R)
    (hs : MF (frontier_head E MN A))
    (front : A -> MF (frontier_head E MN R)) :
  free_omega_ae frontier_head_is_ret hs ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A (observe t) hs ->
  (forall a,
    @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface R
      (observe (k a)) (front a)) ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (PTree.bind t k))
    (free_omega_bind hs (frontier_head_ret_bind_front front)).
Proof.
  intros Hret Hsource Hfront.
  pose (full :=
    free_omega_bind hs (frontier_head_bind_front k front)).
  assert (Hfull :
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface R
        (observe (PTree.bind t k)) full).
  { unfold full. eapply (stable_hitting_weak_bind
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)).
    - apply free_operational_bind_cofinal_all.
    - exact Hsource.
    - exact Hfront. }
  assert (Hrestricted :
      @sem_lift MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ (fun h1 h2 => h1 = h2 /\ frontier_head_is_ret h1)
        hs hs).
  { eapply FOQLAERestrict with
      (T := eq) (P := frontier_head_is_ret)
      (Q := frontier_head_is_ret).
    - apply free_omega_qlift_refl. intro h. reflexivity.
    - exact Hret.
    - exact Hret.
    - intros h1 h2 [-> [H1 H2]]. split; [reflexivity|exact H1]. }
  assert (Houtputs :
      @sem_lift MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ eq full
        (free_omega_bind hs (frontier_head_ret_bind_front front))).
  { unfold full. eapply FOQLBind; [exact Hrestricted|].
    intros h1 h2 [-> Hret1].
    destruct h2 as [a|X e c]; [|contradiction].
    cbn [frontier_head_bind_front frontier_head_ret_bind_front].
    apply free_omega_qlift_refl. intro h. reflexivity. }
  unfold operational_weak, stable_hitting_weak in Hfull |- *.
  eapply FOQLComp with (T := eq) (U := eq) (mid := full).
  - apply FOQLSym. eapply FOQLMono; [exact Houtputs|].
    intros x y ->. reflexivity.
  - exact Hfull.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** Unconditional monadic congruence for the maintained unbounded backend.
    The generic theorem keeps its local scheduling premise; FreeOmega now
    discharges it for every eventful PTree. *)
Corollary free_probabilistic_eutt_bind
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR t1 t2 ->
  (forall r1 r2, RR r1 r2 ->
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A A eq (k1 r1) (k2 r2)) ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intros Hsource Hk.
  eapply probabilistic_eutt_bind.
  - intros B S t k. apply free_operational_bind_cofinal_all.
  - exact Hsource.
  - exact Hk.
  Unshelve. all: try typeclasses eauto.
Qed.

(** Canonical Monad laws.  They are consequences of structural soundness,
    not additional cases of the behavioral generator. *)
Theorem free_probabilistic_eutt_bind_ret_l {A B}
    (a : A) (k : A -> ptree E MN B) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B B eq
    (PTree.bind (Ret a) k) (k a).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural.
  exact (observing_observe (bind_ret_ a k)).
Qed.

Theorem free_probabilistic_eutt_bind_ret_r {A}
    (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.bind t (fun x => Ret x)) t.
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_bind_ret_r.
Qed.

Theorem free_probabilistic_eutt_bind_assoc {A B C}
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_bind_assoc.
Qed.

(** Canonical Functor laws.  [PTree.fmap] is the monadic definition, but the
    named laws keep client proofs independent of that implementation. *)
Theorem free_probabilistic_eutt_fmap_id {A} (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.fmap (fun x => x) t) t.
Proof.
  unfold PTree.fmap. apply free_probabilistic_eutt_bind_ret_r.
Qed.

Theorem free_probabilistic_eutt_fmap_compose {A B C}
    (f : A -> B) (g : B -> C) (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  unfold PTree.fmap.
  eapply pstructural_trans.
  - apply pstructural_bind_assoc.
  - eapply pstructural_bind with (RA := eq) (RB := eq).
    + intros x1 x2 ->. apply observe_eq_pstructural.
      exact (observing_observe (bind_ret_ (f x2) (fun y => Ret (g y)))).
    + apply pstructural_refl.
Qed.

Theorem free_probabilistic_eutt_fmap_bind {A B C}
    (f : B -> C) (t : ptree E MN A) (k : A -> ptree E MN B) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.fmap f (PTree.bind t k))
    (PTree.bind t (fun x => PTree.fmap f (k x))).
Proof.
  unfold PTree.fmap. apply free_probabilistic_eutt_bind_assoc.
Qed.

(** One guarded unfolding of [iter]. *)
Theorem free_probabilistic_eutt_iter_unfold {I R}
    (step : I -> ptree E MN (I + R)) (i : I) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step i)
    (PTree.bind (step i) (fun lr =>
      match lr with
      | inl i' => Tau (PTree.iter step i')
      | inr r => Ret r
      end)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural.
  exact (observing_observe (unfold_aloop_ step i)).
Qed.

(** Syntax-directed iter congruence.  The stronger behavioral congruence is
    intentionally separated: this rule is assumption-free because its step
    relation is the structural baseline. *)
Theorem free_probabilistic_eutt_iter_structural {I R}
    (step1 step2 : I -> ptree E MN (I + R)) (i : I) :
  (forall j, pstructural eq (step1 j) (step2 j)) ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  intro Hstep. apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_iter. exact Hstep.
Qed.

(** Heterogeneous relational fusion for iteration.  This subsumes ordinary
    structural congruence and supports state refinement between loops with
    different index and result types. *)
Theorem free_probabilistic_eutt_iter_rel
    {I1 I2 R1 R2}
    (SI : I1 -> I2 -> Prop) (RR : R1 -> R2 -> Prop)
    (f : I1 -> ptree E MN (I1 + R1))
    (g : I2 -> ptree E MN (I2 + R2))
    (Hstep : forall i1 i2, SI i1 i2 ->
      pstructural (pstructural_iter_sum_rel SI RR) (f i1) (g i2))
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter f i1) (PTree.iter g i2).
Proof.
  intro Hij. apply free_probabilistic_eutt_of_pstructural.
  eapply pstructural_iter_rel; eauto.
Qed.

#[global] Instance free_probabilistic_eutt_bind_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} :
  Proper
    (@probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A A eq ==>
      pointwise_relation A
        (@probabilistic_eutt E MN MF
          (FreeOmegaObservableSemanticMeasureInterface
            (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasureInterface
          FreeOmegaObservableSemanticOmegaInterface B B eq) ==>
      @probabilistic_eutt E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface B B eq)
    (@PTree.bind E MN A B).
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  eapply free_probabilistic_eutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

#[global] Instance free_probabilistic_eutt_fmap_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} (f : A -> B) :
  Proper
    (@probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A A eq ==>
     @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface B B eq)
    (PTree.fmap f).
Proof.
  intros t1 t2 Ht. unfold PTree.fmap.
  eapply free_probabilistic_eutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. apply probabilistic_eutt_refl.
Qed.

Theorem free_operational_bind_approx_cofinal_no_event {A R}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k.
Proof.
  apply free_operational_bind_approx_cofinal_all.
Qed.

Corollary free_operational_bind_cofinal_no_event {A R}
    (no_event : forall X, E X -> False)
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R t k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_approx_cofinal_no_event. exact no_event.
Qed.

Section NestedNoEventGrid.
Context {I A R : Type}.
Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable sample : ptree E MN A.
Variable round : I -> A -> I + R.

Definition free_nested_step (i : I) : ptree E MN (I + R) :=
  PTree.bind sample (fun a => Ret (round i a)).

Definition free_nested_program (i : I) : ptree E MN R :=
  PTree.iter free_nested_step i.

Definition free_nested_after (i : I) (a : A) : ptree E MN R :=
  match round i a with
  | inl i' => Tau (free_nested_program i')
  | inr r => Ret r
  end.

Lemma free_nested_ret_after_structural (i : I) (a : A) :
  pstructural eq
    (PTree.bind (Ret (round i a)) (fun lr =>
      match lr with
      | inl i' => Tau (free_nested_program i')
      | inr r => Ret r
      end))
    (free_nested_after i a).
Proof.
  apply observe_eq_pstructural. unfold free_nested_after. rewrite observe_bind.
  destruct (round i a); reflexivity.
Qed.

(** One canonical operational round, obtained solely from the coinductive
    [iter] unfolding and structural bind laws. *)
Lemma free_nested_program_unfold_structural (i : I) :
  pstructural eq (free_nested_program i)
    (PTree.bind sample (free_nested_after i)).
Proof.
  set (handler := fun lr : I + R =>
    match lr with
    | inl i' => Tau (free_nested_program i')
    | inr r => Ret r
    end).
  eapply pstructural_trans.
  - apply observe_eq_pstructural.
    exact (observing_observe (unfold_aloop_ free_nested_step i)).
  - eapply pstructural_trans.
    + unfold free_nested_step.
      apply pstructural_bind_assoc.
    + eapply pstructural_bind.
      * intros a1 a2 ->. unfold handler.
        apply free_nested_ret_after_structural.
      * apply pstructural_refl.
Qed.

Lemma free_nested_program_hitting_unfold (fuel : nat) (i : I) :
  free_omega_lift eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (free_nested_program i)))
    (operational_hitting_approx (MF := MF) fuel
      (observe (PTree.bind sample (free_nested_after i)))).
Proof.
  apply free_operational_hitting_pstructural_no_event.
  - exact no_event.
  - apply free_nested_program_unfold_structural.
Qed.

Definition free_no_event_head_value_for {X}
    (h : frontier_head E MN X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (no_event e)
  end.

Definition free_no_event_head_value
    (h : frontier_head E MN A) : A :=
  free_no_event_head_value_for h.

Lemma free_no_event_head_ret (h : frontier_head E MN A) :
  exists a, h = FHRet a.
Proof.
  destruct h as [a|X e c].
  - exists a. reflexivity.
  - exfalso. exact (no_event e).
Qed.

Lemma free_omega_approx_monotone_nat {X}
    (chain : nat -> MF X)
    (Hstep : forall n, free_omega_approx eq (chain n) (chain (S n))) :
  forall n m, n <= m -> free_omega_approx eq (chain n) (chain m).
Proof.
  intros n m Hle. induction Hle.
  - apply free_omega_approx_refl. intros x. reflexivity.
  - eapply free_omega_approx_trans; [exact IHHle|apply Hstep].
Qed.

(** [outer] bounds how many completed sampler results may be consumed;
    [inner] bounds primitive execution inside every sampler invocation. *)
Fixpoint free_nested_execution_grid (outer inner : nat) (i : I) :
    MF (frontier_head E MN R) :=
  match outer with
  | O => FOZero
  | Datatypes.S outer' =>
      free_omega_bind
        (operational_hitting_approx (MF := MF) inner (observe sample))
        (fun h =>
          match round i (free_no_event_head_value h) with
          | inl i' => free_nested_execution_grid outer' inner i'
          | inr r => FORet (FHRet r)
          end)
  end.

(** Finite productivity data for a genuinely nested execution.  Unlike the
    earlier one-dimensional iteration certificate, the structured side has
    two independent budgets.  No finite budget is required to contain the
    complete AST sampler: every obligation compares only finite primitive
    execution with one finite grid cell.

    The schedules need not preserve indices.  This is essential because a
    global primitive budget is shared by all sampler invocations, whereas a
    grid cell grants its [inner] budget afresh in each of [outer] rounds. *)
Record free_nested_productivity_certificate (i : I) := {
  nested_operational_to_grid_outer : nat -> nat;
  nested_operational_to_grid_inner : nat -> nat;
  nested_grid_to_operational : nat -> nat -> nat;
  nested_operational_to_grid_sound : forall fuel,
    free_omega_approx eq
      (operational_hitting_approx (MF := MF) fuel
        (observe (free_nested_program i)))
      (free_nested_execution_grid
        (nested_operational_to_grid_outer fuel)
        (nested_operational_to_grid_inner fuel) i);
  nested_grid_to_operational_sound : forall outer inner,
    free_omega_approx eq
      (free_nested_execution_grid outer inner i)
      (operational_hitting_approx (MF := MF)
        (nested_grid_to_operational outer inner)
        (observe (free_nested_program i)))
}.

(** The corresponding row limit replaces the finite inner hitting chain by
    its complete AST output, while retaining finite outer fuel. *)
Fixpoint free_nested_row_out
    (sample_out : MF (frontier_head E MN A))
    (outer : nat) (i : I) : MF (frontier_head E MN R) :=
  match outer with
  | O => FOZero
  | Datatypes.S outer' =>
      free_omega_bind sample_out (fun h =>
        match round i (free_no_event_head_value h) with
        | inl i' => free_nested_row_out sample_out outer' i'
        | inr r => FORet (FHRet r)
        end)
  end.

(** Low-level finite-round meaning corresponding to [free_nested_row_out]. *)
Fixpoint free_nested_measure_row
    (sample_measure : MN A) (outer : nat) (i : I) : MN R :=
  match outer with
  | O => sem_zero
  | S outer' =>
      sem_bind sample_measure (fun a =>
        match round i a with
        | inl i' => free_nested_measure_row sample_measure outer' i'
        | inr r => sem_ret r
        end)
  end.

Section NestedRowDenotation.
Context `{DB : @FreeOmegaDenotationBindLaws MN NI NO}.

Lemma free_nested_row_out_denotes
    (sample_out : MF (frontier_head E MN A))
    (sample_measure : MN A)
    (Hsample : free_omega_denotes
      (@free_no_event_head_value_for A)
      sample_out sample_measure) :
  forall outer i,
    free_omega_denotes
      (@free_no_event_head_value_for R)
      (free_nested_row_out sample_out outer i)
      (free_nested_measure_row sample_measure outer i).
Proof.
  induction outer as [|outer IH]; intro i.
  - apply free_omega_observes_denotes. constructor.
  - cbn [free_nested_row_out free_nested_measure_row].
    eapply free_omega_denotes_bind.
    + exact Hsample.
    + intro h. destruct (free_no_event_head_ret h) as [a ->].
      cbn [free_no_event_head_value free_no_event_head_value_for].
      destruct (round i a) as [i'|r].
      * apply IH.
      * apply free_omega_observes_denotes. constructor.
Qed.

End NestedRowDenotation.

Section NestedLimitDenotation.
Context `{DO : @FreeOmegaDenotationOmegaLaws MN NI NO}.

Lemma free_nested_rows_lub_denotes
    (sample_out : MF (frontier_head E MN A))
    (sample_measure : MN A)
    (Hrows : forall outer i,
      free_omega_denotes
        (@free_no_event_head_value_for R)
        (free_nested_row_out sample_out outer i)
        (free_nested_measure_row sample_measure outer i))
    (i : I) out :
  sem_lub (fun outer => free_nested_measure_row
      sample_measure outer i) out ->
  free_omega_denotes
    (@free_no_event_head_value_for R)
    (FOLub (fun outer => free_nested_row_out sample_out outer i)) out.
Proof.
  intro Hlub. eapply free_omega_denotes_lub.
  - intro outer. apply Hrows.
  - exact Hlub.
Qed.

End NestedLimitDenotation.

Lemma free_nested_execution_grid_inner_increasing outer :
  forall i inner,
    free_omega_approx eq
      (free_nested_execution_grid outer inner i)
      (free_nested_execution_grid outer (Datatypes.S inner) i).
Proof.
  induction outer as [|outer IH]; intros i inner.
  - constructor.
  - cbn [free_nested_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_operational_hitting_mono. apply le_S, le_n.
    + intros h1 h2 ->.
      destruct (round i (free_no_event_head_value h2)) as [i'|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_nested_operational_to_grid_sound fuel :
  forall i,
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (free_nested_program i)))
    (free_nested_execution_grid (S fuel) fuel i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - eapply free_omega_approx_trans.
    + apply free_omega_lift_to_approx.
      apply free_nested_program_hitting_unfold.
    + eapply free_omega_approx_trans.
      * apply free_operational_bind_hitting_le_diagonal.
      * unfold operational_bind_diagonal_approx.
        cbn [free_nested_execution_grid].
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros h. reflexivity.
        -- intros h1 h2 ->.
           destruct (free_no_event_head_ret h2) as [a ->].
           cbn [operational_head_bind_approx free_no_event_head_value
             free_no_event_head_value_for].
           unfold free_nested_after. destruct (round i a) as [i'|r].
           ++ cbn [operational_hitting_approx operational_kernel].
              constructor.
           ++ cbn [operational_hitting_approx operational_kernel].
              try rewrite stable_target_stableE.
              apply free_omega_approx_refl. intros x. reflexivity.
  - eapply free_omega_approx_trans.
    + apply free_omega_lift_to_approx.
      apply free_nested_program_hitting_unfold.
    + eapply free_omega_approx_trans.
      * apply free_operational_bind_hitting_le_diagonal.
      * unfold operational_bind_diagonal_approx.
        cbn [free_nested_execution_grid].
        eapply free_omega_approx_bind with (R := eq) (T := eq).
        -- apply free_omega_approx_refl. intros h. reflexivity.
        -- intros h1 h2 ->.
           destruct (free_no_event_head_ret h2) as [a ->].
           cbn [operational_head_bind_approx free_no_event_head_value
             free_no_event_head_value_for].
           unfold free_nested_after. destruct (round i a) as [i'|r].
           ++ cbn [operational_hitting_approx operational_kernel].
              eapply free_omega_approx_trans.
              ** apply IH.
              ** apply free_omega_approx_monotone_nat with
                    (chain := fun inner =>
                      free_nested_execution_grid (S fuel) inner i').
                 --- intro inner.
                     apply free_nested_execution_grid_inner_increasing.
                 --- apply le_S, le_n.
           ++ cbn [operational_hitting_approx operational_kernel].
              try rewrite stable_target_stableE.
              apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_nested_execution_grid_outer_increasing inner :
  forall outer i,
    free_omega_approx eq
      (free_nested_execution_grid outer inner i)
      (free_nested_execution_grid (Datatypes.S outer) inner i).
Proof.
  induction outer as [|outer IH]; intro i.
  - constructor.
  - cbn [free_nested_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros h. reflexivity.
    + intros h1 h2 ->.
      destruct (round i (free_no_event_head_value h2)) as [i'|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Fixpoint free_nested_grid_operational_fuel
    (outer inner : nat) : nat :=
  match outer with
  | O => O
  | S outer' => inner + S (free_nested_grid_operational_fuel outer' inner)
  end.

Lemma free_nested_grid_to_operational_sound outer :
  forall inner i,
  free_omega_approx eq
    (free_nested_execution_grid outer inner i)
    (operational_hitting_approx (MF := MF)
      (free_nested_grid_operational_fuel outer inner)
      (observe (free_nested_program i))).
Proof.
  induction outer as [|outer IH]; intros inner i.
  - constructor.
  - cbn [free_nested_execution_grid free_nested_grid_operational_fuel].
    eapply free_omega_approx_trans with
      (nu := free_operational_bind_split_approx inner
        (S (free_nested_grid_operational_fuel outer inner))
        sample (free_nested_after i)).
    +
      unfold free_operational_bind_split_approx.
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (free_no_event_head_ret h2) as [a ->].
        cbn [free_no_event_head_value free_no_event_head_value_for
          operational_head_bind_approx].
        unfold free_nested_after. destruct (round i a) as [i'|r].
        -- cbn [operational_hitting_approx operational_kernel].
           apply IH.
        -- cbn [operational_hitting_approx operational_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
    + eapply free_omega_approx_trans.
      * apply free_operational_bind_split_le_hitting.
      * apply free_omega_lift_to_approx.
        eapply free_omega_lift_mono.
        -- intros x y Hyx. symmetry. exact Hyx.
        -- apply free_omega_lift_sym.
           apply free_nested_program_hitting_unfold.
Qed.

Theorem free_nested_productivity (i : I) :
  free_nested_productivity_certificate i.
Proof.
  refine {|
    nested_operational_to_grid_outer := S;
    nested_operational_to_grid_inner := fun fuel => fuel;
    nested_grid_to_operational := free_nested_grid_operational_fuel
  |}.
  - intro fuel. apply free_nested_operational_to_grid_sound.
  - intros outer inner. apply free_nested_grid_to_operational_sound.
Qed.

(** A finite productivity certificate is sufficient for the canonical
    program/grid omega-limit bridge.  Monotonicity in both grid coordinates
    moves arbitrary scheduled cells to the diagonal. *)
Theorem free_nested_productivity_diagonal_cofinal (i : I) :
  free_nested_productivity_certificate i ->
  @operational_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i))
    (fun outer inner => free_nested_execution_grid outer inner i).
Proof.
  intro cert. intro out. apply free_omega_cofinal_lub_iff. split.
  - intro fuel.
    set (outer := nested_operational_to_grid_outer cert fuel).
    set (inner := nested_operational_to_grid_inner cert fuel).
    exists (Nat.max outer inner).
    eapply free_omega_approx_trans.
    + exact (nested_operational_to_grid_sound cert fuel).
    + eapply free_omega_approx_trans.
      * apply free_omega_approx_monotone_nat with
          (chain := fun n => free_nested_execution_grid n inner i).
        -- intros n. apply free_nested_execution_grid_outer_increasing.
        -- apply Nat.le_max_l.
      * apply free_omega_approx_monotone_nat with
          (chain := fun n => free_nested_execution_grid
            (Nat.max outer inner) n i).
        -- intros n. apply free_nested_execution_grid_inner_increasing.
        -- apply Nat.le_max_r.
  - intro diagonal.
    exists (nested_grid_to_operational cert diagonal diagonal).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (nested_grid_to_operational_sound cert diagonal diagonal).
Qed.

Corollary free_nested_program_diagonal_cofinal (i : I) :
  @operational_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i))
    (fun outer inner => free_nested_execution_grid outer inner i).
Proof.
  apply free_nested_productivity_diagonal_cofinal.
  apply free_nested_productivity.
Qed.

Lemma free_nested_execution_grid_row_lub
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out) :
  forall outer i,
    @sem_lub MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface _
      (fun inner => free_nested_execution_grid outer inner i)
      (free_nested_row_out sample_out outer i).
Proof.
  induction outer as [|outer IH]; intro i.
  - cbn [free_nested_execution_grid free_nested_row_out].
    apply sem_lub_constant.
  - cbn [free_nested_execution_grid free_nested_row_out].
    change (@sem_lub MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface _
      (fun inner => @sem_bind MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ (operational_hitting_approx (MF := MF) inner (observe sample))
        (fun h => match round i (free_no_event_head_value h) with
          | inl i' => free_nested_execution_grid outer inner i'
          | inr r => FORet (FHRet r)
          end))
      (@sem_bind MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ sample_out
        (fun h => match round i (free_no_event_head_value h) with
          | inl i' => free_nested_row_out sample_out outer i'
          | inr r => FORet (FHRet r)
          end))).
    eapply sem_bind_diagonal_lub.
    + apply (operational_hitting_increasing
        (FI := FreeOmegaObservableSemanticMeasureInterface)
        (MX := FreeOmegaMixedMeasureInterface)
        (FO := FreeOmegaObservableSemanticOmegaInterface)).
    + intro h. destruct (round i (free_no_event_head_value h)) as [i'|r].
      * intro inner. apply free_nested_execution_grid_inner_increasing.
      * intro inner. apply free_omega_approx_refl. intros x. reflexivity.
    + exact Hsample.
    + intro h. destruct (round i (free_no_event_head_value h)) as [i'|r].
      * apply IH.
      * apply sem_lub_constant.
Qed.

Theorem free_nested_execution_grid_diagonal_lub
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun fuel => free_nested_execution_grid fuel fuel i) out.
Proof.
  intro Houter.
  refine (@sem_lub_double_diagonal MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface
    FreeOmegaObservableSemanticOmegaFubiniLaws (frontier_head E MN R)
    (fun outer inner => free_nested_execution_grid outer inner i)
    (fun outer => free_nested_row_out sample_out outer i) out _ _ _ _).
  - intros outer inner. apply free_nested_execution_grid_inner_increasing.
  - intros inner outer. apply free_nested_execution_grid_outer_increasing.
  - intro outer. apply free_nested_execution_grid_row_lub. exact Hsample.
  - exact Houter.
Qed.

Theorem free_operational_weak_of_nested_no_event_grid
    (program : ptree E MN R)
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  @operational_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R (observe program)
    (fun outer inner => free_nested_execution_grid outer inner i) ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe program) out.
Proof.
  intros Hdiagonal Houter.
  eapply operational_weak_of_nested_grid
    with (row_out := fun outer => free_nested_row_out sample_out outer i).
  - exact Hdiagonal.
  - intros outer inner. apply free_nested_execution_grid_inner_increasing.
  - intros inner outer. apply free_nested_execution_grid_outer_increasing.
  - intro outer. apply free_nested_execution_grid_row_lub. exact Hsample.
  - exact Houter.
Qed.

(** User-facing form for the canonical nested program: the example supplies
    only finite productivity schedules and the outer probabilistic limit. *)
Corollary free_operational_weak_of_nested_productivity
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  free_nested_productivity_certificate i ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i)) out.
Proof.
  intros Hproductivity Houter.
  eapply free_operational_weak_of_nested_no_event_grid.
  - exact Hsample.
  - exact (free_nested_productivity_diagonal_cofinal Hproductivity).
  - exact Houter.
Qed.

Corollary free_operational_ast_weak_of_nested_productivity
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  free_nested_productivity_certificate i ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _ out ->
  @operational_ast_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i)) out.
Proof.
  intros Hproductivity Houter Htotal. split; [|exact Htotal].
  eapply free_operational_weak_of_nested_productivity; eassumption.
Qed.

Corollary free_operational_weak_of_canonical_nested
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i)) out.
Proof.
  intro Houter. eapply free_operational_weak_of_nested_productivity.
  - exact Hsample.
  - apply free_nested_productivity.
  - exact Houter.
Qed.

Corollary free_operational_ast_weak_of_canonical_nested
    (sample_out : MF (frontier_head E MN A))
    (Hsample : @operational_weak E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe sample) sample_out)
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun outer => free_nested_row_out sample_out outer i) out ->
  @sem_total MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _ out ->
  @operational_ast_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (free_nested_program i)) out.
Proof.
  intros Houter Htotal. split; [|exact Htotal].
  eapply free_operational_weak_of_canonical_nested; eassumption.
Qed.

End NestedNoEventGrid.

Lemma free_operational_bind_vis_approx_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal (Vis e c) k.
Proof.
  split; intro n; exists n;
    unfold free_operational_bind_approx_cofinal,
      operational_bind_diagonal_approx,
      operational_head_bind_approx,
      operational_hitting_approx, operational_kernel;
    cbn.
  all: rewrite !stable_target_stableE; cbn.
  all: apply free_omega_approx_refl; intros x; reflexivity.
Qed.

Corollary free_operational_bind_vis_cofinal {A R X}
    (e : E X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Vis e c) k.
Proof.
  apply free_operational_bind_cofinal.
  apply free_operational_bind_vis_approx_cofinal.
Qed.

Lemma free_operational_bind_tau_diagonal_left {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF) n t k)
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) n k))
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply free_omega_approx_refl. intros x. reflexivity.
  - intros h1 h2 ->. destruct h2 as [a|X e c];
      cbn [operational_head_bind_approx].
    + apply free_operational_hitting_mono.
      apply le_S. apply le_n.
    + apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_operational_bind_tau_diagonal_right {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) n :
  free_omega_approx eq
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) (Tau t) k)
    (operational_bind_diagonal_approx (MF := MF)
      (Datatypes.S n) t k).
Proof.
  change (free_omega_approx eq
    (free_omega_bind
      (operational_hitting_approx (MF := MF) n (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))
    (free_omega_bind
      (operational_hitting_approx (MF := MF) (Datatypes.S n) (observe t))
      (operational_head_bind_approx (MF := MF) (Datatypes.S n) k))).
  eapply free_omega_approx_bind with (R := eq) (T := eq).
  - apply free_operational_hitting_mono.
    apply le_S. apply le_n.
  - intros h1 h2 ->. apply free_omega_approx_refl.
    intros x. reflexivity.
Qed.

Lemma free_operational_bind_tau_approx_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  free_operational_bind_approx_cofinal (Tau t) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m Hm]. exists (Datatypes.S m).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply free_omega_approx_trans; [exact Hm|].
      apply free_operational_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m)) as [n Hn].
      exists (Datatypes.S n).
      change (free_omega_approx (fun y x => x = y)
        (operational_bind_diagonal_approx (MF := MF)
          (Datatypes.S m) (Tau t) k)
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind t k)))).
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply free_omega_approx_trans.
        -- apply free_operational_bind_tau_diagonal_right.
        -- eapply free_omega_approx_mono; [|exact Hn].
           intros x y Hyx. symmetry. exact Hyx.
Qed.

Corollary free_operational_bind_tau_cofinal {A R}
    (t : ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_approx_cofinal t k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Tau t) k.
Proof.
  intro Hcofinal. apply free_operational_bind_cofinal.
  exact (free_operational_bind_tau_approx_cofinal Hcofinal).
Qed.

(** Prob requires a genuinely stronger productivity condition than pointwise
    branch cofinality: each outer approximant needs one fuel bound that works
    almost everywhere for the sampled branches.  Finite Enum support can
    obtain such a bound by taking a maximum; arbitrary measures must provide
    it analytically. *)
Definition free_operational_bind_prob_uniform {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) : Prop :=
  (forall n, exists m Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))
        (operational_bind_diagonal_approx (MF := MF) m (c x) k)) /\
  (forall m, exists n Good,
      sem_ae mu Good /\
      forall x, Good x -> free_omega_approx eq
        (operational_bind_diagonal_approx (MF := MF) m (c x) k)
        (operational_hitting_approx (MF := MF) n
          (observe (PTree.bind (c x) k)))).

Lemma free_operational_bind_prob_approx_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_prob_uniform mu c k ->
  free_operational_bind_approx_cofinal (Prob mu c) k.
Proof.
  intros [Hglobal Hdiagonal]. split.
  - intros [|n].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hglobal n) as [m [Good [Hae Hbranches]]].
      exists (Datatypes.S m).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply FOApproxSample with
        (S := fun x y => x = y /\ Good x).
      * apply sem_lift_refl_ae. exact Hae.
      * intros x y [-> Hgood].
        eapply free_omega_approx_trans.
        -- exact (Hbranches y Hgood).
        -- apply free_operational_bind_tau_diagonal_left.
  - intros [|m].
    + exists 0. unfold operational_bind_diagonal_approx,
        operational_hitting_approx, operational_kernel. cbn.
      apply free_omega_approx_refl. intros x. reflexivity.
    + destruct (Hdiagonal (Datatypes.S m))
        as [n [Good [Hae Hbranches]]].
      exists (Datatypes.S n).
      rewrite observe_bind. cbn [operational_hitting_approx operational_kernel].
      eapply free_omega_approx_mono with (R := eq).
      * intros x y Hxy. symmetry. exact Hxy.
      * eapply FOApproxSample with
          (S := fun x y => x = y /\ Good x).
        -- apply sem_lift_refl_ae. exact Hae.
        -- intros x y [-> Hgood].
           eapply free_omega_approx_trans.
           ++ apply free_operational_bind_tau_diagonal_right.
           ++ exact (Hbranches y Hgood).
Qed.

Corollary free_operational_bind_prob_cofinal {A R X}
    (mu : MN X) (c : X -> ptree E MN A) (k : A -> ptree E MN R) :
  free_operational_bind_prob_uniform mu c k ->
  @operational_bind_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A R (Prob mu c) k.
Proof.
  intro Huniform. apply free_operational_bind_cofinal.
  exact (free_operational_bind_prob_approx_cofinal Huniform).
Qed.

(** A two-dimensional operational model for an iterator whose individual
    state-indexed steps may themselves have unbounded running time.  The
    first coordinate bounds completed iterator rounds; the second bounds
    primitive execution inside every step.  Unlike [free_nested_program],
    this construction consumes the client's actual [step] directly, so no
    bind reassociation or [pstructural] normalization is involved. *)
Section DirectUnboundedIteration.
Context {I R : Type}.
Context `{NCAEIter : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIter : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step : I -> ptree E MN (I + R).

Definition free_iter_after (next : I + R) : ptree E MN R :=
  match next with
  | inl j => Tau (PTree.iter step j)
  | inr r => Ret r
  end.

Lemma free_iter_program_observe i :
  observe (PTree.iter step i) =
  observe (PTree.bind (step i) free_iter_after).
Proof.
  pose proof (unfold_aloop_ step i) as Hunfold.
  rewrite (observing_observe Hunfold), observe_bind. reflexivity.
Qed.

Definition free_iter_head_next
    (h : frontier_head E MN (I + R)) : I + R :=
  match h with
  | FHRet next => next
  | @FHVis _ _ _ X e k => False_rect _ (no_event e)
  end.

Definition free_iter_result_value
    (h : frontier_head E MN R) : R :=
  match h with
  | FHRet r => r
  | @FHVis _ _ _ X e k => False_rect _ (no_event e)
  end.

Fixpoint free_iter_execution_grid (rounds inner : nat) (i : I) :
    MF (frontier_head E MN R) :=
  match rounds with
  | O => FOZero
  | S rounds' =>
      free_omega_bind
        (operational_hitting_approx (MF := MF) inner (observe (step i)))
        (fun h =>
          match free_iter_head_next h with
          | inl j => free_iter_execution_grid rounds' inner j
          | inr r => FORet (FHRet r)
          end)
  end.

Lemma free_iter_head_ret (h : frontier_head E MN (I + R)) :
  exists next, h = FHRet next.
Proof.
  destruct h as [next|X e k].
  - exists next. reflexivity.
  - exfalso. exact (no_event e).
Qed.

Lemma free_iter_execution_grid_inner_increasing rounds :
  forall inner i,
    free_omega_approx eq
      (free_iter_execution_grid rounds inner i)
      (free_iter_execution_grid rounds (S inner) i).
Proof.
  induction rounds as [|rounds IH]; intros inner i.
  - constructor.
  - cbn [free_iter_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_operational_hitting_mono. apply le_S, le_n.
    + intros h1 h2 ->.
      destruct (free_iter_head_next h2) as [j|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_iter_execution_grid_outer_increasing inner :
  forall rounds i,
    free_omega_approx eq
      (free_iter_execution_grid rounds inner i)
      (free_iter_execution_grid (S rounds) inner i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - constructor.
  - cbn [free_iter_execution_grid].
    eapply free_omega_approx_bind with (R := eq) (T := eq).
    + apply free_omega_approx_refl. intros h. reflexivity.
    + intros h1 h2 ->.
      destruct (free_iter_head_next h2) as [j|r].
      * apply IH.
      * apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_iter_operational_to_grid_sound fuel : forall i,
  free_omega_approx eq
    (operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (free_iter_execution_grid (S fuel) fuel i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - rewrite free_iter_program_observe.
    eapply free_omega_approx_trans.
    + apply free_operational_bind_hitting_le_diagonal.
    + unfold operational_bind_diagonal_approx.
      cbn [free_iter_execution_grid].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (free_iter_head_ret h2) as [next ->].
        cbn [operational_head_bind_approx free_iter_head_next].
        destruct next as [j|r].
        -- cbn [operational_hitting_approx operational_kernel]. constructor.
        -- cbn [operational_hitting_approx operational_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
  - rewrite free_iter_program_observe.
    eapply free_omega_approx_trans.
    + apply free_operational_bind_hitting_le_diagonal.
    + unfold operational_bind_diagonal_approx.
      cbn [free_iter_execution_grid].
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (free_iter_head_ret h2) as [next ->].
        cbn [operational_head_bind_approx free_iter_head_next].
        destruct next as [j|r].
        -- cbn [operational_hitting_approx operational_kernel].
           eapply free_omega_approx_trans.
           ++ apply IH.
           ++ apply free_omega_approx_monotone_nat with
                (chain := fun inner =>
                  free_iter_execution_grid (S fuel) inner j).
              ** intro inner.
                 apply free_iter_execution_grid_inner_increasing.
              ** apply le_S, le_n.
        -- cbn [operational_hitting_approx operational_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Fixpoint free_iter_grid_operational_fuel
    (rounds inner : nat) : nat :=
  match rounds with
  | O => O
  | S rounds' => inner + S (free_iter_grid_operational_fuel rounds' inner)
  end.

Lemma free_iter_grid_to_operational_sound rounds : forall inner i,
  free_omega_approx eq
    (free_iter_execution_grid rounds inner i)
    (operational_hitting_approx (MF := MF)
      (free_iter_grid_operational_fuel rounds inner)
      (observe (PTree.iter step i))).
Proof.
  induction rounds as [|rounds IH]; intros inner i.
  - constructor.
  - cbn [free_iter_execution_grid free_iter_grid_operational_fuel].
    rewrite free_iter_program_observe.
    eapply free_omega_approx_trans with
      (nu := free_operational_bind_split_approx inner
        (S (free_iter_grid_operational_fuel rounds inner))
        (step i) free_iter_after).
    + unfold free_operational_bind_split_approx.
      eapply free_omega_approx_bind with (R := eq) (T := eq).
      * apply free_omega_approx_refl. intros h. reflexivity.
      * intros h1 h2 ->.
        destruct (free_iter_head_ret h2) as [next ->].
        cbn [free_iter_head_next operational_head_bind_approx].
        destruct next as [j|r].
        -- cbn [operational_hitting_approx operational_kernel]. apply IH.
        -- cbn [operational_hitting_approx operational_kernel].
           try rewrite stable_target_stableE.
           apply free_omega_approx_refl. intros x. reflexivity.
    + apply free_operational_bind_split_le_hitting.
Qed.

Record free_iter_diagonal_productivity_certificate (i : I) := {
  iter_operational_to_grid : forall fuel,
    free_omega_approx eq
      (operational_hitting_approx (MF := MF) fuel
        (observe (PTree.iter step i)))
      (free_iter_execution_grid (S fuel) fuel i);
  iter_grid_to_operational : forall rounds inner,
    free_omega_approx eq
      (free_iter_execution_grid rounds inner i)
      (operational_hitting_approx (MF := MF)
        (free_iter_grid_operational_fuel rounds inner)
        (observe (PTree.iter step i)))
}.

Theorem free_iter_diagonal_productivity i :
  free_iter_diagonal_productivity_certificate i.
Proof.
  constructor.
  - intro fuel. exact (free_iter_operational_to_grid_sound fuel i).
  - intros rounds inner.
    exact (free_iter_grid_to_operational_sound rounds inner i).
Qed.

Theorem free_iter_grid_diagonal_cofinal i :
  @operational_hitting_diagonal_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (PTree.iter step i))
    (fun rounds inner => free_iter_execution_grid rounds inner i).
Proof.
  intro out. apply free_omega_cofinal_lub_iff. split.
  - intro fuel. exists (S fuel).
    eapply free_omega_approx_trans.
    + apply free_iter_operational_to_grid_sound.
    + apply free_omega_approx_monotone_nat with
        (chain := fun inner => free_iter_execution_grid (S fuel) inner i).
      * intro inner. apply free_iter_execution_grid_inner_increasing.
      * apply le_S, le_n.
  - intro diagonal.
    exists (free_iter_grid_operational_fuel diagonal diagonal).
    eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + apply free_iter_grid_to_operational_sound.
Qed.

Variable step_out : I -> MF (frontier_head E MN (I + R)).

Fixpoint free_iter_complete_rows (rounds : nat) (i : I) :
    MF (frontier_head E MN R) :=
  match rounds with
  | O => FOZero
  | S rounds' =>
      free_omega_bind (step_out i) (fun h =>
        match free_iter_head_next h with
        | inl j => free_iter_complete_rows rounds' j
        | inr r => FORet (FHRet r)
        end)
  end.

Lemma free_iter_execution_grid_row_lub
    (Hstep : forall i,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I + R)
        (observe (step i)) (step_out i)) :
  forall rounds i,
    @sem_lub MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface _
      (fun inner => free_iter_execution_grid rounds inner i)
      (free_iter_complete_rows rounds i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - cbn [free_iter_execution_grid free_iter_complete_rows].
    apply sem_lub_constant.
  - cbn [free_iter_execution_grid free_iter_complete_rows].
    change (@sem_lub MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface _
      (fun inner => @sem_bind MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ (operational_hitting_approx (MF := MF) inner (observe (step i)))
        (fun h => match free_iter_head_next h with
          | inl j => free_iter_execution_grid rounds inner j
          | inr r => FORet (FHRet r)
          end))
      (@sem_bind MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        _ _ (step_out i)
        (fun h => match free_iter_head_next h with
          | inl j => free_iter_complete_rows rounds j
          | inr r => FORet (FHRet r)
          end))).
    eapply sem_bind_diagonal_lub.
    + apply (operational_hitting_increasing
        (FI := FreeOmegaObservableSemanticMeasureInterface)
        (MX := FreeOmegaMixedMeasureInterface)
        (FO := FreeOmegaObservableSemanticOmegaInterface)).
    + intro h. destruct (free_iter_head_next h) as [j|r].
      * intro inner. apply free_iter_execution_grid_inner_increasing.
      * intro inner. apply free_omega_approx_refl. intros x. reflexivity.
    + apply Hstep.
    + intro h. destruct (free_iter_head_next h) as [j|r].
      * apply IH.
      * apply sem_lub_constant.
Qed.

Theorem free_iter_execution_grid_diagonal_lub
    (Hstep : forall i,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I + R)
        (observe (step i)) (step_out i))
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun rounds => free_iter_complete_rows rounds i) out ->
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun fuel => free_iter_execution_grid fuel fuel i) out.
Proof.
  intro Hrows.
  refine (@sem_lub_double_diagonal MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface
    FreeOmegaObservableSemanticOmegaFubiniLaws (frontier_head E MN R)
    (fun rounds inner => free_iter_execution_grid rounds inner i)
    (fun rounds => free_iter_complete_rows rounds i) out _ _ _ _).
  - intros rounds inner. apply free_iter_execution_grid_inner_increasing.
  - intros inner rounds. apply free_iter_execution_grid_outer_increasing.
  - intro rounds. apply free_iter_execution_grid_row_lub. exact Hstep.
  - exact Hrows.
Qed.

Theorem free_operational_weak_iter_of_unbounded_steps
    (Hstep : forall i,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I + R)
        (observe (step i)) (step_out i))
    (i : I) out :
  @sem_lub MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmegaInterface _
    (fun rounds => free_iter_complete_rows rounds i) out ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R
    (observe (PTree.iter step i)) out.
Proof.
  intro Hrounds. unfold operational_weak.
  apply (proj2 (free_iter_grid_diagonal_cofinal i out)).
  apply free_iter_execution_grid_diagonal_lub; assumption.
Qed.

Section DirectUnboundedIterationDenotation.
Context `{DB : @FreeOmegaDenotationBindLaws MN NI NO}.
Variable transition : I -> MN (I + R).

Fixpoint free_iter_measure_rows (rounds : nat) (i : I) : MN R :=
  match rounds with
  | O => sem_zero
  | S rounds' => sem_bind (transition i) (fun next =>
      match next with
      | inl j => free_iter_measure_rows rounds' j
      | inr r => sem_ret r
      end)
  end.

Lemma free_iter_complete_rows_denotes
    (Hstep : forall i,
      free_omega_denotes free_iter_head_next (step_out i) (transition i)) :
  forall rounds i,
      free_omega_denotes free_iter_result_value
      (free_iter_complete_rows rounds i)
      (free_iter_measure_rows rounds i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - apply free_omega_observes_denotes. constructor.
  - cbn [free_iter_complete_rows free_iter_measure_rows].
    eapply free_omega_denotes_bind.
    + apply Hstep.
    + intro h. destruct (free_iter_head_ret h) as [next ->].
      cbn [free_iter_head_next]. destruct next as [j|r].
      * apply IH.
      * apply free_omega_observes_denotes. constructor.
Qed.

End DirectUnboundedIterationDenotation.

Section DirectUnboundedIterationLimitDenotation.
Context `{DO : @FreeOmegaDenotationOmegaLaws MN NI NO}.
Variable transition : I -> MN (I + R).

Lemma free_iter_complete_limit_denotes
    (Hrows : forall rounds i,
      free_omega_denotes free_iter_result_value
        (free_iter_complete_rows rounds i)
        (free_iter_measure_rows transition rounds i))
    (i : I) out :
  sem_lub (fun rounds => free_iter_measure_rows transition rounds i) out ->
  free_omega_denotes free_iter_result_value
    (FOLub (fun rounds => free_iter_complete_rows rounds i)) out.
Proof.
  intro Hlub. eapply free_omega_denotes_lub.
  - intro rounds. apply Hrows.
  - exact Hlub.
Qed.

End DirectUnboundedIterationLimitDenotation.

End DirectUnboundedIteration.

Section EventlessBehavioralIterationFusion.
Context {I1 I2 R1 R2 : Type}.
Context `{NCAEIterFusion : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIterFusion : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

Definition free_iter_behavioral_sum_rel
    (x1 : I1 + R1) (x2 : I2 + R2) : Prop :=
  match x1, x2 with
  | inl i1, inl i2 => SI i1 i2
  | inr r1, inr r2 => RR r1 r2
  | _, _ => False
  end.

Variable step_out1 : I1 -> MF (frontier_head E MN (I1 + R1)).
Variable step_out2 : I2 -> MF (frontier_head E MN (I2 + R2)).
Hypothesis Hstep_out1 : forall i1,
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (I1 + R1)
    (observe (step1 i1)) (step_out1 i1).
Hypothesis Hstep_out2 : forall i2,
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface (I2 + R2)
    (observe (step2 i2)) (step_out2 i2).
Hypothesis Hstep_lift : forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      free_iter_behavioral_sum_rel
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2) free_iter_behavioral_sum_rel))
    (step_out1 i1) (step_out2 i2).

Lemma free_iter_complete_rows_behavioral_lift rounds :
  forall i1 i2, SI i1 i2 ->
  free_omega_qlift
    (@ptree_stable_head_rel E MN R1 R2 RR
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface R1 R2 RR))
    (free_iter_complete_rows no_event step_out1 rounds i1)
    (free_iter_complete_rows no_event step_out2 rounds i2).
Proof.
  induction rounds as [|rounds IH]; intros i1 i2 Hij.
  - constructor. constructor.
  - cbn [free_iter_complete_rows].
    eapply FOQLBind; [exact (Hstep_lift Hij)|].
    intros h1 h2 Hhead. dependent destruction Hhead.
    + destruct r1 as [j1|v1], r2 as [j2|v2];
        cbn [free_iter_head_next] in H |- *.
      * apply IH. exact H.
      * contradiction.
      * contradiction.
      * constructor. constructor. constructor. exact H.
    + exfalso. exact (no_event e).
Qed.

Theorem free_probabilistic_eutt_iter_behavioral_rel_of_outputs
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  let rows1 := constr:(fun rounds =>
    free_iter_complete_rows no_event step_out1 rounds i1) in
  let rows2 := constr:(fun rounds =>
    free_iter_complete_rows no_event step_out2 rounds i2) in
  eapply probabilistic_eutt_of_hitting_lift
    with (out1 := FOLub rows1) (out2 := FOLub rows2).
  - eapply free_operational_weak_iter_of_unbounded_steps
      with (step_out := step_out1).
    + exact Hstep_out1.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - eapply free_operational_weak_iter_of_unbounded_steps
      with (step_out := step_out2).
    + exact Hstep_out2.
    + apply free_omega_qlift_refl. intro h. reflexivity.
  - apply FOQLLub. intro rounds.
    apply free_iter_complete_rows_behavioral_lift. exact Hij.
Qed.

End EventlessBehavioralIterationFusion.

Section EventlessBehavioralIterationCongruence.
Context {I1 I2 R1 R2 : Type}.
Context `{NCAEIterCong : @SemanticMeasureCouplingAELaws MN NI}.
Context `{NCountAEIterCong : @SemanticMeasureCountableAELaws MN NI}.
Variable no_event : forall X, E X -> False.
Variable step1 : I1 -> ptree E MN (I1 + R1).
Variable step2 : I2 -> ptree E MN (I2 + R2).
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.

(** Heterogeneous behavioral fusion for eventless unbounded loops.  Step
    programs need only be related by the canonical equivalence; their finite
    schedules and syntax may be unrelated.  Complete step witnesses are
    chosen extensionally, coupled by step equivalence, iterated by the
    complete-row construction, and finally lifted through the double omega
    limit. *)
Theorem free_probabilistic_eutt_iter_behavioral_rel
    (Hstep : forall i1 i2, SI i1 i2 ->
      @probabilistic_eutt E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2)
        (free_iter_behavioral_sum_rel SI RR)
        (step1 i1) (step2 i2))
    i1 i2 :
  SI i1 i2 ->
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R1 R2 RR
    (PTree.iter step1 i1) (PTree.iter step2 i2).
Proof.
  intro Hij.
  assert (Hexists1 : forall j1, exists out,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I1 + R1)
        (observe (step1 j1)) out).
  { intro j1. apply stable_hitting_weak_exists. }
  assert (Hexists2 : forall j2, exists out,
      @operational_weak E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface (I2 + R2)
        (observe (step2 j2)) out).
  { intro j2. apply stable_hitting_weak_exists. }
  destruct (choice _ Hexists1) as [out1 Hout1].
  destruct (choice _ Hexists2) as [out2 Hout2].
  eapply free_probabilistic_eutt_iter_behavioral_rel_of_outputs
    with (step_out1 := out1) (step_out2 := out2)
         (SI := SI) (RR := RR); try eassumption.
  intros j1 j2 Hrel.
  change (@sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _
    (@ptree_stable_head_rel E MN (I1 + R1) (I2 + R2)
      (free_iter_behavioral_sum_rel SI RR)
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface
        (I1 + R1) (I2 + R2) (free_iter_behavioral_sum_rel SI RR)))
    (out1 j1) (out2 j2)).
  eapply probabilistic_eutt_hitting_lift;
    [exact (Hstep j1 j2 Hrel)|exact (Hout1 j1)|exact (Hout2 j2)].
Qed.

End EventlessBehavioralIterationCongruence.

(** The analogous finite obligation for iteration rounds.  This is where
    bounded cost/productivity proofs for concrete samplers belong. *)
Definition free_operational_iter_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) : Prop :=
  free_omega_chains_cofinal eq
    (fun fuel => operational_hitting_approx (MF := MF) fuel
      (observe (PTree.iter step i)))
    (fun rounds => operational_iter_round_approx (MF := MF)
      rounds transition i).

(** Finite, proof-relevant productivity data for bounded-cost iterations.
    A certificate does more than
    assert equality of two omega limits: it exhibits how much structured
    round fuel is sufficient for each operational fuel, and conversely.
    This is deliberately only a sufficient condition.  A genuinely
    unbounded nested sampler generally cannot provide the reverse finite
    schedule: no finite inner fuel contains its complete AST output measure.
    Such programs require diagonal/Fubini continuity of the two omega
    limits, rather than a maximum finite fuel. *)
Record free_operational_iter_productivity_certificate {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) := {
  operational_to_round_schedule : nat -> nat;
  round_to_operational_schedule : nat -> nat;
  operational_to_round_sound : forall fuel,
    free_omega_approx eq
      (operational_hitting_approx (MF := MF) fuel
        (observe (PTree.iter step i)))
      (operational_iter_round_approx (MF := MF)
        (operational_to_round_schedule fuel) transition i);
  round_to_operational_sound : forall rounds,
    free_omega_approx (fun y x => x = y)
      (operational_iter_round_approx (MF := MF) rounds transition i)
      (operational_hitting_approx (MF := MF)
        (round_to_operational_schedule rounds)
        (observe (PTree.iter step i)))
}.

Lemma free_operational_iter_certificate_approx_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_productivity_certificate step transition i ->
  free_operational_iter_approx_cofinal step transition i.
Proof.
  intros cert. split.
  - intro fuel. exists (operational_to_round_schedule cert fuel).
    exact (operational_to_round_sound cert fuel).
  - intro rounds. exists (round_to_operational_schedule cert rounds).
    exact (round_to_operational_sound cert rounds).
Qed.

Corollary free_operational_iter_certificate_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_productivity_certificate step transition i ->
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R step transition i.
Proof.
  intros cert out. unfold operational_iter_cofinal.
  apply free_omega_cofinal_lub_iff.
  exact (free_operational_iter_certificate_approx_cofinal cert).
Qed.

(** A primitive Markov step has a uniform syntactic cost: one probabilistic
    node followed by the silent back-edge inserted by [PTree.iter].  Hence
    its global stable-hitting chain and its absorbing-round chain are
    cofinal.  This theorem is entirely operational; no frontier derivation
    or iteration constructor occurs in its assumptions. *)
Section PrimitiveProbIteration.
Context {I R : Type} (transition : I -> MN (I + R)).

Definition free_primitive_iter_step (i : I) : ptree E MN (I + R) :=
  Prob (transition i) (fun next => Ret next).

Definition free_primitive_iter_program (i : I) : ptree E MN R :=
  PTree.iter free_primitive_iter_step i.

Definition free_primitive_iter_hitting (fuel : nat) (i : I) :
    MF (frontier_head E MN R) :=
  operational_hitting_approx (MF := MF) fuel
    (observe (free_primitive_iter_program i)).

Definition free_primitive_iter_rounds (rounds : nat) (i : I) :
    MF (frontier_head E MN R) :=
  operational_iter_round_approx (MF := MF) rounds transition i.

Definition free_primitive_iter_after (next : I + R) : ptree E MN R :=
  match next with
  | inl j => Tau (free_primitive_iter_program j)
  | inr r => Ret r
  end.

Definition free_primitive_iter_cont (next : I + R) : ptree E MN R :=
  PTree.bind (Ret next) (fun lr =>
    match lr with
    | inl j => Tau (free_primitive_iter_program j)
    | inr r => Ret r
    end).

Lemma free_primitive_iter_observe i :
  observe (free_primitive_iter_program i) =
  ProbF (transition i) free_primitive_iter_cont.
Proof.
  unfold free_primitive_iter_program.
  pose proof (unfold_aloop_ free_primitive_iter_step i) as Hunfold.
  rewrite (observing_observe Hunfold), observe_bind.
  assert (Hstep : observe (free_primitive_iter_step i) =
    ProbF (transition i) (fun next => Ret next)) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma free_primitive_iter_cont_observe next :
  observe (free_primitive_iter_cont next) =
  observe (free_primitive_iter_after next).
Proof.
  unfold free_primitive_iter_cont. rewrite observe_bind.
  destruct next as [j|r]; reflexivity.
Qed.

Lemma free_primitive_iter_rounds_zero i :
  free_primitive_iter_rounds 0 i = FOZero.
Proof. reflexivity. Qed.

Lemma free_primitive_iter_rounds_succ rounds i :
  free_primitive_iter_rounds (Datatypes.S rounds) i =
  FOSample (transition i) (fun next =>
    match next with
    | inl j => free_primitive_iter_rounds rounds j
    | inr r => FORet (FHRet r)
    end).
Proof.
  unfold free_primitive_iter_rounds, operational_iter_round_approx.
  cbv [mixed_iter_approx sem_bind mixed_bind sem_ret free_omega_bind
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaSemanticMeasureInterface].
  f_equal. apply functional_extensionality. intros [j|r]; reflexivity.
Qed.

Lemma free_primitive_iter_hitting_succ fuel i :
  free_primitive_iter_hitting (Datatypes.S fuel) i =
  FOSample (transition i) (fun next =>
    operational_hitting_approx (MF := MF) fuel
      (observe (free_primitive_iter_cont next))).
Proof.
  unfold free_primitive_iter_hitting. rewrite free_primitive_iter_observe.
  reflexivity.
Qed.

Lemma free_primitive_iter_retry_zero j :
  operational_hitting_approx (MF := MF) 0
    (observe (free_primitive_iter_cont (inl j))) = FOZero.
Proof. reflexivity. Qed.

Lemma free_primitive_iter_retry_succ fuel j :
  operational_hitting_approx (MF := MF) (Datatypes.S fuel)
    (observe (free_primitive_iter_cont (inl j))) =
  free_primitive_iter_hitting fuel j.
Proof.
  rewrite free_primitive_iter_cont_observe. reflexivity.
Qed.

Lemma free_primitive_iter_success fuel r :
  operational_hitting_approx (MF := MF) fuel
    (observe (free_primitive_iter_cont (inr r))) = FORet (FHRet r).
Proof.
  rewrite free_primitive_iter_cont_observe.
  unfold free_primitive_iter_after, operational_hitting_approx,
    operational_kernel. cbn. rewrite stable_target_stableE.
  reflexivity.
Qed.

Lemma free_primitive_iter_hitting_le_round fuel :
  forall i, free_omega_approx eq
    (free_primitive_iter_hitting fuel i)
    (free_primitive_iter_rounds (Datatypes.S fuel) i).
Proof.
  induction fuel as [|fuel IH]; intro i.
  - rewrite free_primitive_iter_rounds_succ.
    unfold free_primitive_iter_hitting. rewrite free_primitive_iter_observe.
    unfold operational_hitting_approx, operational_kernel. cbn.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r]; constructor.
  - rewrite free_primitive_iter_hitting_succ,
      free_primitive_iter_rounds_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * eapply free_omega_approx_trans with
          (nu := free_primitive_iter_hitting fuel j).
        -- destruct fuel as [|fuel].
           ++ constructor.
           ++ rewrite free_primitive_iter_retry_succ.
              apply free_operational_hitting_mono.
              apply le_S. apply le_n.
        -- apply IH.
      * rewrite free_primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Lemma free_primitive_iter_round_le_hitting rounds :
  forall i, free_omega_approx eq
    (free_primitive_iter_rounds rounds i)
    (free_primitive_iter_hitting (2 * rounds) i).
Proof.
  induction rounds as [|rounds IH]; intro i.
  - rewrite free_primitive_iter_rounds_zero. constructor.
  - rewrite free_primitive_iter_rounds_succ.
    replace (2 * Datatypes.S rounds) with
      (Datatypes.S (Datatypes.S (2 * rounds))) by lia.
    rewrite free_primitive_iter_hitting_succ.
    eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intros x. reflexivity.
    + intros x y ->. destruct y as [j|r].
      * rewrite free_primitive_iter_retry_succ. apply IH.
      * rewrite free_primitive_iter_success.
        apply free_omega_approx_refl. intros x. reflexivity.
Qed.

Theorem free_primitive_iter_productivity i :
  free_operational_iter_productivity_certificate
    free_primitive_iter_step transition i.
Proof.
  refine {| operational_to_round_schedule := Datatypes.S;
    round_to_operational_schedule := fun rounds => 2 * rounds |}.
  - intro fuel. exact (free_primitive_iter_hitting_le_round fuel i).
  - intro rounds. eapply free_omega_approx_mono.
    + intros x y Hxy. symmetry. exact Hxy.
    + exact (free_primitive_iter_round_le_hitting rounds i).
Qed.

Corollary free_primitive_iter_approx_cofinal i :
  free_operational_iter_approx_cofinal
    free_primitive_iter_step transition i.
Proof.
  apply free_operational_iter_certificate_approx_cofinal.
  exact (free_primitive_iter_productivity i).
Qed.

Corollary free_primitive_iter_cofinal i :
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R
    free_primitive_iter_step transition i.
Proof.
  apply free_operational_iter_certificate_cofinal.
  exact (free_primitive_iter_productivity i).
Qed.

End PrimitiveProbIteration.

Theorem free_operational_iter_cofinal {I R}
    (step : I -> ptree E MN (I + R))
    (transition : I -> MN (I + R)) (i : I) :
  free_operational_iter_approx_cofinal step transition i ->
  @operational_iter_cofinal E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface I R step transition i.
Proof.
  intros Hcofinal out. unfold operational_iter_cofinal.
  apply free_omega_cofinal_lub_iff. exact Hcofinal.
Qed.

End FreeOmegaOperationalCofinalityContinuation.

(** Interpreting visible events preserves every structural proof.  This is
    stated outside the source-event section so structural soundness can be
    instantiated at the handler's target event signature. *)
Theorem free_probabilistic_eutt_interp_structural
    {E F : Type -> Type} {MN : Type -> Type}
    `{NI : SemanticMeasureInterface MN}
    `{NC : @SemanticMeasureCoreLaws MN NI}
    `{NAE : @SemanticMeasureAELiftLaws MN NI}
    `{NO : @SemanticOmegaInterface MN NI}
    {A B} (RR : A -> B -> Prop)
    (handler : forall X, E X -> ptree F MN X)
    (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstructural RR t1 t2 ->
  @probabilistic_eutt F MN (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR
    (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intro Hstruct. apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_interp. exact Hstruct.
Qed.

Section FreeOmegaInterpLaws.
Context {E F : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

(** Semantic interpreter preservation from stable-head kernels.  This is the
    non-circular composition boundary: source hitting is coupled once, each
    related source head supplies a coupled interpreted-head behavior, and
    [operational_weak_interp] plus FreeOmega bind lifting assemble the whole
    interpreted programs. *)
Theorem free_probabilistic_eutt_interp_of_head_lifts
    `{NCAEInterp : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAEInterp : @SemanticMeasureCountableAELaws MN NI}
    {A B} (RR : A -> B -> Prop)
    (handler : forall X, E X -> ptree F MN X)
    (t1 : ptree E MN A) (t2 : ptree E MN B)
    (source1 : MF (frontier_head E MN A))
    (source2 : MF (frontier_head E MN B))
    (front1 : frontier_head E MN A -> MF (frontier_head F MN A))
    (front2 : frontier_head E MN B -> MF (frontier_head F MN B)) :
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A (observe t1) source1 ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B (observe t2) source2 ->
  (forall h, @operational_weak F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A
    (observe (operational_interp_head_tree handler h)) (front1 h)) ->
  (forall h, @operational_weak F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B
    (observe (operational_interp_head_tree handler h)) (front2 h)) ->
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _
    (@ptree_stable_head_rel E MN A B RR
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface A B RR))
    source1 source2 ->
  (forall h1 h2,
    @ptree_stable_head_rel E MN A B RR
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface A B RR) h1 h2 ->
    @sem_lift MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      _ _
      (@ptree_stable_head_rel F MN A B RR
        (@probabilistic_eutt_state F MN MF
          (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasureInterface
          FreeOmegaObservableSemanticOmegaInterface A B RR))
      (front1 h1) (front2 h2)) ->
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR
    (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intros Hsource1 Hsource2 Hfront1 Hfront2 HsourceLift HfrontLift.
  assert (Htarget1 : @operational_weak F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A
      (observe (PTree.interp handler t1))
      (free_omega_bind source1 front1)).
  { eapply (operational_weak_interp
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (MX := FreeOmegaMixedMeasureInterface)).
    + apply free_operational_interp_cofinal_all.
    + exact Hsource1.
    + exact Hfront1. }
  assert (Htarget2 : @operational_weak F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface B
      (observe (PTree.interp handler t2))
      (free_omega_bind source2 front2)).
  { eapply (operational_weak_interp
      (FI := FreeOmegaObservableSemanticMeasureInterface)
      (FO := FreeOmegaObservableSemanticOmegaInterface)
      (MX := FreeOmegaMixedMeasureInterface)).
    + apply free_operational_interp_cofinal_all.
    + exact Hsource2.
    + exact Hfront2. }
  eapply probabilistic_eutt_of_hitting_lift
    with (out1 := free_omega_bind source1 front1)
         (out2 := free_omega_bind source2 front2).
  - exact Htarget1.
  - exact Htarget2.
  - eapply FOQLBind; [exact HsourceLift|]. exact HfrontLift.
  Unshelve. all: typeclasses eauto.
Qed.

(** Canonical unfolding laws for the guarded interpreter. *)
Theorem free_probabilistic_eutt_interp_ret {R}
    (handler : forall X, E X -> ptree F MN X) (r : R) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler (Ret r)) (Ret r).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural. exact (observing_observe (interp_ret_ handler r)).
Qed.

Theorem free_probabilistic_eutt_interp_tau {R}
    (handler : forall X, E X -> ptree F MN X) (t : ptree E MN R) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler (Tau t)) (Tau (PTree.interp handler t)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural. exact (observing_observe (interp_tau_ handler t)).
Qed.

Theorem free_probabilistic_eutt_interp_vis {R X}
    (handler : forall Y, E Y -> ptree F MN Y)
    (e : E X) (k : X -> ptree E MN R) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler (Vis e k))
    (Tau (PTree.bind (handler _ e)
      (fun x => PTree.interp handler (k x)))).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural. exact (observing_observe (interp_vis_ handler e k)).
Qed.

Theorem free_probabilistic_eutt_interp_prob {R X}
    (handler : forall Y, E Y -> ptree F MN Y)
    (mu : MN X) (k : X -> ptree E MN R) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler (Prob mu k))
    (Prob mu (fun x => PTree.interp handler (k x))).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural. exact (observing_observe (interp_prob_ handler mu k)).
Qed.

Theorem free_probabilistic_eutt_interp_bind {A B}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN A) (k : A -> ptree E MN B) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B B eq
    (PTree.interp handler (PTree.bind t k))
    (PTree.bind (PTree.interp handler t)
      (fun x => PTree.interp handler (k x))).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_interp_bind.
Qed.

(** A handler may itself perform unbounded probabilistic computation before
    returning the answer to an event.  Guarded interpretation nevertheless
    commutes with [iter]: the law follows from the joint structural
    coinduction in [pstructural_interp_iter], so it needs no productivity or
    bounded-fuel premise. *)
Theorem free_probabilistic_eutt_interp_iter {I R}
    (handler : forall X, E X -> ptree F MN X)
    (step : I -> ptree E MN (I + R)) (i : I) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler (PTree.iter step i))
    (PTree.iter (fun j => PTree.interp handler (step j)) i).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_interp_iter.
Qed.

(** Sequential effect handlers compose, even when either handler performs
    target-side probabilistic or visible computation. *)
Theorem free_probabilistic_eutt_interp_compose
    {G : Type -> Type} {R}
    (handler1 : forall X, E X -> ptree F MN X)
    (handler2 : forall X, F X -> ptree G MN X)
    (t : ptree E MN R) :
  @probabilistic_eutt G MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler2 (PTree.interp handler1 t))
    (PTree.interp
      (fun (X : Type) (e : E X) =>
        PTree.interp handler2 (@handler1 X e)) t).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_interp_compose.
Qed.

(** Pointwise structurally equivalent handlers are interchangeable under
    interpretation. *)
Theorem free_probabilistic_eutt_interp_handler {R}
    (handler1 handler2 : forall X, E X -> ptree F MN X)
    (Hhandler : forall X (e : E X),
      pstructural eq (@handler1 X e) (@handler2 X e))
    (t : ptree E MN R) :
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R R eq
    (PTree.interp handler1 t) (PTree.interp handler2 t).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_interp_handler. exact Hhandler.
Qed.

Theorem free_probabilistic_eutt_translate_structural {G A B}
    (RR : A -> B -> Prop) (rename : forall X, E X -> G X)
    (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstructural RR t1 t2 ->
  @probabilistic_eutt G MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR
    (PTree.translate rename t1) (PTree.translate rename t2).
Proof.
  apply free_probabilistic_eutt_interp_structural.
Qed.

End FreeOmegaInterpLaws.
