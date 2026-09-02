Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms Program.Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import
  Shallow UnifiedFrontier PrimitiveStableHitting OperationalProbabilisticPTS
  ProbabilisticEutt PStrong
  OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaTranslateIdentity.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).

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
  intros t1 t2 Ht. apply free_probabilistic_eutt_translate. exact Ht.
Qed.

End TranslateProper.

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
    unfold free_translate_cont. rewrite observe_bind. cbn. constructor.
Qed.

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

End FreeOmegaTranslateIdentity.

Section FreeOmegaTranslateComposition.
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

End FreeOmegaTranslateComposition.

(** Interpreting visible events preserves every structural proof. *)
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

(** Focused behavioral facts for effect interpretation over the maintained
    FreeOmega backend.  This module deliberately exposes the one remaining
    algebraic boundary: an effectful handler must close the native generator
    at handler-produced binds.  Operational scheduling and omega-limit
    composition have already been discharged by
    [free_operational_interp_cofinal_all]. *)
Section FreeOmegaInterpCoinduction.
Context {E F : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

(** Semantic interpreter preservation from stable-head kernels.  Source
    hitting is coupled once, related source heads supply coupled interpreted
    behavior, and operational composition assembles the whole programs. *)
Theorem free_probabilistic_eutt_interp_of_head_lifts
    `{NCAEInterp : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAEInterp : @SemanticMeasureCountableAELaws MN NI}
    {A0 B0} (RR0 : A0 -> B0 -> Prop)
    (handler0 : forall X, E X -> ptree F MN X)
    (t1 : ptree E MN A0) (t2 : ptree E MN B0)
    (source1 : MF (frontier_head E MN A0))
    (source2 : MF (frontier_head E MN B0))
    (front1 : frontier_head E MN A0 -> MF (frontier_head F MN A0))
    (front2 : frontier_head E MN B0 -> MF (frontier_head F MN B0)) :
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A0 (observe t1) source1 ->
  @operational_weak E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B0 (observe t2) source2 ->
  (forall h, @operational_weak F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A0
    (observe (operational_interp_head_tree handler0 h)) (front1 h)) ->
  (forall h, @operational_weak F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B0
    (observe (operational_interp_head_tree handler0 h)) (front2 h)) ->
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    _ _
    (@ptree_stable_head_rel E MN A0 B0 RR0
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface A0 B0 RR0))
    source1 source2 ->
  (forall h1 h2,
    @ptree_stable_head_rel E MN A0 B0 RR0
      (@probabilistic_eutt_state E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws
        FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface A0 B0 RR0) h1 h2 ->
    @sem_lift MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      _ _
      (@ptree_stable_head_rel F MN A0 B0 RR0
        (@probabilistic_eutt_state F MN MF
          (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasureInterface
          FreeOmegaObservableSemanticOmegaInterface A0 B0 RR0))
      (front1 h1) (front2 h2)) ->
  @probabilistic_eutt F MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A0 B0 RR0
    (PTree.interp handler0 t1) (PTree.interp handler0 t2).
Proof.
  intros Hsource1 Hsource2 Hfront1 Hfront2 HsourceLift HfrontLift.
  assert (Htarget1 : @operational_weak F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A0
      (observe (PTree.interp handler0 t1))
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
      FreeOmegaObservableSemanticOmegaInterface B0
      (observe (PTree.interp handler0 t2))
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
    (RR0 : A -> B -> Prop) (rename : forall X, E X -> G X)
    (t1 : ptree E MN A) (t2 : ptree E MN B) :
  pstructural RR0 t1 t2 ->
  @probabilistic_eutt G MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A B RR0
    (PTree.translate rename t1) (PTree.translate rename t2).
Proof.
  apply free_probabilistic_eutt_interp_structural.
Qed.

Context {A B : Type} (RR : A -> B -> Prop)
  (handler : forall X, E X -> ptree F MN X).

(** The smallest source-indexed candidate needed for full interpreter
    preservation.  It contains no syntax cases: a target-state pair belongs
    to the candidate exactly when it is obtained by interpreting a pair
    already related by the canonical source equivalence. *)
Definition free_interp_bisim_candidate
    (s1 : ptree' F MN A) (s2 : ptree' F MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe (PTree.interp handler t1) /\
    s2 = observe (PTree.interp handler t2) /\
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2.

(** Exact closure obligation for an arbitrary effectful handler.  Compared
    with the generic PTree coinduction rule, the candidate is fixed to
    interpreted source equivalence.  Consequently an implementation of this
    premise cannot hide a different behavioral relation or strengthen the
    theorem's conclusion. *)
Definition free_interp_generator_closed : Prop :=
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2 ->
    @stable_hitting_match MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface
      (ptree' F MN A) (ptree' F MN B)
      (frontier_head F MN A) (frontier_head F MN B)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface A)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface B)
      (@ptree_stable_head_rel F MN A B RR)
      free_interp_bisim_candidate
      (observe (PTree.interp handler t1))
      (observe (PTree.interp handler t2)).

(** Full behavioral preservation follows from precisely the candidate-level
    handler closure above.  The canonical generator is unchanged. *)
Theorem free_probabilistic_eutt_interp_of_generator_closed
    (Hclosed : free_interp_generator_closed) :
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2 ->
    @probabilistic_eutt F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR
      (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intros t1 t2 Hsource.
  eapply probabilistic_eutt_coinduction with
      (sim := free_interp_bisim_candidate).
  - intros s1 s2 [u1 [u2 [-> [-> Hu]]]]. exact (Hclosed u1 u2 Hu).
  - exists t1, t2. repeat split; try reflexivity. exact Hsource.
Qed.

End FreeOmegaInterpCoinduction.
