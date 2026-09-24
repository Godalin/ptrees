(** Two-handler complete-frontier fusion. This is the generic proof owner;
    the fixed-handler fusion criterion specializes both handlers to one.
    No equality of handlers or handler-preservation theorem is assumed. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt StableHittingRelation BindScheduling.
From PTree.Interp Require Import Kernel Scheduling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Preservation.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Local Lemma bind_cofinal_all {X A B} (t : ptree X MN A) (k : A -> ptree X MN B) :
  ptree_bind_cofinal (MF := MF) t k.
Proof.
  apply BindScheduling.ptree_bind_cofinal_all.
  - exact (@sem_bind_ret_order MF FI FO BindOrd).
  - exact (@sem_bind_zero_order MF FI FO BindOrd).
  - exact (@mixed_bind_assoc_order MN MF FI MX FO MixedOrd).
  - exact (@mixed_bind_le_k MN MF FI MX FO MixedOrd).
  - exact (@sem_lub_cofinal MF FI FO Directed).
Qed.

Context {A B : Type} (RR : A -> B -> Prop)
  (handler1 handler2 : forall X, E X -> ptree F MN X).

(** The smallest source-indexed candidate needed for full interpreter
    preservation.  It contains no syntax cases: a target-state pair belongs
    to the candidate exactly when it is obtained by interpreting a pair
    already related by the canonical source equivalence. *)
Definition interp_rel_candidate
    (s1 : ptree' F MN A) (s2 : ptree' F MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe (PTree.interp handler1 t1) /\
    s2 = observe (PTree.interp handler2 t2) /\
    @peutt E MN MF
      FI
      FC
      MX
      FO A B RR t1 t2.

(** The irreducible handled-[Vis] obligation.  When the handler returns
    internally, stable hitting crosses the handler bind and immediately
    enters the interpreted source continuation.  Ordinary residual-bind
    compatibility cannot guard that recursive use of [interp_rel_candidate].

    This property isolates exactly that collapsed segment; Ret heads and the
    outer source stable-hitting composition are derivable from existing laws. *)
Definition interp_rel_vis_fusion : Prop :=
  forall X (e : E X) (k1 : X -> ptree E MN A) (k2 : X -> ptree E MN B),
    (forall x,
      @peutt E MN MF
        FI
        FC
        MX
        FO A B RR (k1 x) (k2 x)) ->
    @stable_hitting_match MF
      FI
      FO
      (ptree' F MN A) (ptree' F MN B)
      (stable_head F MN A) (stable_head F MN B)
      (@ptree_primitive_kernel F MN MF
        FI
        MX A)
      (@ptree_primitive_kernel F MN MF
        FI
        MX B)
      (@ptree_stable_head_rel F MN A B RR)
      (@bind_upto_closure F MN MF
        FI
        FC
        MX
        FO
        A B RR interp_rel_candidate)
      (observe (ptree_interp_head_tree handler1 (FHVis e k1)))
      (observe (ptree_interp_head_tree handler2 (FHVis e k2))).

(** Full effectful interpreter preservation follows once the single
    collapsed handled-[Vis] fusion above is supplied.  This theorem
    discharges source hitting, Ret heads, outer interpreter scheduling, and
    coupling composition; no broader generator-closure premise remains. *)
Theorem peutt_interp_rel_of_vis_fusion
    (Hvis : interp_rel_vis_fusion) :
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @peutt E MN MF
      FI
      FC
      MX
      FO A B RR t1 t2 ->
    @peutt F MN MF
      FI
      FC
      MX
      FO A B RR
      (PTree.interp handler1 t1) (PTree.interp handler2 t2).
Proof.
  intros t1 t2 Hsource.
  eapply (peutt_coinduction_upto_bind
    (E := F) (MN := MN) (MF := MF)
    (fun A0 R0 (t : ptree F MN A0) (k : A0 -> ptree F MN R0) =>
      bind_cofinal_all t k)
    (A := A) (B := B) (RR0 := RR)
    (sim := interp_rel_candidate)).
  - intros s1 s2 Hsim.
    unfold interp_rel_candidate in Hsim.
    destruct Hsim as [u1 Hsim].
    destruct Hsim as [u2 Hsim].
    destruct Hsim as [Hs1 Hsim].
    destruct Hsim as [Hs2 Hu].
    rewrite Hs1, Hs2.
    destruct (stable_hitting_exists
      (FI := FI)
      (FO := FO)
      (@ptree_primitive_kernel E MN MF
        FI
        MX A) (observe u1))
      as [source1 Hsource1].
    destruct (stable_hitting_exists
      (FI := FI)
      (FO := FO)
      (@ptree_primitive_kernel E MN MF
        FI
        MX B) (observe u2))
      as [source2 Hsource2].
    destruct (stable_hitting_front_choice
      (FI := FI)
      (FO := FO)
      (fun h : stable_head E MN A =>
        ptree_interp_head_tree handler1 h))
      as [front1 Hfront1].
    destruct (stable_hitting_front_choice
      (FI := FI)
      (FO := FO)
      (fun h : stable_head E MN B =>
        ptree_interp_head_tree handler2 h))
      as [front2 Hfront2].
    assert (HsourceLift :
      @sem_lift MF
        FI
        _ _
        (@ptree_stable_head_rel E MN A B RR
          (@peutt_state E MN MF
            FI
            FC
            MX
            FO A B RR))
        source1 source2).
    { eapply peutt_state_hitting_lift;
        [exact Hu|exact Hsource1|exact Hsource2]. }
    assert (Htarget1 : @ptree_stable_hitting F MN MF
      FI
      MX
      FO A
      (observe (PTree.interp handler1 u1))
      (sem_bind source1 front1)).
    { eapply (ptree_stable_hitting_interp
        (FI := FI)
        (FO := FO)
        (handler := handler1) (t := u1) (hs := source1) (front := front1)).
      - exact (@Scheduling.ptree_interp_cofinal_all E F MN MF FI MX FO
          Ord BindOrd MixedOrd Directed handler1 A u1).
      - exact Hsource1.
      - exact Hfront1. }
    assert (Htarget2 : @ptree_stable_hitting F MN MF
      FI
      MX
      FO B
      (observe (PTree.interp handler2 u2))
      (sem_bind source2 front2)).
    { eapply (ptree_stable_hitting_interp
        (FI := FI)
        (FO := FO)
        (handler := handler2) (t := u2) (hs := source2) (front := front2)).
      - exact (@Scheduling.ptree_interp_cofinal_all E F MN MF FI MX FO
          Ord BindOrd MixedOrd Directed handler2 B u2).
      - exact Hsource2.
      - exact Hfront2. }
    eapply stable_hitting_match_of_hitting_lift;
      [exact Htarget1|exact Htarget2|].
    eapply sem_lift_bind; [exact HsourceLift|].
    intros h1 h2 Hhead. inversion Hhead; subst; clear Hhead.
    + eapply (sem_lift_mono (SI := FI)).
      * apply ptree_stable_head_rel_mono.
        intros x1 x2 Hknown. right. left. exact Hknown.
      * eapply peutt_state_hitting_lift.
        -- apply peutt_ret. exact H.
        -- exact (Hfront1 (FHRet r1)).
        -- exact (Hfront2 (FHRet r2)).
    + pose proof (stable_hitting_match_hitting_lift
        (FI := FI) (FO := FO)
        (Hvis X e k1 k2 H)
        (Hfront1 (FHVis e k1))
        (Hfront2 (FHVis e k2))) as HvisLift.
      cbn in HvisLift. exact HvisLift.
  - exists t1, t2. repeat split; try reflexivity. exact Hsource.
  Unshelve. all: typeclasses eauto.
Qed.

End Preservation.

