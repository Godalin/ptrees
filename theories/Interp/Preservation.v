(** Generic interpretation preservation. Complete-head fusion consumes
    only frontier capabilities; finite scheduling is derived independently. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel
  PEutt StableHittingRelation BindScheduling.
From PTree.Interp Require Import Kernel Scheduling RelationalPreservation.
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
  (handler : forall X, E X -> ptree F MN X).

(** The smallest source-indexed candidate needed for full interpreter
    preservation.  It contains no syntax cases: a target-state pair belongs
    to the candidate exactly when it is obtained by interpreting a pair
    already related by the canonical source equivalence. *)
Definition interp_bisim_candidate
    (s1 : ptree' F MN A) (s2 : ptree' F MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe (PTree.interp handler t1) /\
    s2 = observe (PTree.interp handler t2) /\
    @peutt E MN MF
      FI
      FC
      MX
      FO A B RR t1 t2.

(** The irreducible handled-[Vis] obligation.  When the handler returns
    internally, stable hitting crosses the handler bind and immediately
    enters the interpreted source continuation.  Ordinary residual-bind
    compatibility cannot guard that recursive use of [interp_bisim_candidate].

    This property isolates exactly that collapsed segment; Ret heads and the
    outer source stable-hitting composition are derivable from existing laws. *)
Definition interp_vis_fusion : Prop :=
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
        A B RR interp_bisim_candidate)
      (observe (ptree_interp_head_tree handler (FHVis e k1)))
      (observe (ptree_interp_head_tree handler (FHVis e k2))).

(** Full effectful interpreter preservation follows once the single
    collapsed handled-[Vis] fusion above is supplied.  This theorem
    discharges source hitting, Ret heads, outer interpreter scheduling, and
    coupling composition; no broader generator-closure premise remains. *)
Theorem peutt_interp_of_vis_fusion
    (Hvis : interp_vis_fusion) :
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
      (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  apply (peutt_interp_rel_of_vis_fusion (handler1 := handler) (handler2 := handler)).
  exact Hvis.
Qed.

(** Exact closure obligation for an arbitrary effectful handler.  Compared
    with the generic PTree coinduction rule, the candidate is fixed to
    interpreted source equivalence.  Consequently an implementation of this
    premise cannot hide a different behavioral relation or strengthen the
    theorem's conclusion. *)
Definition interp_generator_closed : Prop :=
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @peutt E MN MF
      FI
      FC
      MX
      FO A B RR t1 t2 ->
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
      interp_bisim_candidate
      (observe (PTree.interp handler t1))
      (observe (PTree.interp handler t2)).

(** Full behavioral preservation follows from precisely the candidate-level
    handler closure above.  The canonical generator is unchanged. *)
Theorem peutt_interp_of_generator_closed
    (Hclosed : interp_generator_closed) :
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
      (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intros t1 t2 Hsource.
  eapply peutt_coinduction with
      (sim := interp_bisim_candidate).
  - intros s1 s2 [u1 [u2 [-> [-> Hu]]]]. exact (Hclosed u1 u2 Hu).
  - exists t1, t2. repeat split; try reflexivity. exact Hsource.
Qed.

End Preservation.
