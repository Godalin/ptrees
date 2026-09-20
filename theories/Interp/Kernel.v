(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From PTree.Eq Require Import PTreeKernel.
Section KernelInterpDiagonal.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Definition ptree_interp_head_tree {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : stable_head E MN R) : ptree F MN R :=
  match h with
  | FHRet r => Ret r
  | @FHVis _ _ _ X e k =>
      Tau (PTree.bind (@handler X e)
        (fun x => PTree.interp handler (k x)))
  end.

Definition ptree_interp_head_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (h : stable_head E MN R) :
    MF (stable_head F MN R) :=
  ptree_hitting_approx (MF := MF) fuel
    (observe (ptree_interp_head_tree handler h)).

Definition ptree_interp_diagonal_approx {R}
    (fuel : nat) (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : MF (stable_head F MN R) :=
  sem_bind
    (ptree_hitting_approx (MF := MF) fuel (observe t))
    (ptree_interp_head_approx fuel handler).

Definition ptree_interp_cofinal {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R) : Prop :=
  forall out,
    sem_lub (fun fuel => ptree_hitting_approx (MF := MF) fuel
      (observe (PTree.interp handler t))) out <->
    sem_lub (fun fuel => ptree_interp_diagonal_approx
      fuel handler t) out.

End KernelInterpDiagonal.

Section KernelInterpSoundness.
Context {E F : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FOC : @SemanticOmegaCofinalityLaws MF FI FO}
  `{FDL : @SemanticMeasureDiagonalLaws MF FI FO}.

Lemma ptree_interp_head_approx_increasing {R}
    (handler : forall X, E X -> ptree F MN X)
    (h : stable_head E MN R) :
  sem_increasing (fun fuel => ptree_interp_head_approx
    (MF := MF) fuel handler h).
Proof.
  intro fuel. apply ptree_hitting_increasing.
Qed.

Lemma ptree_interp_head_approx_lub {R}
    (handler : forall X, E X -> ptree F MN X)
    (front : stable_head E MN R -> MF (stable_head F MN R))
    (Hfront : forall h, ptree_stable_hitting (MF := MF)
      (observe (ptree_interp_head_tree handler h)) (front h)) h :
  sem_lub (fun fuel => ptree_interp_head_approx
      (MF := MF) fuel handler h) (front h).
Proof.
  exact (Hfront h).
Qed.

Theorem ptree_stable_hitting_interp {R}
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN R)
    hs (front : stable_head E MN R -> MF (stable_head F MN R)) :
  ptree_interp_cofinal (MF := MF) handler t ->
  ptree_stable_hitting (MF := MF) (observe t) hs ->
  (forall h, ptree_stable_hitting (MF := MF)
    (observe (ptree_interp_head_tree handler h)) (front h)) ->
  ptree_stable_hitting (MF := MF) (observe (PTree.interp handler t))
    (sem_bind hs front).
Proof.
  intros Hcofinal Hsource Hfront. unfold ptree_stable_hitting in *.
  apply (proj2 (Hcofinal _)).
  unfold ptree_interp_diagonal_approx.
  eapply sem_bind_diagonal_lub.
  - apply ptree_hitting_increasing.
  - intro h. apply ptree_interp_head_approx_increasing.
  - exact Hsource.
  - intro h. apply ptree_interp_head_approx_lub. exact Hfront.
Qed.

End KernelInterpSoundness.
