(** Generic heterogeneous bind congruence. Finite scheduling follows from
    probability-level approximation algebra; no backend-specific PTree
    cofinality premise or classical choice is supplied by the caller. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import PTreeKernel PEutt BindScheduling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Bind.
Context {E MN MF : Type -> Type}
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

Theorem peutt_bind {A B R1 R2} (RR : R1 -> R2 -> Prop) (RS : A -> B -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2)
    (k1 : R1 -> ptree E MN A) (k2 : R2 -> ptree E MN B) :
  peutt (MF := MF) RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> peutt (MF := MF) RS (k1 r1) (k2 r2)) ->
  peutt (MF := MF) RS (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intros Ht Hk.
  refine (@peutt_bind_cofinal E MN MF FI FC FB MX FO Ord Omega Cofinal
    Diagonal _ Select A B R1 R2 RR RS t1 t2 k1 k2 Ht Hk).
  intros X Y t k. apply BindScheduling.ptree_bind_cofinal_all.
  - exact (@sem_bind_ret_order MF FI FO BindOrd).
  - exact (@sem_bind_zero_order MF FI FO BindOrd).
  - exact (@mixed_bind_assoc_order MN MF FI MX FO MixedOrd).
  - exact (@mixed_bind_le_k MN MF FI MX FO MixedOrd).
  - exact (@sem_lub_cofinal MF FI FO Directed).
Qed.
End Bind.
