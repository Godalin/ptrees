(** Role: Backend-independent setoid rewriting, derived from generic bind.
    No completion representation or external validation model is selected here. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import PEutt Bind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Algebra.
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

#[global] Instance peutt_bind_Proper {A B} :
  Proper
    (@peutt E MN MF FI FC MX FO A A eq ==>
     pointwise_relation A (@peutt E MN MF FI FC MX FO B B eq) ==>
     @peutt E MN MF FI FC MX FO B B eq)
    (@PTree.bind E MN A B).
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

#[global] Instance peutt_fmap_Proper {A B} (f : A -> B) :
  Proper
    (@peutt E MN MF FI FC MX FO A A eq ==>
     @peutt E MN MF FI FC MX FO B B eq)
    (PTree.fmap f).
Proof.
  intros t1 t2 Ht. unfold PTree.fmap.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. apply peutt_refl.
Qed.
End Algebra.
