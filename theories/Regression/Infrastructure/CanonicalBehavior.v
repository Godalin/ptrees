(** Independent import-order probe: CanonicalBehavior.
    Full relation equality checks MF/FI/MX/FO, not just carrier inference.
    The public glyph must retain that profile in this independent session. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Warnings "-notation-overridden".
From mathcomp Require Import reals.
From PTree Require Import PTree PTreeFacts.
From PTree.Eq Require Import Canonical.
From PTree.Eq.Backend Require Import EnumQ SubEnumQ SubEnumR.
Require PTree.Prob.FreeOmega.StructuralMeasure.
Require PTree.Prob.Backend.EnumQ.Measure.

Module NQ := PTree.Prob.Backend.EnumQ.Measure.
Module SQ := PTree.Prob.Backend.SubEnumQ.Measure.
Module NR := PTree.Prob.Backend.SubEnumR.Measure.
Module CR := PTree.Prob.Backend.SubEnumR.Coupling.
Module OR := PTree.Prob.Backend.SubEnumR.Omega.
Module FM := PTree.Prob.FreeOmega.Measure.
Module FS := PTree.Prob.FreeOmega.StructuralMeasure.
Module FD := PTree.Prob.FreeOmega.Definition.

Section ExactRoutes.
Context {E : Type -> Type} {A B : Type} (RR : A -> B -> Prop).

Example rational_weighted_route
    (t : ptree E (PTree.Prob.Backend.EnumQ.Representation.EnumQ.EnumQ) A) (u : ptree E (PTree.Prob.Backend.EnumQ.Representation.EnumQ.EnumQ) B) :
  (t ≈ₚ[RR] u) =
  @PEutt.peutt E (PTree.Prob.Backend.EnumQ.Representation.EnumQ.EnumQ) (FD.FreeOmega (PTree.Prob.Backend.EnumQ.Representation.EnumQ.EnumQ))
    (@FM.FreeOmegaObservableSemanticMeasure _ (NQ.EnumQ_SemanticMeasure) (NQ.EnumQ_SemanticOmega))
    (@FM.FreeOmegaObservableSemanticMeasureCoreLaws _ (NQ.EnumQ_SemanticMeasure) (NQ.EnumQ_SemanticMeasureCoreLaws) (NQ.EnumQ_SemanticOmega))
    (@FS.FreeOmegaMixedMeasure _)
    (@FM.FreeOmegaObservableSemanticOmega _ (NQ.EnumQ_SemanticMeasure) (NQ.EnumQ_SemanticOmega))
    A B RR t u.
Proof. reflexivity. Qed.

Example rational_subprob_route
    (t : ptree E (PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ) A) (u : ptree E (PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ) B) :
  (t ≈ₚ[RR] u) =
  @PEutt.peutt E (PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ) (FD.FreeOmega (PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ))
    (@FM.FreeOmegaObservableSemanticMeasure _ (SQ.SubEnumQ_SemanticMeasure) (SQ.SubEnumQ_SemanticOmega))
    (@FM.FreeOmegaObservableSemanticMeasureCoreLaws _ (SQ.SubEnumQ_SemanticMeasure) (SQ.SubEnumQ_SemanticMeasureCoreLaws) (SQ.SubEnumQ_SemanticOmega))
    (@FS.FreeOmegaMixedMeasure _)
    (@FM.FreeOmegaObservableSemanticOmega _ (SQ.SubEnumQ_SemanticMeasure) (SQ.SubEnumQ_SemanticOmega))
    A B RR t u.
Proof. reflexivity. Qed.

Example real_subprob_route (R : realType)
    (t : ptree E (PTree.Prob.Backend.SubEnumR.Representation.SubEnumR R) A) (u : ptree E (PTree.Prob.Backend.SubEnumR.Representation.SubEnumR R) B) :
  (t ≈ₚ[RR] u) =
  @PEutt.peutt E (PTree.Prob.Backend.SubEnumR.Representation.SubEnumR R) (FD.FreeOmega (PTree.Prob.Backend.SubEnumR.Representation.SubEnumR R))
    (@FM.FreeOmegaObservableSemanticMeasure _ (NR.SubEnumR_SemanticMeasure R) (OR.SubEnumR_SemanticOmega R))
    (@FM.FreeOmegaObservableSemanticMeasureCoreLaws _ (NR.SubEnumR_SemanticMeasure R) (CR.SubEnumR_SemanticMeasureCoreLaws R) (OR.SubEnumR_SemanticOmega R))
    (@FS.FreeOmegaMixedMeasure _)
    (@FM.FreeOmegaObservableSemanticOmega _ (NR.SubEnumR_SemanticMeasure R) (OR.SubEnumR_SemanticOmega R))
    A B RR t u.
Proof. reflexivity. Qed.
End ExactRoutes.

Section PublicBindRoutes.
Local Notation QNative := PTree.Prob.Backend.EnumQ.Representation.EnumQ.EnumQ.
Local Notation RNative := PTree.Prob.Backend.SubEnumR.Representation.SubEnumR.
Context {E : Type -> Type} {A B X Y : Type}.
Context (RR : X -> Y -> Prop) (RS : A -> B -> Prop).

Example weighted_bind_route
    (t : ptree E QNative X) (u : ptree E QNative Y)
    (k : X -> ptree E QNative A) (l : Y -> ptree E QNative B)
    (Ht : t ≈ₚ[RR] u)
    (Hk : forall x y, RR x y -> k x ≈ₚ[RS] l y) :
  bind t k ≈ₚ[RS] bind u l.
Proof. eapply peutt_bind; eassumption. Qed.

Example real_bind_route (R : realType)
    (t : ptree E (RNative R) X) (u : ptree E (RNative R) Y)
    (k : X -> ptree E (RNative R) A)
    (l : Y -> ptree E (RNative R) B)
    (Ht : t ≈ₚ[RR] u)
    (Hk : forall x y, RR x y -> k x ≈ₚ[RS] l y) :
  bind t k ≈ₚ[RS] bind u l.
Proof. eapply peutt_bind; eassumption. Qed.
End PublicBindRoutes.

Section NoBlanket.
Context (MN : Type -> Type).
Fail Definition generic_route : CanonicalBehavior MN := _.
Fail Definition generic_notation {E A} (t : ptree E MN A) := (t ≈ₚ t).
End NoBlanket.

Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
