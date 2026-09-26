(** Loading the support module is not opting in. Once explicitly imported,
    the same registrations work for arbitrary native carriers. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import State Exception.
From PTree.Interp.FreeOmega Require Import Rewriting.
Set Implicit Arguments.
Unset Strict Implicit.

Fail Check PTree.Eq.Canonical.canonical_peutt.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Module OptIn.
Section Native.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation W := (peutt (FI := FI) (MX := FreeOmegaMixedMeasure)
  (FO := FreeOmegaObservableSemanticOmega)).

Fail Definition no_implicit_iter_registration {E I A} :
  Proper (pointwise_relation I (W eq) ==> eq ==> W eq) (@PTree.iter E MN A I) :=
  ltac:(typeclasses eauto).

Import FreeOmegaRewriting.

Example imported_state_proper {S E A} :
  Proper (W eq ==> eq ==> W eq) (@run_state S E MN A).
Proof. typeclasses eauto. Qed.

Example imported_interp_proper {E F A} (h : forall X, E X -> ptree F MN X) :
  Proper (W eq ==> W eq) (@PTree.interp E F MN h A).
Proof. typeclasses eauto. Qed.

Example imported_exception_proper {Err E A} :
  Proper (W eq ==> W eq) (@run_exception Err E MN A).
Proof. typeclasses eauto. Qed.

Example imported_iter_proper {E I A} :
  Proper (pointwise_relation I (W eq) ==> eq ==> W eq) (@PTree.iter E MN A I).
Proof. typeclasses eauto. Qed.

Example imported_iter_rewrite {E I A} (f g : I -> ptree E MN (I+A))
    (H : pointwise_relation I (W eq) f g) i :
  W eq (PTree.iter f i) (PTree.iter g i).
Proof. setoid_rewrite H. apply peutt_refl. Qed.
End Native.
End OptIn.

(** Import in a client module must not silently register the instances for
    every later client. In particular AllImports is not an opt-in. *)
Section OutsideClient.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation W := (peutt (FI := FI) (MX := FreeOmegaMixedMeasure)
  (FO := FreeOmegaObservableSemanticOmega)).
Fail Definition no_leaked_iter_registration {E I A} :
  Proper (pointwise_relation I (W eq) ==> eq ==> W eq) (@PTree.iter E MN A I) :=
  ltac:(typeclasses eauto).
End OutsideClient.

From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Module RealClient.
Import FreeOmegaRewriting.
Section Client.
Variable R : realType.
Context {E : Type -> Type} {I A : Type}.
Local Notation MN := (SubEnumR R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation W := (peutt (E := E) (FI := FI)).
Example imported_real_iter_rewrite (f g : I -> ptree E MN (I+A))
    (H : pointwise_relation I (W eq) f g) i :
  W eq (PTree.iter f i) (PTree.iter g i).
Proof. setoid_rewrite H. apply peutt_refl. Qed.
End Client.
End RealClient.

From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
Module RationalClient.
Import FreeOmegaRewriting.
Section Client.
Context {E : Type -> Type} {I A : Type}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation W := (peutt (E := E) (FI := FI)).
Example imported_rational_iter_rewrite (f g : I -> ptree E SubEnumQ (I+A))
    (H : pointwise_relation I (W eq) f g) i :
  W eq (PTree.iter f i) (PTree.iter g i).
Proof. setoid_rewrite H. apply peutt_refl. Qed.
End Client.
End RationalClient.
