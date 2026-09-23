(** Generic ownership and completion specialization, without inference magic. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import Iter PEutt.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition generic_eventful_iter := @peutt_iter_eventful_of_generator_closed.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure.
Section Completion.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I1 I2 A B : Type}.
Variable step1 : I1 -> ptree E MN (I1 + A).
Variable step2 : I2 -> ptree E MN (I2 + B).
Variable SI : I1 -> I2 -> Prop.
Variable RR : A -> B -> Prop.

Lemma free_omega_eventful_iter
    (H : @iter_eventful_generator_closed E MN (FreeOmega MN) FI
      FreeOmegaMixedMeasure FO I1 I2 A B step1 step2 SI RR) i j :
  SI i j -> @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.iter step1 i) (PTree.iter step2 j).
Proof. intro Hij. exact (peutt_iter_eventful_of_generator_closed H Hij). Qed.
End Completion.
