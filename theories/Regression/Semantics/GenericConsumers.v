(** Generic ownership and completion specialization, without inference magic. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import Iter PEutt.
From PTree.Interp Require Import Scheduling Preservation Guarded.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition generic_eventful_iter := @peutt_iter_eventful_of_generator_closed.
Definition generic_guarded_contract := @guarded_handler.
Definition generic_guarded_interp := @peutt_interp_guarded.
Definition generic_interp_schedule := @ptree_interp_cofinal_all.

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

(** The real-weight native model assembles the same interpretation theorem,
    without a second completion or interpreter proof. *)
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.BindOrder.
Section RealInterpretation.
Variable R : realType.
Context {E F : Type -> Type} {A B : Type}.
Local Notation MN := (SubEnumR R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Variable handler : forall X, E X -> ptree F MN X.
Variable RR : A -> B -> Prop.

Example real_guarded_interp
    (Hg : @Guarded.guarded_handler E F MN (FreeOmega MN) FI FreeOmegaMixedMeasure FO handler)
    (t : ptree E MN A) (u : ptree E MN B) :
  @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR t u ->
  @peutt F MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t) (PTree.interp handler u).
Proof. apply Guarded.peutt_interp_guarded. exact Hg. Qed.
End RealInterpretation.
