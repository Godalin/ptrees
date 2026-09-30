(** Weak native profile for relational closure and eventful iteration.
    Concrete backend integration is tested separately, not replayed per law. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import PStruct PStrong PEutt Relation Algebra Iter.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Set Implicit Arguments.
Unset Strict Implicit.


Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.RelationalLimit.
Section Completion.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

(** No native AELift/Bind/CountableAE premise has been added. *)
Lemma completion_strong {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) :
  pstrong RR t u ->
  @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO A B RR t u.
Proof.
  apply (Relation.peutt_of_pstrong free_omega_relational_bind
    free_omega_relational_mixed_bind free_omega_relational_zero free_omega_relational_lub).
Qed.

Lemma completion_assoc {A B C} (t : ptree E MN A)
    (k : A -> ptree E MN B) (h : B -> ptree E MN C) :
  @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO C C eq
    (PTree.bind (PTree.bind t k) h) (PTree.bind t (fun a => PTree.bind (k a) h)).
Proof.
  apply (Algebra.peutt_bind_assoc free_omega_relational_bind
    free_omega_relational_mixed_bind free_omega_relational_zero free_omega_relational_lub).
Qed.
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
