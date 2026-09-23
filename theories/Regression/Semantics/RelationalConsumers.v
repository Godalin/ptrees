(** Generic consumers, unchanged weak completion profile, and real/rational
    clients. No backend-specific upper proof or global inference hints. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Eq Require Import PStruct PStrong PEutt Relation Algebra Iter.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Set Implicit Arguments.
Unset Strict Implicit.

Definition generic_structural_bridge := @Relation.peutt_of_pstruct.
Definition generic_strong_bridge := @Relation.peutt_of_pstrong.
Definition generic_structural_iter := @Iter.peutt_iter_rel.
Definition generic_codiagonal := @Iter.peutt_iter_codiagonal.

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
End Completion.

From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.

Example rational_eventful_assoc {E A B C} (t : ptree E SubEnumQ A)
    (k : A -> ptree E SubEnumQ B) (h : B -> ptree E SubEnumQ C) :
  peutt (MF := FreeOmega SubEnumQ) eq (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun a => PTree.bind (k a) h)).
Proof. apply completion_assoc. Qed.

Example real_eventful_assoc (R : realType) {E A B C} (t : ptree E (SubEnumR R) A)
    (k : A -> ptree E (SubEnumR R) B) (h : B -> ptree E (SubEnumR R) C) :
  peutt (MF := FreeOmega (SubEnumR R)) eq (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun a => PTree.bind (k a) h)).
Proof. apply completion_assoc. Qed.
