(** Generic owner and exact old FreeOmega specialization contracts. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PEutt Algebra.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

Definition generic_bind_proper := @peutt_bind_Proper.
Definition generic_fmap_proper := @peutt_fmap_Proper.
Definition derived_ae_lift := @coupling_ae_implies_ae_lift.

(** No native measure instance, bind/order/omega laws, or relational-lub
    certificate is in scope. This is an explicit minimal client signature. *)
Section ShallowClient.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}.
Example generic_left_unit_minimal {A B} (a : A) (k : A -> ptree E MN B) :
  @peutt E MN MF FI FC MX FO B B eq (PTree.bind (Ret a) k) (k a).
Proof. apply peutt_bind_ret_l. Qed.
End ShallowClient.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeOmegaClient.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO).

Lemma free_omega_bind_Proper {A B} :
  Proper (W eq ==> pointwise_relation A (W eq) ==> W eq)
    (@PTree.bind E MN A B).
Proof. apply peutt_bind_Proper. Qed.

Lemma free_omega_fmap_Proper {A B} (f : A -> B) :
  Proper (W eq ==> W eq) (PTree.fmap f).
Proof. apply peutt_fmap_Proper. Qed.

Example free_omega_frontier_ae_lift : @SemanticMeasureAELiftLaws MF FI.
Proof. apply coupling_ae_implies_ae_lift. Qed.

Example free_omega_frontier_dirac_ae : @SemanticMeasureDiracAELaws MF FI.
Proof. apply free_omega_observable_dirac_ae_laws. Qed.
End FreeOmegaClient.

(** A second concrete native backend discharges the same generic profile. *)
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Section RealClient.
Variable R : realType.
Context {E : Type -> Type} {A B : Type}.
Local Notation MN := (SubEnumR R).
Local Notation NI := (SubEnumR_SemanticMeasure R).
Local Notation NO := (SubEnumR_SemanticOmega R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (@peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO).

Example real_bind_proper :
  Proper (W eq ==> pointwise_relation A (W eq) ==> W eq) (@PTree.bind E MN A B).
Proof. apply peutt_bind_Proper. Qed.

Example real_fmap_proper (f : A -> B) :
  Proper (W eq ==> W eq) (@PTree.fmap E MN A B f).
Proof. apply peutt_fmap_Proper. Qed.
End RealClient.
