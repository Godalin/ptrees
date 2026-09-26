(** Generic owner and exact old FreeOmega specialization contracts. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PEutt Algebra.
From PTree.Interp Require Import IterationUniform ExceptionFacts StatePreservation Unrestricted.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

Definition generic_bind_proper := @peutt_bind_Proper.
Definition generic_fmap_proper := @peutt_fmap_Proper.
Definition generic_iter_proper := @peutt_iter_Proper.
Definition generic_exception_proper := @run_exception_peutt_eq_Proper.
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

Example generic_prob_bind_minimal {X A B} (mu : MN X)
    (h : X -> ptree E MN A) (k : A -> ptree E MN B) :
  peutt (MF := MF) eq (PTree.bind (Prob mu h) k)
    (Prob mu (fun x => PTree.bind (h x) k)).
Proof. apply peutt_bind_prob. Qed.

Example generic_vis_map_minimal {X A B} (e : E X)
    (h : X -> ptree E MN A) (f : A -> B) :
  peutt (MF := MF) eq (PTree.fmap f (Vis e h))
    (Vis e (fun x => PTree.fmap f (h x))).
Proof. apply peutt_fmap_vis. Qed.
End ShallowClient.

(** Exercise actual rewriting through constructor notations, not merely
    inference of their whole-node Proper declarations. No backend is loaded. *)
Section ConstructorClient.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MO : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Local Notation W := (peutt (MF := MF) eq).

Example generic_vis_context_rewrite {A X} (e : E X)
    (k h : X -> ptree E MN A) (H : pointwise_relation X W k h) :
  W (Vis e k) (Vis e h).
Proof. setoid_rewrite H. reflexivity. Qed.

Example generic_prob_context_rewrite {A X} (mu : MN X)
    (k h : X -> ptree E MN A) (H : pointwise_relation X W k h) :
  W (Prob mu k) (Prob mu h).
Proof. setoid_rewrite H. reflexivity. Qed.
End ConstructorClient.

Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder
  PTree.Prob.FreeOmega.RelationalLimit.

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

Example free_omega_sample_bind {X A} (mu : MN X) (k : X -> ptree E MN A) :
  W eq (PTree.bind (Prob mu (fun x => Ret x)) k) (Prob mu k).
Proof. apply peutt_sample_bind. Qed.

Example free_omega_sample_map `{NDirac : @SemanticMeasureDiracAELaws MN NI}
    `{NBindAE : @SemanticMeasureBindAEExactLaws MN NI}
    {X A} (mu : MN X) (f : X -> A) :
  W eq (Prob mu (fun x => Ret (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) (fun a => Ret a)).
Proof. apply (peutt_sample_map (NI := NI)). Qed.
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

Example real_sample_bind (mu : MN A) (k : A -> ptree E MN B) :
  W eq (PTree.bind (Prob mu (fun x => Ret x)) k) (Prob mu k).
Proof. apply peutt_sample_bind. Qed.

Example real_sample_map (mu : MN A) (f : A -> B) :
  W eq (Prob mu (fun x => Ret (f x)))
    (Prob (sem_bind mu (fun x => sem_ret (f x))) (fun a => Ret a)).
Proof. apply (peutt_sample_map (NI := NI)). Qed.
End RealClient.

(** Register generic iteration locally, then actually rewrite under a loop.
    The native real backend supplies no duplicate iteration theorem. *)
Section RealIteration.
Variable R : realType.
Context {E : Type -> Type} {I A : Type}.
Local Notation MN := (SubEnumR R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation W := (peutt (E := E) (FI := FI)).
#[local] Instance real_iter_rewrite :
  Proper (pointwise_relation I (W eq) ==> eq ==> W eq) (@PTree.iter E MN A I) :=
  peutt_iter_Proper free_omega_relational_zero free_omega_relational_lub.

Example real_iter_setoid (f g : I -> ptree E MN (I+A))
    (H : forall i, W eq (f i) (g i)) i :
  W eq (PTree.iter f i) (PTree.iter g i).
Proof.
  assert (Hpoint : pointwise_relation I (W eq) f g) by exact H.
  setoid_rewrite Hpoint. apply peutt_refl.
Qed.
End RealIteration.
