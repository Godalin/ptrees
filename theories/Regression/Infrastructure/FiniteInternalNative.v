(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum MathCompMeasure TwoLevelMeasureMathComp.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq.Internal Require Import FiniteInternal FiniteInternalPlan.
From PTree.Eq Require Import PStrong.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalJoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GenericPaths.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

(** Branch-dependent path types and unbounded branchwise Tau prefixes.
    No finite-support or uniform-depth assumption appears in this test. *)
Example dependent_compression_round_native {X} {Y : X -> Type}
    (mu : MN X) (nu : forall x, MN (Y x))
    (depth : forall x, Y x -> nat) (k : forall x, Y x -> tree) :
  exists p, free_omega_qlift eq
    (free_omega_bind
      (FOSample mu (fun x => FOSample (nu x) (fun y => FORet (k x y))))
      finite_internal_guard_transition) (free_omega_native p).
Proof.
  eapply (@finite_internal_round_native_presentation E MN NI NC NO ND NBAE R) with
    (t := Prob mu (fun x => Tau (Prob (nu x)
      (fun y => tau_prefix (depth x y) (k x y))))).
  apply (@FIProb E MN MF FI FreeOmegaMixedMeasure). intro x. apply FITau.
  apply (@FIProb E MN MF FI FreeOmegaMixedMeasure). intro y.
  apply (@finite_internal_tau_prefix E MN MF FI FreeOmegaMixedMeasure).
Qed.

End GenericPaths.

(** Native path normalization preserves the carrier's subprobability bound;
    it does not normalize a partial computation to total mass one. *)
Example subenum_compression_measure_bounded {E : Type -> Type} {R}
    (t : ptree E SubEnum R) out :
  @finite_internal E SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaMixedMeasure R t out ->
  exists p : free_omega_native_presentation SubEnum (ptree E SubEnum R),
    free_omega_qlift eq out (free_omega_native p) /\
    enum_subprob (subenum_raw (native_sample_measure p)).
Proof.
  intro Hcut. destruct (finite_internal_native_presentation Hcut) as [p Hp].
  exists p. split; [exact Hp|apply subenum_bound].
Qed.

(** MathComp needs its existing core gluing capability, Dirac AE, and bind
    AE exactness.  No node SemanticMeasureBindLaws is postulated. *)
Section MathCompPaths.
Context (Real : realType) `{MathCompCouplingGluing Real}.
Context {E : Type -> Type} {R : Type}.
Local Notation MN := (MathCompKernelMeasure Real).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := MathCompNodeSemanticMeasure Real) (NO := MathCompNodeSemanticOmega Real)).

Example mathcomp_compression_native (t : ptree E MN R) out :
  @finite_internal E MN (FreeOmega MN) FI FreeOmegaMixedMeasure R t out ->
  exists p : free_omega_native_presentation MN (ptree E MN R),
    free_omega_qlift eq out (free_omega_native p).
Proof. apply finite_internal_native_presentation. Qed.
End MathCompPaths.
