(** Phase 3: the native real backend IS the shared finite carrier. These
    are definitional interoperation tests, not conversion/embedding tests. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
From PTree.Prob.Interface Require Import Measure Subprobability Omega.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.

Fail Check PTree.Prob.Backend.SubEnumR.Representation.Build_SubEnumR.
Fail Check PTree.Prob.Backend.SubEnumR.Representation.SubEnumR_rect.
Fail Check PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section SharedReal.
Variable R : realType.

Example shared_carrier {A} : SubEnumR R A = FiniteSubdist R A.
Proof. reflexivity. Qed.
Example shared_ret {A} (x : A) : subenumR_ret R x = finite_subdist_ret R x.
Proof. reflexivity. Qed.
Example shared_zero {A} : @subenumR_zero R A = @finite_subdist_zero R A.
Proof. reflexivity. Qed.
Example shared_bind {A B} (mu : SubEnumR R A) (k : A -> FiniteSubdist R B) :
  subenumR_bind mu k = finite_subdist_bind mu k.
Proof. reflexivity. Qed.
Example shared_expectation {A} (mu : SubEnumR R A) f :
  subenumR_expect mu f = finite_subdist_expect mu f.
Proof. reflexivity. Qed.
Example shared_raw_projection {A} (mu : SubEnumR R A) :
  subenumR_raw mu = finite_enum_raw (finite_subdist_enum mu).
Proof. reflexivity. Qed.

Definition common_to_native {A} (mu : FiniteSubdist R A) : SubEnumR R A := mu.
Definition native_to_common {A} (mu : SubEnumR R A) : FiniteSubdist R A := mu.
Example no_conversion_roundtrip {A} (mu : FiniteSubdist R A) :
  native_to_common (common_to_native mu) = mu.
Proof. reflexivity. Qed.

(** A list constructed by the shared API immediately supports native
    equality, AE and actual-joint lifting, without rebuilding invariants. *)
Definition common_with_null : FiniteSubdist R bool.
Proof.
  refine (finite_subdist_of_list (mu := [(1,true); (0,false)]) _ _).
  - intros p b [H|[H|[]]]; inversion H; subst; [exact: ler01|exact: lexx].
  - by rewrite /= !mulr1 !addr0.
Defined.
Example shared_input_native_ae : subenumR_ae common_with_null (fun b => b = true).
Proof.
  intros p b [H|[H|[]]] Hnz; inversion H; subst; first reflexivity.
  exfalso; exact (Hnz (Logic.eq_refl _)).
Qed.
Example shared_input_native_crossed_coupling :
  subenumR_lift (fun b c => negb b = c) common_with_null (subenumR_map negb common_with_null).
Proof. exact: subenumR_lift_map. Qed.
Example shared_bind_native_mass {A B} (mu : FiniteSubdist R A) (k : A -> FiniteSubdist R B) :
  @sem_subprob (SubEnumR R) (SubEnumR_SemanticMeasure R)
    (SubEnumR_SemanticSubprobability R) B (finite_subdist_bind mu k).
Proof. exact (finite_subdist_mass_bound _). Qed.

Local Notation NI := (SubEnumR_SemanticMeasure R).
Local Notation NO := (SubEnumR_SemanticOmega R).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Definition shared_completion_core : @SemanticMeasureCoreLaws (FreeOmega (FiniteSubdist R)) FI := _.
Definition shared_completion_bind : @SemanticMeasureBindLaws (FreeOmega (FiniteSubdist R)) FI := _.
Definition shared_completion_omega : @SemanticOmegaLaws (FreeOmega (FiniteSubdist R)) FI
    (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)) := _.
Fail Definition shared_native_omega_complete : @SemanticOmegaLaws (FiniteSubdist R) NI NO := _.
End SharedReal.

Section HighCarrier.
Universe u.
Variable R : realType.
Definition high_shared_native (A : Type@{u}) : SubEnumR R Type@{u} := finite_subdist_ret R A.
Example high_shared_native_bind (A : Type@{u}) (f : Type@{u} -> R) :
  subenumR_expect (subenumR_bind (high_shared_native A) (fun X => finite_subdist_ret R X)) f = f A.
Proof.
  change (finite_subdist_expect
    (finite_subdist_bind (finite_subdist_ret R A) (fun X => finite_subdist_ret R X)) f = f A).
  by rewrite finite_subdist_bind_ret_r finite_subdist_expect_ret.
Qed.
End HighCarrier.
