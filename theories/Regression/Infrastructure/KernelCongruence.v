(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From mathcomp Require Import eqtype.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.Internal.FreeOmega Require Import KernelCompletion KernelCongruence.
From PTree.Regression.Semantics Require Import PEuttAlgebra.

Set Implicit Arguments.

(** A nonstructural algebraic rewrite can be made in EVERY kernel round,
    including after arbitrary internal state changes.  This is not a
    bounded-prefix test, and no AST or round bound is assumed. *)
Section ExchangeInEveryRound.
Context {S O : Type}.
Variables mu nu : SubEnumQ bool.
Variable next : S -> bool -> bool -> stable_target S O.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Definition first_sample_kernel s : MF (stable_target S O) :=
  FOSample mu (fun x => FOSample nu (fun y => FORet (next s x y))).
Definition swapped_sample_kernel s : MF (stable_target S O) :=
  FOSample nu (fun y => FOSample mu (fun x => FORet (next s x y))).

Lemma sample_exchange_kernel_equal s :
  free_omega_qlift eq (first_sample_kernel s) (swapped_sample_kernel s).
Proof.
  apply free_omega_mixed_exchange_of_product.
  - exact (enumQ_semantic_product_swap (subenumQ_raw mu) (subenumQ_raw nu)).
  - intros x y. apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

Lemma first_sample_kernel_closed s :
  free_omega_ae (kernel_completion_invariant (fun _ : S => True))
    (first_sample_kernel s).
Proof.
  apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
  intros x _. apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
  intros y _. apply FOAERet. destruct (next s x y); exact I.
Qed.

Example sample_exchange_preserves_complete_hitting s out1 out2 :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    S O first_sample_kernel s out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    S O swapped_sample_kernel s out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  intros Hleft Hright.
  eapply (kernel_stable_hitting_eq
    (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
    with (D := fun _ => True) (s := s).
  - intros state _. apply first_sample_kernel_closed.
  - intros state _. apply sample_exchange_kernel_equal.
  - exact I.
  - exact Hleft.
  - exact Hright.
Qed.

End ExchangeInEveryRound.
