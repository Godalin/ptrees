(** Observable quotient equality does not entail raw approximation order.
    These counterexamples guard the probability-level bind abstraction. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed BindOrder.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NegativeOrderBoundary.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.

Example constant_lub_quotient_equal :
  free_omega_qlift eq (@FORet MN unit tt) (FOLub (fun _ => FORet tt)).
Proof. apply FOQLLubConstantR, FOQLStructural; constructor; reflexivity. Qed.

Example constant_lub_not_approx_forward :
  ~ free_omega_approx eq (@FORet MN unit tt) (FOLub (fun _ => FORet tt)).
Proof. intro H; inversion H. Qed.

Example constant_lub_not_approx_backward :
  ~ free_omega_approx eq (FOLub (fun _ => @FORet MN unit tt)) (FORet tt).
Proof. intro H; inversion H. Qed.

Example observable_equality_does_not_imply_order :
  ~ (forall (mu nu : FreeOmega MN unit),
    @sem_eq (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) _ mu nu ->
    @sem_le (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _ mu nu).
Proof.
  cbn. intro H. apply constant_lub_not_approx_forward.
  apply H, constant_lub_quotient_equal.
Qed.

Example sampled_zero_quotient_equal {A B} (mu : MN A) :
  free_omega_qlift (@eq B) (FOSample mu (fun _ => FOZero)) FOZero.
Proof. apply FOQLSampleZero. Qed.

Example sampled_zero_not_approx_bottom {A B} (mu : MN A) :
  ~ free_omega_approx (@eq B) (FOSample mu (fun _ => FOZero)) FOZero.
Proof. intro H; inversion H. Qed.
End NegativeOrderBoundary.
