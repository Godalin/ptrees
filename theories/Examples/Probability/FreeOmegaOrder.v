(** Role: finite probability/coupling/backend example. *)
(** Observable quotient equality does not entail raw approximation order.
    These counterexamples guard the probability-level bind abstraction. *)
From Coq Require Import Utf8 Morphisms Setoid.

Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed BindOrder.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.BindOrder.
From PTree.Prob.FreeOmega Require Import IterationOrder.
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NegativeOrderBoundary.
Context {MN : Type → Type} `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.

Example constant_lub_quotient_equal :
  free_omega_qlift eq (@FORet MN unit tt) (FOLub (λ _, FORet tt)).
Proof. apply FOQLLubConstantR, FOQLStructural; constructor; reflexivity. Qed.

Example constant_lub_not_approx_forward :
  ¬ free_omega_approx eq (@FORet MN unit tt) (FOLub (λ _, FORet tt)).
Proof. intro H; inversion H. Qed.

Example constant_lub_not_approx_backward :
  ¬ free_omega_approx eq (FOLub (λ _, @FORet MN unit tt)) (FORet tt).
Proof. intro H; inversion H. Qed.

Example observable_equality_does_not_imply_order :
  ¬ (∀ (mu nu : FreeOmega MN unit),
    @sem_eq (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)) _ mu nu →
    @sem_le (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmega _ mu nu).
Proof.
  cbn. intro H. apply constant_lub_not_approx_forward.
  apply H, constant_lub_quotient_equal.
Qed.

Example sampled_zero_quotient_equal {A B} (mu : MN A) :
  free_omega_qlift (@eq B) (FOSample mu (λ _, FOZero)) FOZero.
Proof. apply FOQLSampleZero. Qed.

Example sampled_zero_not_approx_bottom {A B} (mu : MN A) :
  ¬ free_omega_approx (@eq B) (FOSample mu (λ _, FOZero)) FOZero.
Proof. intro H; inversion H. Qed.
End NegativeOrderBoundary.

(** The public semantic preorder repairs exactly the mismatch above,
    without changing the structural relation used for scheduling. *)
Section SemanticOrder.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.

Example constant_lub_semantic_both_directions :
  @FORet MN unit tt ⊑ω FOLub (λ _, FORet tt) ∧
  FOLub (λ _, @FORet MN unit tt) ⊑ω FORet tt.
Proof.
  split.
  - apply free_omega_sem_eq_le, constant_lub_quotient_equal.
  - apply free_omega_lub_least.
    + intro n; constructor; reflexivity.
    + intro n; apply free_omega_sem_le_refl.
Qed.

Example semantic_order_strictly_extends_structural :
  (@FORet MN unit tt ⊑ω FOLub (λ _, FORet tt)) ∧
  ¬ free_omega_approx eq (@FORet MN unit tt) (FOLub (λ _, FORet tt)).
Proof.
  split; [apply constant_lub_semantic_both_directions|apply constant_lub_not_approx_forward].
Qed.

Example quotient_rewrite_in_order {A} (t u bound : FreeOmega MN A) :
  free_omega_qlift eq t u → u ⊑ω bound → t ⊑ω bound.
Proof. intros H G. rewrite H. exact G. Qed.

Example unequal_diracs_not_structurally_increasing :
  ¬ free_omega_struct_increasing
    (λ n, @FORet MN bool (match n with O => true | S _ => false end)).
Proof. intro H. specialize (H O). inversion H; discriminate. Qed.

(** A pre-fixed-point proof bounds an unbounded loop without calculating
    any finite distributions. Endless retry selects bottom, not a Dirac. *)
Example endless_retry_semantic_bottom :
  free_omega_iter (λ i : unit, @FORet MN (unit+bool) (inl i)) tt ⊑ω FOZero.
Proof.
  apply (free_omega_iter_least_prefixed (Y := λ _, FOZero)).
  intro i; apply free_omega_sem_le_refl.
Qed.
End SemanticOrder.
