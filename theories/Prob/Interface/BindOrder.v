(** Approximation-compatible finite bind algebra. These laws do NOT assert
    sem_eq -> sem_le: observable equality may forget approximation structure.
    The paired inequalities are just preorder equivalence, not another
    public equality. Extracted from the explicit BindScheduling prototype. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Polymorphic Class SemanticMeasureBindOrderLaws
    (MF : Type → Type) `{FI : SemanticMeasure MF}
    `{FO : @SemanticOmega MF FI} := {
  sem_bind_ret_order : ∀ A B (x : A) (k : A → MF B),
    sem_le (sem_bind (sem_ret x) k) (k x) ∧
    sem_le (k x) (sem_bind (sem_ret x) k);
  sem_bind_zero_order : ∀ A B (k : A → MF B),
    sem_le (sem_bind sem_zero k) sem_zero
}.

Polymorphic Class MixedMeasureBindOrderLaws
    (MN MF : Type → Type) `{FI : SemanticMeasure MF}
    `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI} := {
  mixed_bind_assoc_order : ∀ A B C (mu : MN A)
      (k : A → MF B) (h : B → MF C),
    sem_le (sem_bind (mixed_bind mu k) h)
      (mixed_bind mu (fun x => sem_bind (k x) h)) ∧
    sem_le (mixed_bind mu (fun x => sem_bind (k x) h))
      (sem_bind (mixed_bind mu k) h);
  mixed_bind_le_k : ∀ A B (mu : MN A) (k h : A → MF B),
    (∀ x, sem_le (k x) (h x)) →
    sem_le (mixed_bind mu k) (mixed_bind mu h)
}.
