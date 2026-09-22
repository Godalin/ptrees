(** Deprecated weighted rational interface and term syntax. Maintained finite
    probability carriers use ordinary rat through FiniteEnum/FiniteSubdist.
    This module is not imported by the maintained EnumQ backend. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.
Require Import Setoid.
Require Import Program.
Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import order ssralg ssrint rat.

Require Import PTree.Prob.Legacy.RatSubTypes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Open Scope subrat_scope.

(** The Inference Problem Representation for discrete cases *)
Section Interface.
Import NonnegQNotations.

(* The semantics is defined as [Mass] functions. *)
(* Definition Mass (X : Type) := X → ℚ≥0. *)

(* Record Mass_Monad := *)
(*   { ret_mass := fun A x y => if x == y then 1 else 0 *)
(*   ; bind_mass := fun A B f g x => fun y => f x y * g y; *)
(*   }. *)



Class Discrete (m : Type → Type) := {
  disc_ret : forall {A}, A → m A;
  disc_bind : forall {A B}, m A → (A → m B) → m B;
  disc_flip : () → m bool;
  disc_score : nnQ → m ()%type;
}.

(** Discrete Laws:
  bind (ret x) f ≃ f x
  bind m ret ≃ m
  bind m (λ x, bind (f x) g) ≃ bind (bind m f) g
  bind m (λ x, bind n (λ y, f x y)) ≃ bind n (λ y, bind m (λ x, f x y))
  *)

Class DiscreteLaws (m : Type → Type) `{Discrete m}
  (R : forall {a}, m a → m a → Prop) :=

  { disc_ret_bind : forall A B (x : A) (f : A → m B),
    R (disc_bind (disc_ret x) f) (f x)

  ; disc_bind_ret : forall A (u : m A),
    R (disc_bind u disc_ret) u

  ; disc_bind_assoc : forall A B C (u : m A) (f : A → m B) (g : B → m C),
    R (disc_bind u (λ x, disc_bind (f x) g))
      (disc_bind (disc_bind u f) g)

  ; disc_comm_law : forall A B C (u : m A) (v : m B) (f : A → B → m C),
    R (disc_bind u (λ x, disc_bind v (λ y, f x y)))
      (disc_bind v (λ y, disc_bind u (λ x, f x y)))
  }.

Class DiscreteInterface (M : Type → Type) : Type :=
  { disc_rep :: Discrete M

  (* ; disc_laws :: DiscreteLaws *)

  (** The equality for discrete representations *)
  ; disc_eq : ∀ {R : eqType}, M R → M R → Prop

  (** The equality should be some [Equivalence] *)
  ; disc_eq_equiv :: ∀ R : eqType,
      Equivalence (@disc_eq R)

  (** We need a relation transformer *)
  ; disc_RT : ∀ {R1 R2 : eqType},
      (R1 → R2 → Prop) → M R1 → M R2 → Prop

  (** The transformed [disc_RT eq] should coincide with [disc_eq] *)
  ; disc_RTeq : ∀ (R : eqType) (μ1 μ2 : M R),
      disc_eq μ1 μ2 ↔ disc_RT eq μ1 μ2

  (** A mass operator for getting the probability mass *)
  ; disc_mass {R : eqType} : R → M R → nnQ

  (** The mass operator should be proper.  *)
  ; disc_mass_proper {R : eqType} {x : R} ::
      Proper (disc_RT eq ==> eq) (disc_mass x)

  (** supp *)
  ; disc_supp {R : eqType} : M R → seq R
  }.

Context {M : Type → Type}.
Context `{DiscreteInterface M}.

(** "easy-to-use" [Equivalence] for [disc_RT] when  is given *)
#[global] Instance dist_RT_equiv {X : eqType}
  : @Equivalence (M X) (disc_RT eq).
Proof. split.
  - unfold Reflexive. intros. apply disc_RTeq. reflexivity.
  - unfold Symmetric. intros. apply disc_RTeq. symmetry.
    apply disc_RTeq. assumption.
  - unfold Transitive. intros. apply disc_RTeq.
    etransitivity; apply disc_RTeq; eassumption.
Qed.

End Interface.



(** The [Term] Representation *)
Module Term.
Import NonnegQNotations.

Inductive Term (A : Type) :=
  | Return : nnQ → A → Term A
  | Flip : Term A → Term A → Term A.

Arguments Return {A} _ _.
Arguments Flip {A} _ _.

Fixpoint scale_Term {A} (s : nnQ) (t : Term A) : Term A :=
  match t with
  | Return p x => Return (s * p) x
  | Flip k_false k_true =>
    Flip (scale_Term s k_false) (scale_Term s k_true)
  end.

Fixpoint bind_Term {A B} (a : Term A) (f : A → Term B) :=
  match a with
    | Return r x => scale_Term r (f x)
    | Flip k_true k_false =>
      Flip (bind_Term k_true f) (bind_Term k_false f)
  end.

#[global]
Instance Term_Discrete : Discrete Term :=
  {|disc_ret := λ A x, Return 1 x
  ; disc_bind := @bind_Term
  ; disc_flip := λ _, Flip
      (Return 1 true)
      (Return 1 false)
  ; disc_score := λ r : ℚ≥0, Return r tt
  |}.

End Term.
