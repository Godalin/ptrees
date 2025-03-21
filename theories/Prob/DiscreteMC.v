Require Import Utf8.
Require Import Setoid.
Require Import Program.
Require Import Morphisms.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import order ssralg ssrint rat.

From PTree.Prob Require Import RatSubTypes.

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





(** The [Enum] Representation *)
Module Enum.
Import NonnegQNotations.
Import GRing.Theory.

Definition Enum (A : Type) := seq (ℚ≥0 * A).

Declare Scope enum_scope.
Bind Scope enum_scope with Enum.
Delimit Scope enum_scope with enum.
#[local] Open Scope enum_scope.

Fixpoint scale_Enum {A} (r : ℚ≥0) (e : Enum A) : Enum A :=
  match e with
  | [::] => [::]
  | (s, x) :: e' => (r * s, x) :: scale_Enum r e'
  end.

Lemma scale_app : ∀ A r (u v : Enum A),
  scale_Enum r (u ++ v) = scale_Enum r u ++ scale_Enum r v.
Proof. move=> A r u v. move: r. elim: u => [//|[t a] us] IH r //=.
  congr cons. rewrite IH //.
Qed.

Lemma scale_scale : ∀ {A} r s (u : Enum A),
  scale_Enum r (scale_Enum s u) = scale_Enum (r * s) u.
Proof. move=> A r s u. elim: u => [//|[t a] us] IH //=.
rewrite {}IH. congr cons. congr pair. rewrite mulrA //.
Qed.

Definition ret_Enum {A} (x : A) : Enum A := [:: (1, x)].

Definition bind_Enum {A B} (xs : Enum A) (f : A → Enum B) : Enum B :=
  foldr (λ '(s, x) ys, scale_Enum s (f x) ++ ys) [::] xs.

#[global] Instance Enum_Discrete : Discrete Enum :=
  {|disc_ret := @ret_Enum
  ; disc_bind := @bind_Enum
  ; disc_flip := λ _, [:: (1, true); (1, false)]
  ; disc_score := λ r, [:: (r, tt)]
  |}.

Inductive InSupp {A} (x : A) : list A → Prop :=
| In_head : forall xs, InSupp x (x :: xs)
| In_tail : forall y xs, InSupp x xs → InSupp x (y :: xs).

Definition scale_bind : ∀ {A B} r (u : Enum A) (f : A → Enum B),
  scale_Enum r (bind_Enum u f) = bind_Enum u (λ x, scale_Enum r (f x)).
Proof. move=> A B r u f. elim: u => [//|[s a] us] IH //=.
rewrite !scale_app {}IH. congr app. rewrite !scale_scale.
congr scale_Enum. rewrite mulrC //.
Qed.



(** We need the decidable equality for the base type [A] of
    the enumeration. *)

Fixpoint acc_mass {A : eqType} (x : A) (μ : Enum A) : ℚ≥0 :=
  match μ with
  | [::] => 0
  | (p, y) :: μ' => if x == y
      then p + acc_mass x μ' else acc_mass x μ'
  end.

Lemma acc_nil : ∀ (A : eqType) (x : A), acc_mass x [::] = 0.
Proof. move=> //=. Qed.

Lemma acc_app {A : eqType} {x : A} {μ1 μ2 : Enum A}
  : acc_mass x (μ1 ++ μ2) = acc_mass x μ1 + acc_mass x μ2.
Proof. elim: μ1 => [//|[r a] μ1 IH]. apply: val_inj.
rewrite [RHS]add0q //=.
move=> //=. case: (x == a); move => //=. rewrite IH [LHS]addrA //.
Qed.

Definition EqEnum {A : eqType} (μ1 μ2 : Enum A) : Prop :=
  ∀ x : A, acc_mass x μ1 = acc_mass x μ2.

Infix "==Enum" := EqEnum (at level 70).



(*+ TODO: update till here +*)

Lemma enum_eq_eq {A : eqType} : ∀ {μ1 μ2 : Enum A},
  μ1 = μ2 → EqEnum μ1 μ2.
Proof. intros. unfold EqEnum. intros.
  rewrite H. reflexivity.
Qed.

Lemma enum_eq_refl : ∀ {A : eqType} {μ : Enum A},
  μ ==Enum μ.
Proof. intros. unfold EqEnum. intros. reflexivity. Qed.

Lemma enum_eq_sym {A : eqType} : ∀ {μ ν : Enum A},
  μ ==Enum ν → ν ==Enum μ.
Proof. intros. unfold EqEnum. intros. symmetry. apply H. Qed.

Lemma enum_eq_trans {A : eqType} : ∀ {x y z : Enum A},
  x ==Enum y → y ==Enum z → x ==Enum z.
Proof. intros. unfold EqEnum. intros. etransitivity; eauto. Qed.



#[global] Instance enum_eq_equiv {A : eqType}
  : @Equivalence (Enum A) EqEnum.
Proof. split. unfold Reflexive. intros. apply enum_eq_refl.
  unfold Symmetric. intros. now apply enum_eq_sym.
  unfold Transitive. intros. now eapply enum_eq_trans.
Qed.

Add Parametric Morphism {A : eqType} : (@app (ℚ≥0 * A))
  with signature EqEnum ==> EqEnum ==> EqEnum
  as app_proper.
Proof. intros. intros a. repeat rewrite acc_app.
  rewrite H. rewrite H0. reflexivity.
Qed.



Lemma app_comm {A : eqType} (u v : Enum A) : u ++ v ==Enum v ++ u.
Proof. unfold EqEnum. intros. induction u.
  simpl. now rewrite cats0. destruct a.
  repeat rewrite acc_app. apply: val_inj; move=> /=. rewrite addrC //.
Qed.

Lemma enum_nil_bind : ∀ A B (f : A → Enum B),
  bind_Enum [:: ] f = [:: ].
Proof. intros. simpl. reflexivity. Qed.

Lemma enum_cons_bind : ∀ A B x r (u : Enum A) (f : A → Enum B),
  bind_Enum ((r, x) :: u) f = scale_Enum r (f x) ++ bind_Enum u f.
Proof. intros. simpl. reflexivity. Qed.

Lemma enum_bind_nil : ∀ A B (u : Enum A),
  bind_Enum u (λ _, [::] : Enum B) = [::].
Proof.
  intros. simpl. induction u.
  now simpl. destruct a. rewrite enum_cons_bind.
  now simpl.
Qed.

Lemma enum_bind_app : ∀ A {B : eqType} (u : Enum A) (f g : A → Enum B),
  bind_Enum u (λ x, (f x) ++ (g x))
    ==Enum
  bind_Enum u (λ x, f x) ++ bind_Enum u (λ x, g x).
Proof. intros. induction u. now simpl.
  destruct a. repeat rewrite enum_cons_bind.
  rewrite scale_app. rewrite IHu. repeat rewrite <- catA.
  rewrite (catA (bind_Enum u (λ x : A, f x))).
  rewrite (app_comm (bind_Enum u (λ x : A, f x)) (scale_Enum n (g a))).
  repeat rewrite <- catA. reflexivity.
Qed.

Lemma enum_comm_nil : ∀ A B C (v : Enum B) (f : A → B → Enum C),
  bind_Enum [::] (λ x, bind_Enum v (λ y, f x y)) =
  bind_Enum v (λ y, bind_Enum [::] (λ x, f x y)).
Proof.
  intros A B C v f.
  rewrite enum_bind_nil. simpl. reflexivity.
Qed.

Lemma enum_comm_cons : ∀
  {A : eqType} {B : eqType} {C : eqType} r a
  (u : Enum A) (v : Enum B) (f : A → B → Enum C),
    bind_Enum ((r, a) :: u) (λ x, bind_Enum v (λ y, f x y))
      ==Enum
    bind_Enum v (λ y, bind_Enum ((r, a) :: u) (λ x, f x y)).
Proof.
  intros. rewrite enum_cons_bind. simpl.
  induction v.
  - simpl. rewrite enum_bind_nil. now apply enum_eq_eq.
  - destruct a0. simpl. repeat rewrite scale_app.
    repeat rewrite enum_bind_app.
    repeat rewrite <- catA.
    rewrite (catA (scale_Enum r (bind_Enum v (λ y : B, f a y)))).
    rewrite (app_comm (scale_Enum r (bind_Enum v (λ y : B, f a y)))).
    rewrite <- catA.
    rewrite IHv. repeat rewrite scale_scale.
    rewrite scale_bind. rewrite enum_bind_app.
    apply enum_eq_eq. congr app. congr scale_Enum.
    apply: val_inj; move=> /=. rewrite mulrC //.
Qed.

Theorem enum_Fubini_Tonelli : ∀
  {A : eqType} {B : eqType} {C : eqType}
  (u : Enum A) (v : Enum B) (f : A → B → Enum C),
    bind_Enum u (λ x, bind_Enum v (λ y, f x y))
      ==Enum
    bind_Enum v (λ y, bind_Enum u (λ x, f x y)).
Proof. destruct u.
  - intros. apply enum_eq_eq. apply enum_comm_nil.
  - intros. destruct p. now eapply enum_comm_cons.
Qed.

(** * the relation transformer for [Enum] *)

Definition enumRT {R1 : eqType} {R2 : eqType}
    (RR : R1 → R2 → Prop) : Enum R1 → Enum R2 → Prop
  := λ μx μy, ∀ x y, RR x y → acc_mass x μx = acc_mass y μy.

Infix "==EnumRT" := (enumRT _) (at level 70).

#[global] Program Instance Enum_DiscreteInterface
    : DiscreteInterface Enum :=
  {|disc_rep := Enum_Discrete
  ; disc_eq := @EqEnum
  ; disc_RT := @enumRT
  ; disc_mass := @acc_mass
  |}.
Next Obligation.
  split. intros. unfold enumRT. intros x ? <-.
  rewrite H. reflexivity.
  intros. intro a. apply H. reflexivity.
Qed.
Next Obligation.
  intros m1 m2 Hm.
  unfold enumRT in Hm.
  apply Hm. reflexivity.
Qed.



(** Convenient Distribution Constructors *)
Section Dists.

Definition dirac {A} (x : A) : Enum A :=
  ret_Enum x.

#[program] Definition one_div_two := [nn 1/2].
#[program] Definition one_div_three := [nn 1/3].

Definition unif2 {A} (x y : A) : Enum A :=
  [:: (one_div_two, x); (one_div_two, y)].

Definition unif3 {A} (x y z : A) : Enum A :=
  [:: (one_div_three, x); (one_div_three, y); (one_div_three, z)].

End Dists.



Section successor.
Context {X : eqType}.

Definition EnumSucc {Y} (μ : Enum X) (k : X → Y) : Enum Y :=
  map (λ '(p, x), (p, k x)) μ.



(* Definition EnumSubSucc {μ : Enum X} (k : X → Y) *)

End successor.

End Enum.
