(** Shared finite subdistributions: a nonnegative weighting with mass <= 1.
    All invariants are in Prop. Smart constructors preserve them without
    imposing any invariant on the ordinary scalar type itself.
    This finite carrier is not an omega-completion or a SemanticMeasure instance. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section FiniteProbability.
Variable R : numDomainType.

Record FiniteSubdist (A : Type) := {
  finite_subdist_enum : FiniteEnum R A;
  finite_subdist_mass_bound : finite_mass finite_subdist_enum <= 1
}.
Arguments finite_subdist_enum {A} _.
Arguments finite_subdist_mass_bound {A} _.

Definition finite_subdist_of_list {A} mu
    (Hnn : @finite_nonnegative R A mu)
    (Hmass : finite_expect (λ _, 1) mu <= 1) : FiniteSubdist A :=
  @Build_FiniteSubdist A (finite_enum_of_list Hnn) Hmass.

(** A finite certificate, shared by rational and real backends. Checking
    never sorts, merges, prunes or normalizes entries. Abstract scalars may
    require a proof of the check rather than computation. *)
Definition finite_subdist_valid {A} (mu : list (R * A)) : bool :=
  List.forallb (λ px, 0 <= fst px) mu && (finite_expect (λ _, 1) mu <= 1).

Lemma finite_subdist_validP {A} (mu : list (R * A)) :
  reflect (finite_nonnegative mu ∧ finite_expect (λ _, 1) mu <= 1)
    (finite_subdist_valid mu).
Proof.
  apply: (iffP andP).
  - intros [Hnn Hmass]; split; last exact Hmass.
    move/forallb_forall: Hnn => Hnn.
    intros p x Hin. exact (Hnn (p,x) Hin).
  - intros [Hnn Hmass]; split; last exact Hmass.
    apply/forallb_forall. intros [p x] Hin. exact (Hnn p x Hin).
Qed.

Definition finite_subdist_checked {A} mu
    (Hvalid : @finite_subdist_valid A mu) : FiniteSubdist A :=
  let facts := elimT (finite_subdist_validP mu) Hvalid in
  finite_subdist_of_list (proj1 facts) (proj2 facts).

Lemma finite_subdist_checked_raw {A} mu (Hvalid : @finite_subdist_valid A mu) :
  finite_enum_raw (finite_subdist_enum (finite_subdist_checked Hvalid)) = mu.
Proof. reflexivity. Qed.

Definition finite_subdist_expect {A} (mu : FiniteSubdist A) f :=
  finite_enum_expect (finite_subdist_enum mu) f.

Lemma finite_subdist_checked_expect {A} mu
    (Hvalid : @finite_subdist_valid A mu) (f : A → R) :
  finite_subdist_expect (finite_subdist_checked Hvalid) f = finite_expect f mu.
Proof. reflexivity. Qed.

Definition finite_subdist_ret {A} (x : A) : FiniteSubdist A.
Proof.
  refine (@Build_FiniteSubdist A (finite_enum_ret R x) _).
  by rewrite finite_mass_ret.
Defined.
Definition finite_subdist_zero {A} : FiniteSubdist A.
Proof.
  refine (@Build_FiniteSubdist A (@finite_enum_zero R A) _).
  rewrite finite_mass_zero; exact: ler01.
Defined.

Definition finite_subdist_bind {A B} (mu : FiniteSubdist A)
    (k : A → FiniteSubdist B) : FiniteSubdist B.
Proof.
  refine (@Build_FiniteSubdist B
    (finite_enum_bind (finite_subdist_enum mu) (λ x, finite_subdist_enum (k x))) _).
  rewrite finite_mass_bind.
  apply: le_trans (finite_subdist_mass_bound mu).
  apply finite_expect_mono; first exact (finite_enum_nonnegative (finite_subdist_enum mu)).
  intro x; exact (finite_subdist_mass_bound (k x)).
Defined.

Definition finite_subdist_map {A B} (h : A → B) (mu : FiniteSubdist A) : FiniteSubdist B.
Proof.
  refine (@Build_FiniteSubdist B (finite_enum_map h (finite_subdist_enum mu)) _).
  rewrite finite_mass_map; exact (finite_subdist_mass_bound mu).
Defined.

Definition finite_subdist_scale {A} (p : R) (Hp : 0 <= p) (Hp1 : p <= 1)
    (mu : FiniteSubdist A) : FiniteSubdist A.
Proof.
  refine (@Build_FiniteSubdist A (finite_enum_scale Hp (finite_subdist_enum mu)) _).
  rewrite finite_mass_scale.
  apply: le_trans (_ : p * 1 <= 1); last by rewrite mulr1.
  apply ler_wpM2l; [exact Hp|exact (finite_subdist_mass_bound mu)].
Defined.

Lemma finite_subdist_expect_ret {A} (x : A) f :
  finite_subdist_expect (finite_subdist_ret x) f = f x.
Proof. exact: finite_enum_expect_ret. Qed.
Lemma finite_subdist_expect_zero {A} f :
  finite_subdist_expect (@finite_subdist_zero A) f = 0.
Proof. reflexivity. Qed.
Lemma finite_subdist_expect_bind {A B} (mu : FiniteSubdist A) (k : A → FiniteSubdist B) f :
  finite_subdist_expect (finite_subdist_bind mu k) f =
  finite_subdist_expect mu (λ x, finite_subdist_expect (k x) f).
Proof. exact: finite_enum_expect_bind. Qed.
Lemma finite_subdist_expect_map {A B} (h : A → B) (mu : FiniteSubdist A) f :
  finite_subdist_expect (finite_subdist_map h mu) f = finite_subdist_expect mu (λ x, f (h x)).
Proof. exact: finite_enum_expect_map. Qed.
Lemma finite_subdist_expect_scale {A} p (Hp : 0 <= p) (Hp1 : p <= 1) (mu : FiniteSubdist A) f :
  finite_subdist_expect (finite_subdist_scale Hp Hp1 mu) f = p * finite_subdist_expect mu f.
Proof. exact: finite_enum_expect_scale. Qed.

(** Laws are stated on expectations, not record equality: no proof irrelevance
    or quotient is needed to use the finite algebra. *)
Lemma finite_subdist_bind_ret_l {A B} (x : A) (k : A → FiniteSubdist B) f :
  finite_subdist_expect (finite_subdist_bind (finite_subdist_ret x) k) f =
  finite_subdist_expect (k x) f.
Proof. by rewrite finite_subdist_expect_bind finite_subdist_expect_ret. Qed.
Lemma finite_subdist_bind_ret_r {A} (mu : FiniteSubdist A) f :
  finite_subdist_expect (finite_subdist_bind mu (λ x, finite_subdist_ret x)) f =
  finite_subdist_expect mu f.
Proof.
  rewrite finite_subdist_expect_bind; apply finite_expect_ext=> x.
  exact: finite_subdist_expect_ret.
Qed.
Lemma finite_subdist_bind_assoc {A B C} (mu : FiniteSubdist A)
    (k : A → FiniteSubdist B) (h : B → FiniteSubdist C) f :
  finite_subdist_expect (finite_subdist_bind (finite_subdist_bind mu k) h) f =
  finite_subdist_expect (finite_subdist_bind mu (λ x, finite_subdist_bind (k x) h)) f.
Proof.
  rewrite !finite_subdist_expect_bind; apply finite_expect_ext=> x.
  symmetry; exact: finite_subdist_expect_bind.
Qed.
End FiniteProbability.

Arguments finite_subdist_enum {R A} _.
Arguments finite_subdist_mass_bound {R A} _.

(** Opt-in construction, not a global hint. Closed rational literals compute;
    otherwise expose only scalar inequalities, never list-membership goals.
    Failure to establish validity cannot silently change the distribution. *)
Ltac finite_distribution_build entries :=
  refine (@finite_subdist_checked _ _ entries _);
  first [solve [reflexivity] |
    unfold finite_subdist_valid;
    cbn [List.forallb fst finite_expect];
    repeat match goal with
    | |- is_true (andb _ _) => apply/andP; split
    end;
    rewrite ?mulr1 ?addr0;
    try solve [reflexivity | assumption]].

Tactic Notation "finite_distribution" uconstr(entries) :=
  finite_distribution_build entries.
