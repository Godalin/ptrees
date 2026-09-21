(** Role: One-way external validation of finite rational subdistributions.
    This adapter constructs OmegaVal laws from finite weighted expectation;
    the mainline probability/equational theory must not import it. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.Enum Require Import Representation.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  UpperExpectation UpperCoupling UpperContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeDomain.
Variable R : realType.

Lemma enum_real_expect_test_scale {A} (mu : Enum A) (f : A -> R) p :
  enum_real_expect (fun x => p * f x) mu = p * enum_real_expect f mu.
Proof.
  elim: mu=> [|[q x] tl IH]; cbn [enum_real_expect]; first by rewrite mulr0.
  rewrite IH mulrDr; congr (_ + _); exact: mulrCA.
Qed.

Lemma enum_real_expect_test_add {A} (mu : Enum A) (f g : A -> R) :
  enum_real_expect (fun x => f x + g x) mu =
    enum_real_expect f mu + enum_real_expect g mu.
Proof.
  elim: mu=> [|[q x] tl IH]; cbn [enum_real_expect]; first by rewrite addr0.
  rewrite IH mulrDr. exact: addrACA.
Qed.

Definition subenum_domain_laws {A} (mu : SubEnum A) :
  OmegaValLaws (fun f : A -> R => enum_real_expect f (subenum_raw mu)).
Proof.
  constructor.
  - exact: enum_real_expect_zero.
  - intros f g Hf Hg Hfg; exact: enum_real_expect_mono.
  - intros p f Hp Hp1 Hf; exact: enum_real_expect_test_scale.
  - intros f g Hf Hg Hfg; exact: enum_real_expect_test_add.
  - apply subenum_real_expect_bound=> x; exact: lexx.
  - intros f Hf Hi; exact (enum_real_expect_countable (subenum_raw mu) Hf Hi).
Defined.

Definition subenum_domain {A} (mu : SubEnum A) : OmegaVal R A :=
  {| oval_eval := fun f => enum_real_expect f (subenum_raw mu);
     oval_laws := subenum_domain_laws mu |}.

Theorem subenum_domain_ret {A} (x : A) :
  oval_eq (subenum_domain (subenum_ret x)) (oval_ret R x).
Proof. intros f Hf; by rewrite /= rmorph1 mul1r addr0. Qed.
Theorem subenum_domain_zero {A} :
  oval_eq (subenum_domain (@subenum_zero A)) (oval_bottom R).
Proof. intros f Hf; reflexivity. Qed.
Theorem subenum_domain_bind {A B} (mu : SubEnum A) (k : A -> SubEnum B) :
  oval_eq (subenum_domain (subenum_bind mu k))
    (oval_bind (subenum_domain mu) (fun x => subenum_domain (k x))).
Proof. intros f Hf; exact: enum_real_expect_bind. Qed.

(** This is test-inequality soundness, NOT an asserted joint-coupling
    realization theorem in the external measure model. *)
Theorem subenum_sem_lift_test_sound {A B} (S : A -> B -> Prop)
    (mu : SubEnum A) (nu : SubEnum B) (f : A -> R) (g : B -> R) :
  sem_lift S mu nu -> (forall x y, S x y -> f x <= g y) ->
  oval_eval (subenum_domain mu) f <= oval_eval (subenum_domain nu) g.
Proof. exact: subenum_lift_real_expect. Qed.

Theorem subenum_sem_eq_sound {A} (mu nu : SubEnum A) :
  sem_eq mu nu -> oval_eq (subenum_domain mu) (subenum_domain nu).
Proof.
  intros H f Hf; apply/eqP; rewrite eq_le; apply/andP; split.
  - eapply subenum_sem_lift_test_sound; [exact H|]. intros x y ->; exact: lexx.
  - eapply subenum_sem_lift_test_sound; [exact (sem_eq_sym H)|].
    intros x y ->; exact: lexx.
Qed.
End NativeDomain.
