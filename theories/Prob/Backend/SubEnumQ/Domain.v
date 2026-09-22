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
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeDomain.
Variable R : realType.

Lemma enumQ_real_expect_test_scale {A} (mu : EnumQ A) (f : A -> R) p :
  enumQ_real_expect (fun x => p * f x) mu = p * enumQ_real_expect f mu.
Proof.
  elim: mu=> [|[q x] tl IH]; cbn [enumQ_real_expect]; first by rewrite mulr0.
  rewrite IH mulrDr; congr (_ + _); exact: mulrCA.
Qed.

Lemma enumQ_real_expect_test_add {A} (mu : EnumQ A) (f g : A -> R) :
  enumQ_real_expect (fun x => f x + g x) mu =
    enumQ_real_expect f mu + enumQ_real_expect g mu.
Proof.
  elim: mu=> [|[q x] tl IH]; cbn [enumQ_real_expect]; first by rewrite addr0.
  rewrite IH mulrDr. exact: addrACA.
Qed.

Definition subenumQ_domain_laws {A} (mu : SubEnumQ A) :
  OmegaValLaws (fun f : A -> R => enumQ_real_expect f (subenumQ_raw mu)).
Proof.
  constructor.
  - exact: enumQ_real_expect_zero.
  - intros f g Hf Hg Hfg; exact: enumQ_real_expect_mono.
  - intros p f Hp Hp1 Hf; exact: enumQ_real_expect_test_scale.
  - intros f g Hf Hg Hfg; exact: enumQ_real_expect_test_add.
  - apply subenumQ_real_expect_bound=> x; exact: lexx.
  - intros f Hf Hi; exact (enumQ_real_expect_countable (subenumQ_raw mu) Hf Hi).
Defined.

Definition subenumQ_domain {A} (mu : SubEnumQ A) : OmegaVal R A :=
  {| oval_eval := fun f => enumQ_real_expect f (subenumQ_raw mu);
     oval_laws := subenumQ_domain_laws mu |}.

Theorem subenumQ_domain_ret {A} (x : A) :
  oval_eq (subenumQ_domain (subenumQ_ret x)) (oval_ret R x).
Proof. intros f Hf; by rewrite /= rmorph1 mul1r addr0. Qed.
Theorem subenumQ_domain_zero {A} :
  oval_eq (subenumQ_domain (@subenumQ_zero A)) (oval_bottom R).
Proof. intros f Hf; reflexivity. Qed.
Theorem subenumQ_domain_bind {A B} (mu : SubEnumQ A) (k : A -> SubEnumQ B) :
  oval_eq (subenumQ_domain (subenumQ_bind mu k))
    (oval_bind (subenumQ_domain mu) (fun x => subenumQ_domain (k x))).
Proof. intros f Hf; exact: enumQ_real_expect_bind. Qed.

(** This is test-inequality soundness, NOT an asserted joint-coupling
    realization theorem in the external measure model. *)
Theorem subenumQ_sem_lift_test_sound {A B} (S : A -> B -> Prop)
    (mu : SubEnumQ A) (nu : SubEnumQ B) (f : A -> R) (g : B -> R) :
  sem_lift S mu nu -> (forall x y, S x y -> f x <= g y) ->
  oval_eval (subenumQ_domain mu) f <= oval_eval (subenumQ_domain nu) g.
Proof. exact: subenumQ_lift_real_expect. Qed.

Theorem subenumQ_sem_eq_sound {A} (mu nu : SubEnumQ A) :
  sem_eq mu nu -> oval_eq (subenumQ_domain mu) (subenumQ_domain nu).
Proof.
  intros H f Hf; apply/eqP; rewrite eq_le; apply/andP; split.
  - eapply subenumQ_sem_lift_test_sound; [exact H|]. intros x y ->; exact: lexx.
  - eapply subenumQ_sem_lift_test_sound; [exact (sem_eq_sym H)|].
    intros x y ->; exact: lexx.
Qed.
End NativeDomain.
