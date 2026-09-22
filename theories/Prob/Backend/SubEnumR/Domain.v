(** One-way finite-real expectation model. Native arithmetic stays independent
    of this file; FreeOmega validation reuses the generic native bridge. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable.
From PTree.Prob.Backend.SubEnumR Require Import Representation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section RealDomain.
Variable R : realType.

Lemma real_enum_expect_continuous {A} (mu : list (R * A)) (f : nat -> A -> R) :
  real_enum_nonnegative mu -> (forall n, oval_test (f n)) ->
  (forall n x, f n x <= f (S n) x) ->
  real_enum_expect (oval_pointwise_sup f) mu = oval_sup (fun n => real_enum_expect (f n) mu).
Proof.
  intros Hnn Hf Hi; induction mu as [|[p x] tl IH];
    rewrite ?real_enum_expect_cons ?real_enum_expect_nil.
  - symmetry; exact: oval_sup_const.
  - have Hp : 0 <= p := Hnn p x (or_introl (Logic.eq_refl _)).
    have Htl : real_enum_nonnegative tl := fun q y Hy => Hnn q y (or_intror Hy).
    rewrite (IH Htl); unfold oval_pointwise_sup.
    rewrite -(oval_sup_scale (b := 1) Hp (fun n => proj2 (Hf n x))).
    symmetry; apply oval_sup_add with (bc := p) (bd := real_enum_expect (fun _ => 1) tl).
    + intro n; exact (ler_wpM2l Hp (Hi n x)).
    + intro n; apply real_enum_expect_mono; [exact Htl|exact (Hi n)].
    + intro n; apply: le_trans (ler_wpM2l Hp (proj2 (Hf n x))) _; by rewrite mulr1.
    + intro n; apply real_enum_expect_mono; [exact Htl|intro y; exact (proj2 (Hf n y))].
Qed.

Definition subenumR_domain_laws {A} (mu : SubEnumR R A) : OmegaValLaws (subenumR_expect mu).
Proof.
  constructor.
  - exact: real_enum_expect_zero.
  - intros f g Hf Hg Hfg; apply real_enum_expect_mono; [exact (@subenumR_nonnegative R A mu)|exact Hfg].
  - intros p f Hp Hp1 Hf; exact: real_enum_expect_scale.
  - intros f g Hf Hg Hfg; exact: real_enum_expect_add.
  - exact (@subenumR_mass_bound R A mu).
  - intros f Hf Hi; apply real_enum_expect_continuous; [exact (@subenumR_nonnegative R A mu)|exact Hf|exact Hi].
Defined.
Definition subenumR_domain {A} (mu : SubEnumR R A) : OmegaVal R A :=
  {| oval_eval := subenumR_expect mu; oval_laws := subenumR_domain_laws mu |}.

Theorem subenumR_domain_ret {A} (x : A) :
  oval_eq (subenumR_domain (subenumR_ret R x)) (oval_ret R x).
Proof. intros f Hf; by rewrite /= /subenumR_expect /= mul1r addr0. Qed.
Theorem subenumR_domain_zero {A} :
  oval_eq (subenumR_domain (@subenumR_zero R A)) (oval_bottom R).
Proof. intros f Hf; reflexivity. Qed.
Theorem subenumR_domain_bind {A B} (mu : SubEnumR R A) (k : A -> SubEnumR R B) :
  oval_eq (subenumR_domain (subenumR_bind mu k))
    (oval_bind (subenumR_domain mu) (fun x => subenumR_domain (k x))).
Proof. intros f Hf; exact: subenumR_expect_bind. Qed.

Lemma real_enum_expect_support_ext {A} (mu : list (R * A)) (f g : A -> R) :
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x = g x) ->
  real_enum_expect f mu = real_enum_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; intros H;
    rewrite ?real_enum_expect_cons ?real_enum_expect_nil; first reflexivity.
  have He : real_enum_expect f tl = real_enum_expect g tl.
  { apply IH; intros q y Hy Hq; exact (H q y (or_intror Hy) Hq). }
  rewrite He; destruct (eqVneq p 0) as [->|Hp]; first by rewrite !mul0r.
  have Hnz : p <> 0 by move=> Hz; move/eqP: Hp; exact.
  by rewrite (H p x (or_introl (Logic.eq_refl _)) Hnz).
Qed.

Theorem subenumR_domain_ae {A} (mu : SubEnumR R A) P :
  subenumR_ae mu P -> oval_ae (subenumR_domain mu) P.
Proof.
  intros H f g Hf Hg Hfg; apply real_enum_expect_support_ext.
  intros p x Hin Hnz; exact (Hfg x (H p x Hin Hnz)).
Qed.
Theorem subenumR_domain_eq {A} (mu nu : SubEnumR R A) :
  subenumR_eq mu nu -> oval_eq (subenumR_domain mu) (subenumR_domain nu).
Proof. intros H f Hf; exact (H f). Qed.

Theorem subenumR_domain_lift {A B} (S : A -> B -> Prop) (mu : SubEnumR R A) (nu : SubEnumR R B) f g :
  subenumR_lift S mu nu -> (forall x y, S x y -> f x <= g y) ->
  oval_eval (subenumR_domain mu) f <= oval_eval (subenumR_domain nu) g.
Proof.
  intros [j [Hl [Hr Hj]]] Hfg; change (subenumR_expect mu f <= subenumR_expect nu g).
  rewrite -(Hl f) -(Hr g); apply real_enum_expect_ae_mono.
  - exact (@subenumR_nonnegative R (A*B) j).
  - intros p [x y] Hin Hnz; exact (Hfg x y (Hj p (x,y) Hin Hnz)).
Qed.
End RealDomain.
