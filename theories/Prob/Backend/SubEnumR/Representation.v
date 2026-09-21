(** Finite real-weight subdistributions. The carrier itself enforces
    nonnegative weights and total mass at most one. No external domain or
    free completion occurs in the native representation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section FiniteReal.
Variable R : realType.
Fixpoint real_enum_expect {A} (f : A -> R) (mu : list (R * A)) : R :=
  match mu with [] => 0 | (p,x)::tl => p * f x + real_enum_expect f tl end.
Definition real_enum_nonnegative {A} (mu : list (R * A)) :=
  forall p x, List.In (p,x) mu -> 0 <= p.

Lemma real_enum_expect_ext {A} (mu : list (R * A)) f g :
  (forall x, f x = g x) -> real_enum_expect f mu = real_enum_expect g mu.
Proof. intro H; induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite H IH]. Qed.
Lemma real_enum_expect_zero {A} (mu : list (R * A)) : real_enum_expect (fun _ => 0) mu = 0.
Proof. induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite mulr0 IH addr0]. Qed.
Lemma real_enum_expect_add {A} (mu : list (R * A)) f g :
  real_enum_expect (fun x => f x + g x) mu = real_enum_expect f mu + real_enum_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; [by rewrite addr0|].
  rewrite mulrDr IH; exact: addrACA.
Qed.
Lemma real_enum_expect_scale {A} (mu : list (R * A)) p f :
  real_enum_expect (fun x => p * f x) mu = p * real_enum_expect f mu.
Proof.
  induction mu as [|[q x] tl IH]; cbn; [by rewrite mulr0|].
  rewrite IH mulrDr; congr (_ + _); exact: mulrCA.
Qed.
Lemma real_enum_expect_mono {A} (mu : list (R * A)) f g :
  real_enum_nonnegative mu -> (forall x, f x <= g x) ->
  real_enum_expect f mu <= real_enum_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; intros H Hfg; first exact: lexx.
  apply lerD.
  - apply ler_wpM2l; [exact (H p x (or_introl (Logic.eq_refl _)))|exact (Hfg x)].
  - apply IH; [intros q y Hy; exact (H q y (or_intror Hy))|exact Hfg].
Qed.
Lemma real_enum_expect_nonnegative {A} (mu : list (R * A)) f :
  real_enum_nonnegative mu -> (forall x, 0 <= f x) -> 0 <= real_enum_expect f mu.
Proof.
  intros H Hf; rewrite -(real_enum_expect_zero mu); exact: real_enum_expect_mono.
Qed.
Lemma real_enum_expect_ae_mono {A} (mu : list (R * A)) f g :
  real_enum_nonnegative mu ->
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x <= g x) ->
  real_enum_expect f mu <= real_enum_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; intros Hnn H; cbn; first exact: lexx.
  have Htail : real_enum_expect f tl <= real_enum_expect g tl.
  { apply IH; [intros q y Hy; exact (Hnn q y (or_intror Hy))|].
    intros q y Hy Hq; exact (H q y (or_intror Hy) Hq). }
  destruct (eqVneq p 0) as [->|Hp]; first by rewrite !mul0r !add0r.
  apply lerD; last exact Htail.
  apply ler_wpM2l; first exact (Hnn p x (or_introl (Logic.eq_refl _))).
  apply (H p x (or_introl (Logic.eq_refl _))).
  move=> Hz; move/eqP: Hp; exact.
Qed.
Lemma real_enum_expect_app {A} (mu nu : list (R * A)) f :
  real_enum_expect f (mu ++ nu) = real_enum_expect f mu + real_enum_expect f nu.
Proof. induction mu as [|[p x] tl IH]; cbn; [by rewrite add0r|by rewrite IH addrA]. Qed.
Lemma real_enum_expect_weight_map {A} (mu : list (R * A)) p f :
  real_enum_expect f (List.map (fun qx => (p * fst qx, snd qx)) mu) = p * real_enum_expect f mu.
Proof.
  induction mu as [|[q x] tl IH]; cbn; [by rewrite mulr0|].
  by rewrite IH mulrDr mulrA.
Qed.

Record SubEnumR (A : Type) := {
  subenumR_raw : list (R * A);
  subenumR_nonnegative : real_enum_nonnegative subenumR_raw;
  subenumR_mass_bound : real_enum_expect (fun _ => 1) subenumR_raw <= 1
}.
Arguments subenumR_raw {A} _.
Arguments subenumR_nonnegative {A} _.
Arguments subenumR_mass_bound {A} _.

Definition subenumR_expect {A} (mu : SubEnumR A) f := real_enum_expect f (subenumR_raw mu).
Definition subenumR_ret {A} (x : A) : SubEnumR A.
Proof.
  refine (@Build_SubEnumR A [(1,x)] _ _).
  - intros p y [H|[]]; inversion H; exact: ler01.
  - cbn; by rewrite mulr1 addr0.
Defined.
Definition subenumR_zero {A} : SubEnumR A.
Proof. refine (@Build_SubEnumR A [] _ _); [intros p x []|exact: ler01]. Defined.

Definition subenumR_coin (p : R) (Hp : 0 <= p) (Hp1 : p <= 1) : SubEnumR bool.
Proof.
  refine (@Build_SubEnumR bool [(p,true); (1-p,false)] _ _).
  - intros q b [H|[H|[]]]; inversion H; subst; [exact Hp|by rewrite subr_ge0].
  - cbn; by rewrite !mulr1 addr0 addrC subrK.
Defined.

Definition real_enum_bind {A B} (mu : list (R * A)) (k : A -> SubEnumR B) : list (R * B) :=
  List.flat_map (fun px => List.map (fun qy => (fst px * fst qy, snd qy))
    (subenumR_raw (k (snd px)))) mu.

Lemma real_enum_expect_bind {A B} (mu : list (R * A)) (k : A -> SubEnumR B) f :
  real_enum_expect f (real_enum_bind mu k) =
  real_enum_expect (fun x => subenumR_expect (k x) f) mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn [real_enum_bind List.flat_map]; first reflexivity.
  rewrite real_enum_expect_app real_enum_expect_weight_map IH; reflexivity.
Qed.

Definition subenumR_bind {A B} (mu : SubEnumR A) (k : A -> SubEnumR B) : SubEnumR B.
Proof.
  refine (@Build_SubEnumR B (real_enum_bind (subenumR_raw mu) k) _ _).
  - intros p y Hin; apply List.in_flat_map in Hin.
    destruct Hin as [[q x] [Hq Hin]]; apply List.in_map_iff in Hin.
    destruct Hin as [[r z] [He Hr]]; cbn in He; inversion He; subst.
    apply mulr_ge0; [exact (subenumR_nonnegative mu q x Hq)|exact (subenumR_nonnegative (k x) r y Hr)].
  - rewrite real_enum_expect_bind.
    apply: le_trans (_ : real_enum_expect (fun _ => 1) (subenumR_raw mu) <= 1).
    + apply real_enum_expect_mono; [exact (subenumR_nonnegative mu)|].
      intro x; exact (subenumR_mass_bound (k x)).
    + exact (subenumR_mass_bound mu).
Defined.

Definition subenumR_eq {A} (mu nu : SubEnumR A) :=
  forall f, subenumR_expect mu f = subenumR_expect nu f.
Definition subenumR_ae {A} (mu : SubEnumR A) (P : A -> Prop) :=
  forall p x, List.In (p,x) (subenumR_raw mu) -> p <> 0 -> P x.
Definition subenumR_lift {A B} (S : A -> B -> Prop) (mu : SubEnumR A) (nu : SubEnumR B) :=
  exists j : SubEnumR (A * B),
    (forall f, subenumR_expect j (fun xy => f (fst xy)) = subenumR_expect mu f) /\
    (forall g, subenumR_expect j (fun xy => g (snd xy)) = subenumR_expect nu g) /\
    subenumR_ae j (fun xy => S (fst xy) (snd xy)).

Lemma subenumR_expect_bind {A B} (mu : SubEnumR A) (k : A -> SubEnumR B) f :
  subenumR_expect (subenumR_bind mu k) f = subenumR_expect mu (fun x => subenumR_expect (k x) f).
Proof. exact: real_enum_expect_bind. Qed.

Lemma subenumR_bind_ret_l {A B} (x : A) (k : A -> SubEnumR B) :
  subenumR_eq (subenumR_bind (subenumR_ret x) k) (k x).
Proof. intro f; rewrite subenumR_expect_bind /subenumR_expect /=; by rewrite mul1r addr0. Qed.
Lemma subenumR_bind_ret_r {A} (mu : SubEnumR A) :
  subenumR_eq (subenumR_bind mu (fun x => subenumR_ret x)) mu.
Proof.
  intro f; rewrite subenumR_expect_bind /subenumR_expect.
  apply real_enum_expect_ext=> x; by rewrite /subenumR_expect /= mul1r addr0.
Qed.
Lemma subenumR_bind_assoc {A B C} (mu : SubEnumR A) (k : A -> SubEnumR B) (h : B -> SubEnumR C) :
  subenumR_eq (subenumR_bind (subenumR_bind mu k) h)
    (subenumR_bind mu (fun x => subenumR_bind (k x) h)).
Proof.
  intro f; rewrite !subenumR_expect_bind.
  apply real_enum_expect_ext=> x; symmetry; exact: subenumR_expect_bind.
Qed.
End FiniteReal.
