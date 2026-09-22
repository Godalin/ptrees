(** Shared finite nonnegative weightings over ordinary ordered scalars.
    The sign invariant belongs to the container, not to a scalar subtype.
    There is deliberately no probability-mass bound or semantic interface here.
    Duplicate values and zero-weight entries are retained by the operations. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section FiniteWeighting.
Variable R : numDomainType.

Fixpoint finite_expect {A : Type} (f : A -> R) (mu : list (R * A)) : R :=
  match mu with [] => 0 | (p,x)::tl => p * f x + finite_expect f tl end.

Definition finite_nonnegative {A : Type} (mu : list (R * A)) : Prop :=
  forall p x, List.In (p,x) mu -> 0 <= p.

Definition finite_weight_map {A : Type} (p : R) (mu : list (R * A)) :=
  List.map (fun qx => (p * fst qx, snd qx)) mu.

Definition finite_bind {A B : Type}
    (mu : list (R * A)) (k : A -> list (R * B)) :=
  List.flat_map (fun px => finite_weight_map (fst px) (k (snd px))) mu.

Lemma finite_expect_ext {A} (mu : list (R * A)) f g :
  (forall x, f x = g x) -> finite_expect f mu = finite_expect g mu.
Proof. intro H; induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite H IH]. Qed.

Lemma finite_expect_zero {A} (mu : list (R * A)) :
  finite_expect (fun _ => 0) mu = 0.
Proof. induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite mulr0 IH addr0]. Qed.

Lemma finite_expect_add {A} (mu : list (R * A)) f g :
  finite_expect (fun x => f x + g x) mu = finite_expect f mu + finite_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn; [by rewrite addr0|].
  rewrite mulrDr IH; exact: addrACA.
Qed.

Lemma finite_expect_scale {A} (mu : list (R * A)) p f :
  finite_expect (fun x => p * f x) mu = p * finite_expect f mu.
Proof.
  induction mu as [|[q x] tl IH]; cbn; [by rewrite mulr0|].
  rewrite IH mulrDr; congr (_ + _); exact: mulrCA.
Qed.

Lemma finite_expect_app {A} (mu nu : list (R * A)) f :
  finite_expect f (mu ++ nu) = finite_expect f mu + finite_expect f nu.
Proof. induction mu as [|[p x] tl IH]; cbn; [by rewrite add0r|by rewrite IH addrA]. Qed.

Lemma finite_expect_weight_map {A} (mu : list (R * A)) p f :
  finite_expect f (finite_weight_map p mu) = p * finite_expect f mu.
Proof.
  induction mu as [|[q x] tl IH]; cbn; [by rewrite mulr0|].
  by rewrite IH mulrDr mulrA.
Qed.

Lemma finite_expect_map {A B} (mu : list (R * A)) (h : A -> B) f :
  finite_expect f (List.map (fun px => (fst px, h (snd px))) mu) =
  finite_expect (fun x => f (h x)) mu.
Proof. induction mu as [|[p x] tl IH]; cbn; [reflexivity|by rewrite IH]. Qed.

Lemma finite_expect_bind {A B} (mu : list (R * A)) (k : A -> list (R * B)) f :
  finite_expect f (finite_bind mu k) = finite_expect (fun x => finite_expect f (k x)) mu.
Proof.
  induction mu as [|[p x] tl IH]; cbn [finite_bind List.flat_map]; first reflexivity.
  rewrite finite_expect_app finite_expect_weight_map IH; reflexivity.
Qed.

Lemma finite_expect_ae_mono {A} (mu : list (R * A)) f g :
  finite_nonnegative mu ->
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x <= g x) ->
  finite_expect f mu <= finite_expect g mu.
Proof.
  induction mu as [|[p x] tl IH]; intros Hnn H; cbn; first exact: lexx.
  have Htail : finite_expect f tl <= finite_expect g tl.
  { apply IH; [intros q y Hy; exact (Hnn q y (or_intror Hy))|].
    intros q y Hy Hq; exact (H q y (or_intror Hy) Hq). }
  destruct (eqVneq p 0) as [->|Hp]; first by rewrite !mul0r !add0r.
  apply lerD; last exact Htail.
  apply ler_wpM2l; first exact (Hnn p x (or_introl (Logic.eq_refl _))).
  apply (H p x (or_introl (Logic.eq_refl _))).
  move=> Hz; move/eqP: Hp; exact.
Qed.

Lemma finite_expect_mono {A} (mu : list (R * A)) f g :
  finite_nonnegative mu -> (forall x, f x <= g x) ->
  finite_expect f mu <= finite_expect g mu.
Proof. intros H Hfg; apply finite_expect_ae_mono; [exact H|intros; apply Hfg]. Qed.

Lemma finite_expect_nonnegative {A} (mu : list (R * A)) f :
  finite_nonnegative mu -> (forall x, 0 <= f x) -> 0 <= finite_expect f mu.
Proof. intros H Hf; rewrite -(finite_expect_zero mu); exact: finite_expect_mono. Qed.

Lemma finite_expect_ae_ext {A} (mu : list (R * A)) f g :
  finite_nonnegative mu ->
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x = g x) ->
  finite_expect f mu = finite_expect g mu.
Proof.
  intros Hnn H; apply/eqP; rewrite eq_le; apply/andP; split;
    apply finite_expect_ae_mono; try exact Hnn;
    intros p x Hin Hnz; by rewrite (H p x Hin Hnz).
Qed.

Record FiniteEnum (A : Type) := {
  finite_enum_raw : list (R * A);
  finite_enum_nonnegative : finite_nonnegative finite_enum_raw
}.
Arguments finite_enum_raw {A} _.
Arguments finite_enum_nonnegative {A} _.

Definition finite_enum_of_list {A} mu (Hnn : @finite_nonnegative A mu) : FiniteEnum A :=
  @Build_FiniteEnum A mu Hnn.

Definition finite_enum_expect {A} (mu : FiniteEnum A) f :=
  finite_expect f (finite_enum_raw mu).
Definition finite_mass {A} (mu : FiniteEnum A) := finite_enum_expect mu (fun _ => 1).

Definition finite_enum_ret {A} (x : A) : FiniteEnum A.
Proof.
  refine (@finite_enum_of_list A [(1,x)] _).
  intros p y [H|[]]; inversion H; exact: ler01.
Defined.

Definition finite_enum_zero {A} : FiniteEnum A.
Proof. refine (@finite_enum_of_list A [] _); intros p x []. Defined.

Definition finite_enum_scale {A} (p : R) (Hp : 0 <= p) (mu : FiniteEnum A) : FiniteEnum A.
Proof.
  refine (@finite_enum_of_list A (finite_weight_map p (finite_enum_raw mu)) _).
  intros q y Hin; apply List.in_map_iff in Hin.
  destruct Hin as [[r x] [He Hr]]; cbn in He; inversion He; subst.
  apply mulr_ge0; [exact Hp|exact (finite_enum_nonnegative mu r y Hr)].
Defined.

Definition finite_enum_map {A B} (h : A -> B) (mu : FiniteEnum A) : FiniteEnum B.
Proof.
  refine (@finite_enum_of_list B (List.map (fun px => (fst px, h (snd px))) (finite_enum_raw mu)) _).
  intros p y Hin; apply List.in_map_iff in Hin.
  destruct Hin as [[q x] [He Hq]]; cbn in He; inversion He; subst.
  exact (finite_enum_nonnegative mu p x Hq).
Defined.

Definition finite_enum_bind {A B} (mu : FiniteEnum A) (k : A -> FiniteEnum B) : FiniteEnum B.
Proof.
  refine (@finite_enum_of_list B (finite_bind (finite_enum_raw mu) (fun x => finite_enum_raw (k x))) _).
  intros p y Hin; apply List.in_flat_map in Hin.
  destruct Hin as [[q x] [Hq Hin]]; apply List.in_map_iff in Hin.
  destruct Hin as [[r z] [He Hr]]; cbn in He; inversion He; subst.
  apply mulr_ge0; [exact (finite_enum_nonnegative mu q x Hq)|exact (finite_enum_nonnegative (k x) r y Hr)].
Defined.

Lemma finite_enum_expect_ret {A} (x : A) f : finite_enum_expect (finite_enum_ret x) f = f x.
Proof. by rewrite /finite_enum_expect /= mul1r addr0. Qed.
Lemma finite_enum_expect_zero {A} f : finite_enum_expect (@finite_enum_zero A) f = 0.
Proof. reflexivity. Qed.
Lemma finite_enum_expect_scale {A} p (Hp : 0 <= p) (mu : FiniteEnum A) f :
  finite_enum_expect (finite_enum_scale Hp mu) f = p * finite_enum_expect mu f.
Proof. exact: finite_expect_weight_map. Qed.
Lemma finite_enum_expect_map {A B} (h : A -> B) (mu : FiniteEnum A) f :
  finite_enum_expect (finite_enum_map h mu) f = finite_enum_expect mu (fun x => f (h x)).
Proof. exact: finite_expect_map. Qed.
Lemma finite_enum_expect_bind {A B} (mu : FiniteEnum A) (k : A -> FiniteEnum B) f :
  finite_enum_expect (finite_enum_bind mu k) f = finite_enum_expect mu (fun x => finite_enum_expect (k x) f).
Proof. exact: finite_expect_bind. Qed.

Lemma finite_mass_ret {A} (x : A) : finite_mass (finite_enum_ret x) = 1.
Proof. exact: finite_enum_expect_ret. Qed.
Lemma finite_mass_zero {A} : finite_mass (@finite_enum_zero A) = 0.
Proof. reflexivity. Qed.
Lemma finite_mass_scale {A} p (Hp : 0 <= p) (mu : FiniteEnum A) :
  finite_mass (finite_enum_scale Hp mu) = p * finite_mass mu.
Proof. exact: finite_enum_expect_scale. Qed.
Lemma finite_mass_map {A B} (h : A -> B) (mu : FiniteEnum A) :
  finite_mass (finite_enum_map h mu) = finite_mass mu.
Proof. exact: finite_enum_expect_map. Qed.
Lemma finite_mass_bind {A B} (mu : FiniteEnum A) (k : A -> FiniteEnum B) :
  finite_mass (finite_enum_bind mu k) = finite_enum_expect mu (fun x => finite_mass (k x)).
Proof. exact: finite_enum_expect_bind. Qed.
Lemma finite_mass_nonnegative {A} (mu : FiniteEnum A) : 0 <= finite_mass mu.
Proof.
  apply finite_expect_nonnegative; [exact (finite_enum_nonnegative mu)|intro x; exact: ler01].
Qed.
End FiniteWeighting.

Arguments finite_enum_raw {R A} _.
Arguments finite_enum_nonnegative {R A} _ p x _.
