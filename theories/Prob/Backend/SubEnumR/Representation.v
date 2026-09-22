(** Finite real-weight subdistributions, specialized from the shared
    FiniteSubdist representation. Sign proofs belong to its FiniteEnum
    component; there is no separate native record or scalar subtype.
    Native equality/AE/joint lifting remain backend-owned concepts. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section FiniteReal.
Variable R : realType.

(** Native-facing specializations: all finite-list algebra is proved in
    Common. These names retain the established backend theorem signatures. *)
Definition real_enum_expect {A} (f : A -> R) (mu : list (R * A)) : R :=
  finite_expect f mu.
Definition real_enum_nonnegative {A} (mu : list (R * A)) :=
  finite_nonnegative mu.

(** Computation equations keep clients independent of the shared Fixpoint's
    implementation name; they are definitional, not a second recursion. *)
Lemma real_enum_expect_nil {A} (f : A -> R) : real_enum_expect f [] = 0.
Proof. reflexivity. Qed.
Lemma real_enum_expect_cons {A} (f : A -> R) p x tl :
  real_enum_expect f ((p,x)::tl) = p * f x + real_enum_expect f tl.
Proof. reflexivity. Qed.

Lemma real_enum_expect_ext {A} (mu : list (R * A)) f g :
  (forall x, f x = g x) -> real_enum_expect f mu = real_enum_expect g mu.
Proof. exact: finite_expect_ext. Qed.
Lemma real_enum_expect_zero {A} (mu : list (R * A)) : real_enum_expect (fun _ => 0) mu = 0.
Proof. exact: finite_expect_zero. Qed.
Lemma real_enum_expect_add {A} (mu : list (R * A)) f g :
  real_enum_expect (fun x => f x + g x) mu = real_enum_expect f mu + real_enum_expect g mu.
Proof. exact: finite_expect_add. Qed.
Lemma real_enum_expect_scale {A} (mu : list (R * A)) p f :
  real_enum_expect (fun x => p * f x) mu = p * real_enum_expect f mu.
Proof. exact: finite_expect_scale. Qed.
Lemma real_enum_expect_mono {A} (mu : list (R * A)) f g :
  real_enum_nonnegative mu -> (forall x, f x <= g x) ->
  real_enum_expect f mu <= real_enum_expect g mu.
Proof. exact: finite_expect_mono. Qed.
Lemma real_enum_expect_nonnegative {A} (mu : list (R * A)) f :
  real_enum_nonnegative mu -> (forall x, 0 <= f x) -> 0 <= real_enum_expect f mu.
Proof. exact: finite_expect_nonnegative. Qed.
Lemma real_enum_expect_ae_mono {A} (mu : list (R * A)) f g :
  real_enum_nonnegative mu ->
  (forall p x, List.In (p,x) mu -> p <> 0 -> f x <= g x) ->
  real_enum_expect f mu <= real_enum_expect g mu.
Proof. exact: finite_expect_ae_mono. Qed.
Lemma real_enum_expect_app {A} (mu nu : list (R * A)) f :
  real_enum_expect f (mu ++ nu) = real_enum_expect f mu + real_enum_expect f nu.
Proof. exact: finite_expect_app. Qed.
Lemma real_enum_expect_weight_map {A} (mu : list (R * A)) p f :
  real_enum_expect f (List.map (fun qx => (p * fst qx, snd qx)) mu) = p * real_enum_expect f mu.
Proof. exact: finite_expect_weight_map. Qed.

Definition SubEnumR (A : Type) := FiniteSubdist R A.
Definition subenumR_raw {A} (mu : SubEnumR A) : list (R * A) :=
  finite_enum_raw (finite_subdist_enum mu).

(** Accessor theorem, not a distribution field: the only sign certificate
    is the one owned by the nested shared weighting. *)
Lemma subenumR_nonnegative {A} (mu : SubEnumR A) :
  real_enum_nonnegative (subenumR_raw mu).
Proof. exact (finite_enum_nonnegative (finite_subdist_enum mu)). Qed.
Lemma subenumR_mass_bound {A} (mu : SubEnumR A) :
  real_enum_expect (fun _ => 1) (subenumR_raw mu) <= 1.
Proof. exact (finite_subdist_mass_bound mu). Qed.
Arguments subenumR_raw {A} _.
Arguments subenumR_nonnegative {A} _.
Arguments subenumR_mass_bound {A} _.

Definition subenumR_of_list {A} (mu : list (R * A))
    (Hnn : real_enum_nonnegative mu)
    (Hmass : real_enum_expect (fun _ => 1) mu <= 1) : SubEnumR A :=
  finite_subdist_of_list Hnn Hmass.

Definition subenumR_expect {A} (mu : SubEnumR A) f := real_enum_expect f (subenumR_raw mu).
Definition subenumR_ret {A} (x : A) : SubEnumR A := finite_subdist_ret R x.
Definition subenumR_zero {A} : SubEnumR A := @finite_subdist_zero R A.

Definition subenumR_coin (p : R) (Hp : 0 <= p) (Hp1 : p <= 1) : SubEnumR bool.
Proof.
  refine (@subenumR_of_list bool [(p,true); (1-p,false)] _ _).
  - intros q b [H|[H|[]]]; inversion H; subst; [exact Hp|by rewrite subr_ge0].
  - cbn; by rewrite !mulr1 addr0 addrC subrK.
Defined.

Definition real_enum_bind {A B} (mu : list (R * A)) (k : A -> SubEnumR B) : list (R * B) :=
  finite_bind mu (fun x => subenumR_raw (k x)).

Lemma real_enum_expect_bind {A B} (mu : list (R * A)) (k : A -> SubEnumR B) f :
  real_enum_expect f (real_enum_bind mu k) =
  real_enum_expect (fun x => subenumR_expect (k x) f) mu.
Proof. exact: finite_expect_bind. Qed.

Definition subenumR_bind {A B} (mu : SubEnumR A) (k : A -> SubEnumR B) : SubEnumR B :=
  finite_subdist_bind mu k.

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
Proof. exact: finite_subdist_expect_bind. Qed.

Lemma subenumR_bind_ret_l {A B} (x : A) (k : A -> SubEnumR B) :
  subenumR_eq (subenumR_bind (subenumR_ret x) k) (k x).
Proof. intro f; exact: finite_subdist_bind_ret_l. Qed.
Lemma subenumR_bind_ret_r {A} (mu : SubEnumR A) :
  subenumR_eq (subenumR_bind mu (fun x => subenumR_ret x)) mu.
Proof. intro f; exact: finite_subdist_bind_ret_r. Qed.
Lemma subenumR_bind_assoc {A B C} (mu : SubEnumR A) (k : A -> SubEnumR B) (h : B -> SubEnumR C) :
  subenumR_eq (subenumR_bind (subenumR_bind mu k) h)
    (subenumR_bind mu (fun x => subenumR_bind (k x) h)).
Proof. intro f; exact: finite_subdist_bind_assoc. Qed.
End FiniteReal.
