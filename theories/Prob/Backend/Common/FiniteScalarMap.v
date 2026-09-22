(** Ordinary-scalar transport of the shared finite representations.
    An order-preserving ring morphism transports both container invariants.
    Operation laws compare raw data, not equality of proof fields. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FiniteListAlgebra FiniteAtoms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section ScalarMap.
Variables R S : numDomainType.
Variable f : {rmorphism R -> S}.
Hypothesis f_mono : forall x y, x <= y -> f x <= f y.

Definition finite_map_weights {A} (mu : list (R * A)) : list (S * A) :=
  List.map (fun px => (f px.1, px.2)) mu.

Lemma finite_map_weights_nonnegative {A} (mu : list (R * A)) :
  finite_nonnegative mu -> finite_nonnegative (finite_map_weights mu).
Proof.
  move=> H p x Hin; apply List.in_map_iff in Hin.
  destruct Hin as [[q y] [He Hq]]; cbn in He; inversion He; subst.
  rewrite -(rmorph0 f); exact: f_mono (H _ _ Hq).
Qed.

Lemma finite_map_weights_expect {A} (mu : list (R * A)) (g : A -> R) :
  finite_expect (fun x => f (g x)) (finite_map_weights mu) = f (finite_expect g mu).
Proof.
  elim: mu=> [|[p x] tl IH] /=; first by rewrite rmorph0.
  by rewrite rmorphD rmorphM IH.
Qed.

Lemma finite_map_weights_mass {A} (mu : list (R * A)) :
  finite_expect (fun _ => 1) (finite_map_weights mu) = f (finite_expect (fun _ => 1) mu).
Proof. rewrite -finite_map_weights_expect; apply finite_expect_ext=> x; by rewrite rmorph1. Qed.

Lemma finite_map_weights_ret {A} (x : A) :
  finite_map_weights [:: (1,x)] = [:: (1,x)].
Proof. by rewrite /finite_map_weights /= rmorph1. Qed.

Lemma finite_map_weights_bind {A B} (mu : list (R * A)) (k : A -> list (R * B)) :
  finite_map_weights (finite_bind mu k) =
  finite_bind (finite_map_weights mu) (fun x => finite_map_weights (k x)).
Proof.
  rewrite -!finite_bind_with_numeric.
  apply finite_bind_with_scalar_map=> p q; exact: rmorphM.
Qed.

Lemma finite_map_weights_atom {A : eqType} (mu : list (R*A)) x :
  finite_atom x (finite_map_weights mu) = f (finite_atom x mu).
Proof.
  elim: mu=> [|[p y] tl IH]; first by rewrite /= rmorph0.
  rewrite /finite_map_weights /= !finite_atom_cons -/finite_map_weights IH rmorphD.
  case: (y == x); by rewrite ?rmorph0.
Qed.
Lemma finite_map_weights_scale {A} p (mu : list (R*A)) :
  finite_map_weights (finite_weight_map p mu) =
  finite_weight_map (f p) (finite_map_weights mu).
Proof. by elim: mu=> [|[q x] tl IH] //=; rewrite rmorphM IH. Qed.
Lemma finite_map_weights_map {A B} (g : A -> B) (mu : list (R*A)) :
  finite_map_weights (List.map (fun px => (px.1,g px.2)) mu) =
  List.map (fun px => (px.1,g px.2)) (finite_map_weights mu).
Proof. by elim: mu=> [|[p x] tl IH] //=; rewrite IH. Qed.
Lemma finite_map_weights_app {A} (mu nu : list (R*A)) :
  finite_map_weights (mu++nu) = finite_map_weights mu ++ finite_map_weights nu.
Proof. exact: List.map_app. Qed.
Lemma finite_map_weights_filter {A} (P : A -> bool) (mu : list (R*A)) :
  finite_map_weights (List.filter (fun px => P px.2) mu) =
  List.filter (fun px => P px.2) (finite_map_weights mu).
Proof. by elim: mu=> [|[p x] tl IH] //=; case: (P x)=> /=; rewrite IH. Qed.

Definition finite_enum_map_weights {A} (mu : FiniteEnum R A) : FiniteEnum S A :=
  finite_enum_of_list (finite_map_weights_nonnegative (finite_enum_nonnegative mu)).

Lemma finite_enum_map_weights_expect {A} (mu : FiniteEnum R A) (g : A -> R) :
  finite_enum_expect (finite_enum_map_weights mu) (fun x => f (g x)) =
  f (finite_enum_expect mu g).
Proof. exact: finite_map_weights_expect. Qed.

Lemma finite_enum_map_weights_mass {A} (mu : FiniteEnum R A) :
  finite_mass (finite_enum_map_weights mu) = f (finite_mass mu).
Proof. exact: finite_map_weights_mass. Qed.

Lemma finite_enum_map_weights_ret {A} (x : A) :
  finite_enum_raw (finite_enum_map_weights (finite_enum_ret R x)) = finite_enum_raw (finite_enum_ret S x).
Proof. exact: finite_map_weights_ret. Qed.

Lemma finite_enum_map_weights_zero {A} :
  finite_enum_raw (finite_enum_map_weights (@finite_enum_zero R A)) = finite_enum_raw (@finite_enum_zero S A).
Proof. reflexivity. Qed.

Lemma finite_enum_map_weights_bind {A B} (mu : FiniteEnum R A) (k : A -> FiniteEnum R B) :
  finite_enum_raw (finite_enum_map_weights (finite_enum_bind mu k)) =
  finite_enum_raw (finite_enum_bind (finite_enum_map_weights mu) (fun x => finite_enum_map_weights (k x))).
Proof. exact: finite_map_weights_bind. Qed.

Definition finite_subdist_map_weights {A} (mu : FiniteSubdist R A) : FiniteSubdist S A.
Proof.
  refine (@Build_FiniteSubdist S A (finite_enum_map_weights (finite_subdist_enum mu)) _).
  rewrite finite_enum_map_weights_mass -(rmorph1 f).
  exact: f_mono (finite_subdist_mass_bound mu).
Defined.

Lemma finite_subdist_map_weights_expect {A} (mu : FiniteSubdist R A) (g : A -> R) :
  finite_subdist_expect (finite_subdist_map_weights mu) (fun x => f (g x)) =
  f (finite_subdist_expect mu g).
Proof. exact: finite_map_weights_expect. Qed.

Lemma finite_subdist_map_weights_ret {A} (x : A) :
  finite_enum_raw (finite_subdist_enum (finite_subdist_map_weights (finite_subdist_ret R x))) =
  finite_enum_raw (finite_subdist_enum (finite_subdist_ret S x)).
Proof. exact: finite_map_weights_ret. Qed.

Lemma finite_subdist_map_weights_zero {A} :
  finite_enum_raw (finite_subdist_enum (finite_subdist_map_weights (@finite_subdist_zero R A))) =
  finite_enum_raw (finite_subdist_enum (@finite_subdist_zero S A)).
Proof. reflexivity. Qed.

Lemma finite_subdist_map_weights_bind {A B} (mu : FiniteSubdist R A) (k : A -> FiniteSubdist R B) :
  finite_enum_raw (finite_subdist_enum (finite_subdist_map_weights (finite_subdist_bind mu k))) =
  finite_enum_raw (finite_subdist_enum
    (finite_subdist_bind (finite_subdist_map_weights mu) (fun x => finite_subdist_map_weights (k x)))).
Proof. exact: finite_map_weights_bind. Qed.
End ScalarMap.
