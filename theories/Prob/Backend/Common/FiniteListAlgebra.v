(** Raw finite weighted-list algebra. Multiplication is an ordinary function,
    not a new scalar subtype or probability capability. Algebraic laws are
    explicit lemma premises; checked numeric operations specialize them. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun seq ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RawAlgebra.
Context {W : Type} (mul : W -> W -> W).

Fixpoint finite_scale_with {A : Type} (p : W) (mu : list (W * A)) : list (W * A) :=
  match mu with
  | [::] => [::]
  | (q,x)::tl => (mul p q,x)::finite_scale_with p tl
  end.

Definition finite_bind_with {A B : Type} (mu : list (W * A)) (k : A -> list (W * B)) :=
  foldr (fun '(p,x) tl => finite_scale_with p (k x) ++ tl) [::] mu.

Lemma finite_scale_with_map {A} p (mu : list (W * A)) :
  finite_scale_with p mu = List.map (fun px => (mul p px.1, px.2)) mu.
Proof. by elim: mu=> [|[q x] tl IH] //=; rewrite IH. Qed.

Lemma finite_scale_with_app {A} p (mu nu : list (W * A)) :
  finite_scale_with p (mu ++ nu) = finite_scale_with p mu ++ finite_scale_with p nu.
Proof. by elim: mu=> [|[q x] tl IH] //=; rewrite IH. Qed.

Lemma finite_scale_with_comp {A} p q (mu : list (W * A)) :
  (forall a b c, mul a (mul b c) = mul (mul a b) c) ->
  finite_scale_with p (finite_scale_with q mu) = finite_scale_with (mul p q) mu.
Proof. move=> Hassoc; by elim: mu=> [|[r x] tl IH] //=; rewrite Hassoc IH. Qed.

Lemma finite_bind_with_app {A B} (mu nu : list (W * A)) (k : A -> list (W * B)) :
  finite_bind_with (mu ++ nu) k = finite_bind_with mu k ++ finite_bind_with nu k.
Proof. by elim: mu=> [|[p x] tl IH] //=; rewrite IH catA. Qed.

Lemma finite_scale_with_bind {A B} p (mu : list (W * A)) (k : A -> list (W * B)) :
  (forall a b c, mul a (mul b c) = mul (mul a b) c) ->
  (forall a b, mul a b = mul b a) ->
  finite_scale_with p (finite_bind_with mu k) =
  finite_bind_with mu (fun x => finite_scale_with p (k x)).
Proof.
  move=> Hassoc Hcomm; elim: mu=> [|[q x] tl IH] //=.
  rewrite finite_scale_with_app IH !finite_scale_with_comp //.
  by rewrite (Hcomm p q).
Qed.

Lemma finite_bind_with_scale {A B} p (mu : list (W * A)) (k : A -> list (W * B)) :
  (forall a b c, mul a (mul b c) = mul (mul a b) c) ->
  finite_bind_with (finite_scale_with p mu) k = finite_scale_with p (finite_bind_with mu k).
Proof.
  move=> Hassoc; elim: mu=> [|[q x] tl IH] //=.
  by rewrite finite_scale_with_app finite_scale_with_comp // IH.
Qed.

Lemma finite_bind_with_assoc {A B C} (mu : list (W * A))
    (k : A -> list (W * B)) (h : B -> list (W * C)) :
  (forall a b c, mul a (mul b c) = mul (mul a b) c) ->
  finite_bind_with (finite_bind_with mu k) h =
  finite_bind_with mu (fun x => finite_bind_with (k x) h).
Proof.
  move=> Hassoc; elim: mu=> [|[p x] tl IH] //=.
  by rewrite finite_bind_with_app finite_bind_with_scale // IH.
Qed.

Lemma finite_bind_with_left_unit {A B} one (x : A) (k : A -> list (W * B)) :
  (forall p, mul one p = p) -> finite_bind_with [:: (one,x)] k = k x.
Proof.
  move=> H; rewrite /finite_bind_with /= cats0 finite_scale_with_map.
  elim: (k x)=> [|[p y] tl IH] //=; by rewrite H IH.
Qed.

Lemma finite_bind_with_right_unit {A} one (mu : list (W * A)) :
  (forall p, mul p one = p) -> finite_bind_with mu (fun x => [:: (one,x)]) = mu.
Proof. move=> H; by elim: mu=> [|[p x] tl IH] //=; rewrite H IH. Qed.

Lemma finite_scale_with_length {A} p (mu : list (W * A)) :
  size (finite_scale_with p mu) = size mu.
Proof. by elim: mu=> [|[q x] tl IH] //=; rewrite IH. Qed.
End RawAlgebra.

Lemma finite_scale_with_scalar_map {W V A} (mul : W -> W -> W)
    (mul' : V -> V -> V) (f : W -> V) p (mu : list (W * A)) :
  (forall p q, f (mul p q) = mul' (f p) (f q)) ->
  List.map (fun px => (f px.1, px.2)) (finite_scale_with mul p mu) =
  finite_scale_with mul' (f p) (List.map (fun px => (f px.1, px.2)) mu).
Proof. move=> H; by elim: mu=> [|[q x] tl IH] //=; rewrite H IH. Qed.

Lemma finite_bind_with_scalar_map {W V A B} (mul : W -> W -> W)
    (mul' : V -> V -> V) (f : W -> V) (mu : list (W * A)) (k : A -> list (W * B)) :
  (forall p q, f (mul p q) = mul' (f p) (f q)) ->
  List.map (fun px => (f px.1, px.2)) (finite_bind_with mul mu k) =
  finite_bind_with mul' (List.map (fun px => (f px.1, px.2)) mu)
    (fun x => List.map (fun px => (f px.1, px.2)) (k x)).
Proof.
  move=> H; elim: mu=> [|[p x] tl IH] //=.
  by rewrite List.map_app (finite_scale_with_scalar_map (mul' := mul') _ _ H) IH.
Qed.

Section CheckedConnection.
Variable R : numDomainType.
Lemma finite_scale_with_weight_map {A} (p : R) (mu : list (R * A)) :
  finite_scale_with (fun x y => x * y) p mu = finite_weight_map p mu.
Proof. exact: finite_scale_with_map. Qed.
Lemma finite_bind_with_numeric {A B} (mu : list (R * A)) (k : A -> list (R * B)) :
  finite_bind_with (fun x y => x * y) mu k = finite_bind mu k.
Proof. by elim: mu=> [|[p x] tl IH] //=; rewrite finite_scale_with_weight_map IH. Qed.
End CheckedConnection.
