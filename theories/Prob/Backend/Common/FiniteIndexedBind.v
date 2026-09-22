(** Positions of flattened finite binds. This is raw list algebra: values
    need no equality, and weights need no order or probability structure. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq ssrnat ssralg.
From PTree.Prob.Backend.Common Require Import FinitePositions FiniteListAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Positions.
Context {W : Type}.
Variable mul : W -> W -> W.

Lemma finite_index_map_values {A B} (f : A -> B) n (mu : list (W*A)) :
  finite_index_from n (List.map (fun px => (px.1,f px.2)) mu) = finite_index_from n mu.
Proof. by elim: mu n=> [|[p x] tl IH] n //=; rewrite IH. Qed.

Lemma finite_index_shift_from {A} offset start (mu : list (W*A)) :
  finite_index_from (Nat.add offset start) mu =
  List.map (fun pi => (pi.1,Nat.add offset pi.2)) (finite_index_from start mu).
Proof.
  elim: mu offset start=> [|[p x] tl IH] offset start //=.
  by rewrite -Nat.add_succ_r IH.
Qed.
Lemma finite_index_scale {A} offset p (mu : list (W*A)) :
  finite_index_from offset (finite_scale_with mul p mu) =
  finite_scale_with mul p (finite_index_from offset mu).
Proof. by elim: mu offset=> [|[q x] tl IH] offset //=; rewrite IH. Qed.
Lemma finite_index_app {A} offset (mu nu : list (W*A)) :
  finite_index_from offset (mu++nu) =
  finite_index_from offset mu ++ finite_index_from (Nat.add offset (size mu)) nu.
Proof.
  elim: mu offset=> [|[p x] tl IH] offset /=.
  - by rewrite Nat.add_0_r.
  - by rewrite IH Nat.add_succ_r.
Qed.
Lemma finite_index_in_ge {A} n (mu : list (W*A)) p i :
  List.In (p,i) (finite_index_from n mu) -> (n <= i)%coq_nat.
Proof.
  elim: mu n=> [|[q x] tl IH] n //=.
  move=> [He|Hin]; first by inversion He; subst; apply Nat.le_refl.
  have H := IH n.+1 Hin; lia.
Qed.

Fixpoint finite_indexed_bind_blocks {A B} (mu : list (W*A))
    (k : A -> list (W*B)) (offset : nat) : list (W*nat) :=
  match mu with
  | nil => nil
  | (p,a)::tl => finite_scale_with mul p (finite_index_from offset (k a)) ++
      finite_indexed_bind_blocks tl k (Nat.add offset (size (k a)))
  end.
Lemma finite_index_bind {A B} offset (mu : list (W*A)) (k : A -> list (W*B)) :
  finite_index_from offset (finite_bind_with mul mu k) = finite_indexed_bind_blocks mu k offset.
Proof.
  elim: mu offset=> [|[p a] tl IH] offset //=.
  rewrite finite_index_app finite_index_scale.
  have Hsize : size (finite_scale_with mul p (k a)) = size (k a).
  { exact: finite_scale_with_length. }
  by rewrite Hsize IH.
Qed.

Fixpoint finite_indexed_bind_block_from {A B} (mu : list (W*A))
    (k : A -> list (W*B)) (start offset i : nat) : list (W*nat) :=
  match mu with
  | nil => nil
  | (_,a)::tl => if Nat.eqb i start then finite_index_from offset (k a)
      else finite_indexed_bind_block_from tl k start.+1 (Nat.add offset (size (k a))) i
  end.

Lemma finite_bind_with_ext_in {A B} (mu : list (W*A)) (k h : A -> list (W*B)) :
  (forall p x, List.In (p,x) mu -> k x = h x) ->
  finite_bind_with mul mu k = finite_bind_with mul mu h.
Proof.
  elim: mu=> [|[p x] tl IH] H //=.
  rewrite (H p x (or_introl (Logic.eq_refl _))) IH //.
  move=> q y Hy; exact (H q y (or_intror Hy)).
Qed.

Lemma finite_index_bind_as_position_bind {A B} (mu : list (W*A))
    (k : A -> list (W*B)) start offset :
  finite_index_from offset (finite_bind_with mul mu k) =
  finite_bind_with mul (finite_index_from start mu)
    (finite_indexed_bind_block_from mu k start offset).
Proof.
  elim: mu start offset=> [|[p a] tl IH] start offset //=.
  rewrite finite_index_app finite_index_scale.
  have Hsize : size (finite_scale_with mul p (k a)) = size (k a).
  { exact: finite_scale_with_length. }
  rewrite Hsize.
  rewrite (IH start.+1 (Nat.add offset (size (k a)))).
  rewrite Nat.eqb_refl; congr (_ ++ _).
  apply finite_bind_with_ext_in=> q i Hi.
  have Hneq : Nat.eqb i start = false.
  { apply Nat.eqb_neq=> He; subst i; have H := finite_index_in_ge Hi; lia. }
  by rewrite Hneq.
Qed.

Lemma finite_indexed_bind_block_from_nth {A B} (mu : list (W*A))
    (k : A -> list (W*B)) start offset i p a :
  nth_error mu i = Some (p,a) ->
  finite_indexed_bind_block_from mu k start offset (Nat.add start i) =
  finite_index_from (Nat.add offset (finite_bind_offset mu k i)) (k a).
Proof.
  elim: mu start offset i p a=> [|[q x] tl IH] start offset [|i] p a H //=.
  - inversion H; subst; by rewrite Nat.add_0_r Nat.eqb_refl Nat.add_0_r.
  - have Hneq : Nat.eqb (Nat.add start i.+1) start = false.
    { apply Nat.eqb_neq; lia. }
    rewrite Hneq.
    replace (Nat.add start i.+1) with (Nat.add start.+1 i) by lia.
    by rewrite (IH start.+1 (Nat.add offset (size (k x))) i p a H) Nat.add_assoc.
Qed.
End Positions.
