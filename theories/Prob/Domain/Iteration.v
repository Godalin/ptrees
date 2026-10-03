(** Classical least-fixed-point iteration in the independent expectation
    domain. This module imports neither a probability interface nor trees. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Domain Require Import Expectation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Iteration.
Variable R : realType.
Context {I A : Type} (K : I → OmegaVal R (I+A)).

Definition oval_iter_step (X : I → OmegaVal R A) i :=
  oval_bind (K i) (λ v, match v with inl j => X j | inr a => oval_ret R a end).
Fixpoint oval_iter_approx n i : OmegaVal R A :=
  match n with O => @oval_bottom R A | S m => oval_iter_step (oval_iter_approx m) i end.

Lemma oval_iter_step_mono X Y :
  (∀ i, oval_le (X i) (Y i)) →
  ∀ i, oval_le (oval_iter_step X i) (oval_iter_step Y i).
Proof.
  intros H i. apply oval_bind_mono; [apply oval_le_refl|].
  intros [j|a]; [apply H|apply oval_le_refl].
Qed.
Lemma oval_iter_increasing i : oval_increasing (λ n, oval_iter_approx n i).
Proof.
  intro n; revert i; induction n as [|n IH]; intro i; [apply oval_bottom_le|].
  apply oval_iter_step_mono. exact IH.
Qed.
Definition oval_iter i := oval_lub (oval_iter_increasing i).

Lemma oval_iter_upper i n : oval_le (oval_iter_approx n i) (oval_iter i).
Proof. exact (oval_lub_upper (oval_iter_increasing i) n). Qed.
Lemma oval_iter_least i L :
  (∀ n, oval_le (oval_iter_approx n i) L) → oval_le (oval_iter i) L.
Proof. intro H. exact (oval_lub_least (oval_iter_increasing i) H). Qed.

Theorem oval_iter_least_prefixed Y :
  (∀ i, oval_le (oval_iter_step Y i) (Y i)) →
  ∀ i, oval_le (oval_iter i) (Y i).
Proof.
  intros HY i. apply oval_iter_least. intro n; revert i.
  induction n as [|n IH]; intro i; [apply oval_bottom_le|].
  eapply oval_le_trans; [apply oval_iter_step_mono; exact IH|apply HY].
Qed.

Local Definition next n (v : I+A) : OmegaVal R A :=
  match v with inl j => oval_iter_approx n j | inr a => oval_ret R a end.
Local Lemma next_increasing v : oval_increasing (λ n, next n v).
Proof. destruct v as [j|a]; [apply oval_iter_increasing|intro n; apply oval_le_refl]. Qed.

Lemma oval_iter_step_limit i :
  oval_eq (oval_iter_step oval_iter i)
    (oval_lub (oval_bind_chain_r (K i) next_increasing)).
Proof.
  intros f Hf.
  transitivity (oval_eval (oval_bind (K i) (λ v, oval_lub (next_increasing v))) f).
  - cbn [oval_iter_step oval_bind oval_eval].
    apply oval_eval_ext. intros [j|a]; [reflexivity|].
    symmetry. change (oval_sup (λ _ : nat, f a) = f a). apply oval_sup_const.
  - exact (oval_bind_lub_r (K i) next_increasing Hf).
Qed.

Theorem oval_iter_fixed_point i : oval_eq (oval_iter i) (oval_iter_step oval_iter i).
Proof.
  apply oval_le_antisym.
  - apply oval_iter_least. intros [|n]; [apply oval_bottom_le|].
    apply oval_iter_step_mono. intro j. apply oval_iter_upper.
  - intros f Hf. rewrite (oval_iter_step_limit i Hf).
    assert (Hb : ∀ n, oval_le (oval_bind (K i) (next n)) (oval_iter i)).
    { intro n. exact (oval_iter_upper i (S n)). }
    exact (oval_lub_least (oval_bind_chain_r (K i) next_increasing) Hb Hf).
Qed.
End Iteration.
