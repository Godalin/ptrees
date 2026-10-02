(** Ordinary absorbing Kleisli iteration on the frontier carrier.
    Formal limit equations and genuine order-theoretic leastness are kept
    separate: the general omega interface need not make sem_lub an order lub. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure Omega BindOrder.
Set Implicit Arguments.
Unset Strict Implicit.

Section Iteration.
Context {M : Type → Type} `{MI : SemanticMeasure M}
  `{MO : @SemanticOmega M MI}.
Context {I A : Type} (K : I → M (I+A)).

Definition sem_iter_step (X : I → M A) i : M A :=
  sem_bind (K i) (fun next =>
    match next with inl j => X j | inr a => sem_ret a end).

Fixpoint sem_iter_approx (n : nat) (i : I) : M A :=
  match n with
  | O => sem_zero
  | S m => sem_iter_step (sem_iter_approx m) i
  end.

Definition sem_iter i out := sem_lub (fun n => sem_iter_approx n i) out.

Context `{Ord : @SemanticMeasureOrderLaws M MI MO}.

Lemma sem_iter_step_mono X Y :
  (∀ i, sem_le (X i) (Y i)) →
  ∀ i, sem_le (sem_iter_step X i) (sem_iter_step Y i).
Proof.
  intros H i. apply sem_bind_le_k. intros [j|a]; [apply H|apply sem_le_refl].
Qed.

Lemma sem_iter_approx_increasing i :
  sem_increasing (fun n => sem_iter_approx n i).
Proof.
  intro n; revert i; induction n as [|n IH]; intro i.
  - apply sem_zero_le.
  - apply sem_iter_step_mono. exact IH.
Qed.

(** This finite induction does not assume any order-theoretic property of
    sem_lub, nor compatibility of sem_eq with sem_le. *)
Lemma sem_iter_approx_prefixed_bound Y
    (Hpre : ∀ i, sem_le (sem_iter_step Y i) (Y i)) n i :
  sem_le (sem_iter_approx n i) (Y i).
Proof.
  revert i; induction n as [|n IH]; intro i; [apply sem_zero_le|].
  eapply sem_le_trans; [apply sem_iter_step_mono; exact IH|apply Hpre].
Qed.

Context `{Omega : @SemanticOmegaLaws M MI MO}
  `{Cofinal : @SemanticOmegaCofinalityLaws M MI MO}.

Theorem sem_iter_exists i : ∃ out, sem_iter i out.
Proof. apply sem_lub_exists. apply sem_iter_approx_increasing. Qed.

Lemma sem_iter_lub_shift i out :
  sem_iter i out ↔ sem_lub (fun n => sem_iter_approx (S n) i) out.
Proof.
  unfold sem_iter. split; intro H.
  - apply (proj2 (sem_lub_zero_prefix _ _)).
    eapply sem_lub_chain_proper; [|exact H].
    intro n; destruct n; cbn [sem_zero_prefix sem_iter_approx];
      eapply sem_lub_unique; apply sem_lub_constant.
  - eapply sem_lub_chain_proper;
      [|exact (proj1 (sem_lub_zero_prefix _ _) H)].
    intro n; destruct n; cbn [sem_zero_prefix sem_iter_approx];
      eapply sem_lub_unique; apply sem_lub_constant.
Qed.

Context `{Diagonal : @SemanticMeasureDiagonalLaws M MI MO}.

Lemma sem_iter_step_lub (X : I → M A)
    (HX : ∀ i, sem_iter i (X i)) i :
  sem_lub (fun n => sem_iter_approx (S n) i) (sem_iter_step X i).
Proof.
  apply (sem_bind_diagonal_lub (SI := MI) (SO := MO))
    with (source := fun _ => K i).
  - intro n. apply sem_le_refl.
  - intros [j|a] n; [apply sem_iter_approx_increasing|apply sem_le_refl].
  - apply sem_lub_constant.
  - intros [j|a]; [apply HX|apply sem_lub_constant].
Qed.

Theorem sem_iter_fixed_point (X : I → M A)
    (HX : ∀ i, sem_iter i (X i)) i :
  sem_eq (X i) (sem_iter_step X i).
Proof.
  eapply sem_lub_unique;
    [apply (proj1 (sem_iter_lub_shift i (X i))); apply HX|apply sem_iter_step_lub; exact HX].
Qed.

(** Actual CPO models discharge these ordinary supremum properties.
    They are not installed as a new class or assumed of raw FreeOmega. *)
Hypothesis lub_upper : ∀ (c : nat → M A) out,
  sem_lub c out → ∀ n, sem_le (c n) out.
Hypothesis lub_least : ∀ (c : nat → M A) out bound,
  sem_lub c out → (∀ n, sem_le (c n) bound) → sem_le out bound.

Theorem sem_iter_least_prefixed (X : I → M A)
    (HX : ∀ i, sem_iter i (X i)) Y :
  (∀ i, sem_le (sem_iter_step Y i) (Y i)) →
  ∀ i, sem_le (X i) (Y i).
Proof.
  intros HY i. eapply lub_least; [apply HX|intro n].
  apply sem_iter_approx_prefixed_bound. exact HY.
Qed.

(** Both fixed-point inequalities, plus leastness among all pre-fixed
    points. This is the standard least-fixed-point while semantics. *)
Theorem sem_iter_least_fixed_point (X : I → M A)
    (HX : ∀ i, sem_iter i (X i)) :
  (∀ i, sem_le (sem_iter_step X i) (X i) ∧
             sem_le (X i) (sem_iter_step X i)) ∧
  (∀ Y, (∀ i, sem_le (sem_iter_step Y i) (Y i)) →
             ∀ i, sem_le (X i) (Y i)).
Proof.
  split; [intro i; split|apply sem_iter_least_prefixed; exact HX].
  - eapply lub_least; [apply sem_iter_step_lub; exact HX|intro n].
    eapply lub_upper. apply (proj1 (sem_iter_lub_shift i (X i))). apply HX.
  - eapply lub_least; [apply (proj1 (sem_iter_lub_shift i (X i))); apply HX|intro n].
    eapply lub_upper. apply sem_iter_step_lub. exact HX.
Qed.
End Iteration.

Lemma sem_bind_zero_eq {M} `{MI : SemanticMeasure M}
    `{MO : @SemanticOmega M MI} `{Ord : @SemanticMeasureOrderLaws M MI MO}
    `{Omega : @SemanticOmegaLaws M MI MO}
    `{Cofinal : @SemanticOmegaCofinalityLaws M MI MO}
    `{Directed : @SemanticOmegaDirectedCofinalityLaws M MI MO}
    `{BO : @SemanticMeasureBindOrderLaws M MI MO}
    {A B} (k : A → M B) :
  sem_eq (sem_bind sem_zero k) sem_zero.
Proof.
  apply sem_eq_of_le_equiv; [apply sem_bind_zero_order|apply sem_zero_le].
Qed.
