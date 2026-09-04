Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Prob Require Import TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Behavior semantics for an arbitrary state-to-distribution kernel.
    Neither the state space nor the kernel contains a PTree, Bind, or Iter
    constructor.  A primitive step either reaches a stable observation or a
    residual state. *)
Polymorphic Variant stable_target (S O : Type) : Type :=
  | SHStable (out : O)
  | SHInternal (state : S).

Arguments SHStable {S O} _.
Arguments SHInternal {S O} _.

Section PrimitiveStableHitting.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FO : @SemanticOmega MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

(** Resolve at most [fuel] residual primitive states.  Stable semantic weight
    is retained immediately; unresolved residual weight is sent to the
    backend's zero.  With a subprobability carrier this is precisely the
    missing-mass approximation. *)
Fixpoint stable_target_approx (fuel : nat) (target : stable_target S A) :
    MF A :=
  match target with
  | SHStable out => sem_ret out
  | SHInternal state =>
      match fuel with
      | Datatypes.O => sem_zero
      | Datatypes.S fuel' =>
          sem_bind (kernel state) (stable_target_approx fuel')
      end
  end.

Definition stable_hitting_approx (fuel : nat) (state : S) : MF A :=
  sem_bind (kernel state) (stable_target_approx fuel).

Definition stable_hitting (state : S) (out : MF A) : Prop :=
  sem_lub (fun fuel => stable_hitting_approx fuel state) out.

(** Historical compatibility name.  Internal-transition closure is already
    intrinsic to stable hitting, so new public statements should use
    [stable_hitting]. *)
Definition stable_hitting_weak := stable_hitting.

Definition stable_hitting_ast (state : S) (out : MF A) : Prop :=
  stable_hitting state out /\ sem_total out.

Lemma stable_target_stableE fuel out :
  stable_target_approx fuel (SHStable out) = sem_ret out.
Proof. destruct fuel; reflexivity. Qed.

Lemma stable_target_internal_zeroE state :
  stable_target_approx Datatypes.O (SHInternal state) = sem_zero.
Proof. reflexivity. Qed.

Lemma stable_target_internal_succE fuel state :
  stable_target_approx (Datatypes.S fuel) (SHInternal state) =
    sem_bind (kernel state) (stable_target_approx fuel).
Proof. reflexivity. Qed.

End PrimitiveStableHitting.

Section PrimitiveStableHittingOrder.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

Lemma stable_target_approx_increasing fuel
    (target : stable_target S A) :
  sem_le (stable_target_approx kernel fuel target)
    (stable_target_approx kernel (Datatypes.S fuel) target).
Proof.
  induction fuel as [|fuel IH] in target |- *; destruct target as [out|state].
  - apply sem_le_refl.
  - apply sem_zero_le.
  - apply sem_le_refl.
  - apply sem_bind_le_k. exact IH.
Qed.

Theorem stable_hitting_increasing state :
  sem_increasing (fun fuel => stable_hitting_approx kernel fuel state).
Proof.
  intro fuel. unfold stable_hitting_approx.
  apply sem_bind_le_k. intro target.
  exact (stable_target_approx_increasing fuel target).
Qed.

Theorem stable_hitting_mono state n m :
  Peano.le n m ->
  sem_le (stable_hitting_approx kernel n state)
    (stable_hitting_approx kernel m state).
Proof.
  intro Hnm. induction Hnm.
  - apply sem_le_refl.
  - eapply sem_le_trans; [exact IHHnm|].
    apply stable_hitting_increasing.
Qed.

End PrimitiveStableHittingOrder.

Section PrimitiveStableHittingLimits.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

Theorem stable_hitting_weak_exists state :
  exists out, stable_hitting_weak kernel state out.
Proof.
  unfold stable_hitting_weak. apply sem_lub_exists.
  exact (stable_hitting_increasing kernel state).
Qed.

Theorem stable_hitting_weak_unique state out1 out2 :
  stable_hitting_weak kernel state out1 ->
  stable_hitting_weak kernel state out2 ->
  sem_eq out1 out2.
Proof.
  unfold stable_hitting_weak. intros H1 H2.
  eapply sem_lub_unique; eassumption.
Qed.

Corollary stable_hitting_exists state :
  exists out, stable_hitting kernel state out.
Proof. apply stable_hitting_weak_exists. Qed.

Corollary stable_hitting_unique state out1 out2 :
  stable_hitting kernel state out1 ->
  stable_hitting kernel state out2 ->
  sem_eq out1 out2.
Proof. apply stable_hitting_weak_unique. Qed.

End PrimitiveStableHittingLimits.

Section PrimitiveStableHittingAE.
Context {MF : Type -> Type}
  `{FI : SemanticMeasure MF}
  `{FO : @SemanticOmega MF FI}
  `{FAE : @SemanticMeasureAEKleisliLaws MF FI}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).
Variable D : S -> Prop.
Variable P : A -> Prop.

Definition stable_target_invariant (target : stable_target S A) : Prop :=
  match target with
  | SHStable out => P out
  | SHInternal state => D state
  end.

Hypothesis kernel_ae_closed : forall state, D state ->
  sem_ae (kernel state) stable_target_invariant.

Lemma stable_target_approx_ae fuel target :
  stable_target_invariant target ->
  sem_ae (stable_target_approx kernel fuel target) P.
Proof.
  revert target. induction fuel as [|fuel IH]; intros [out|state] Hgood.
  - apply sem_ae_ret. exact Hgood.
  - apply sem_ae_zero.
  - apply sem_ae_ret. exact Hgood.
  - cbn. eapply sem_ae_bind.
    + exact (kernel_ae_closed Hgood).
    + intros target Htarget. exact (IH target Htarget).
Qed.

Lemma stable_hitting_approx_ae fuel state :
  D state -> sem_ae (stable_hitting_approx kernel fuel state) P.
Proof.
  intro HD. unfold stable_hitting_approx. eapply sem_ae_bind.
  - exact (kernel_ae_closed HD).
  - intros target Htarget.
    exact (stable_target_approx_ae fuel Htarget).
Qed.

(** The central unbounded invariant theorem: closure of one primitive kernel
    is enough to establish closure of its entire omega stable-hitting limit.
    Totality is not needed for this support property. *)
Theorem stable_hitting_weak_ae state out :
  D state -> stable_hitting_weak kernel state out -> sem_ae out P.
Proof.
  intros HD Hlimit. eapply sem_ae_lub; [exact Hlimit|].
  intro fuel. exact (stable_hitting_approx_ae fuel HD).
Qed.

Corollary stable_hitting_ae state out :
  D state -> stable_hitting kernel state out -> sem_ae out P.
Proof. apply stable_hitting_weak_ae. Qed.

Corollary stable_hitting_ast_ae state out :
  D state -> stable_hitting_ast kernel state out -> sem_ae out P.
Proof.
  intros HD [Hweak _]. exact (stable_hitting_weak_ae HD Hweak).
Qed.

End PrimitiveStableHittingAE.
