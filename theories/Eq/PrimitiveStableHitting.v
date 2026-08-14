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
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {S A : Type}.
Variable kernel : S -> MF (stable_target S A).

(** Resolve at most [fuel] residual primitive states.  Stable mass is
    retained immediately; unresolved residual mass is discarded into the
    subprobability bottom. *)
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

Definition stable_hitting_weak (state : S) (out : MF A) : Prop :=
  sem_lub (fun fuel => stable_hitting_approx fuel state) out.

Definition stable_hitting_ast (state : S) (out : MF A) : Prop :=
  stable_hitting_weak state out /\ sem_total out.

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
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}
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
  `{FI : SemanticMeasureInterface MF}
  `{FO : @SemanticOmegaInterface MF FI}
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

End PrimitiveStableHittingLimits.
