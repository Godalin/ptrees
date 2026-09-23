(** Generic finite interpreter scheduling. Reuses the preorder algebra of
    bind scheduling; no observable-equality-to-order reflection is assumed. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier
  PTreeKernel BindScheduling.
From PTree.Interp Require Import Kernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Scheduling.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{DC : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.
Variable handler : forall X, E X -> ptree F MN X.

(** These are explicit local specializations of existing generic algebra,
    not new global instances or a second backend proof. *)
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance mixed_equiv A B (mu : MN A) :
  Proper (pointwise_relation A (@equiv B) ==> @equiv B)
    (@mixed_bind MN MF MX A B mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.

Local Lemma ret_equiv A B (x : A) (k : A -> MF B) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma mixed_assoc_equiv A B C (mu : MN A)
    (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h)
    (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

Local Notation unfold_source := (@BindScheduling.hitting_unfold E MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).
Local Notation unfold_target := (@BindScheduling.hitting_unfold F MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Definition ptree_interp_split_approx {A} n m (t : ptree E MN A) :=
  sem_bind (ptree_hitting_approx (MF := MF) n (observe t))
    (ptree_interp_head_approx m handler).

Lemma ptree_interp_hitting_le_diagonal {A} n (t : ptree E MN A) :
  sem_le (ptree_hitting_approx (MF := MF) n (observe (PTree.interp handler t)))
    (ptree_interp_split_approx n n t).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold ptree_interp_split_approx; rewrite observe_interp;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite unfold_source; setoid_rewrite unfold_target; cbn [observe].
  - setoid_rewrite ret_equiv. cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    apply (proj2 (unfold_target 0 (RetF r))).
  - apply sem_zero_le.
  - apply sem_zero_le.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    apply (proj2 (unfold_target (S n) (RetF r))).
  - eapply sem_le_trans; [apply IH|].
    apply sem_bind_le_k. intro h. apply ptree_hitting_mono. lia.
  - setoid_rewrite ret_equiv.
    cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    exact (proj2 (unfold_target (S n)
      (TauF (PTree.bind (handler e) (fun x => PTree.interp handler (k x)))))).
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply IH|].
    apply sem_bind_le_k. intro h. apply ptree_hitting_mono. lia.
Qed.

Lemma ptree_interp_split_le_hitting {A} n m (t : ptree E MN A) :
  sem_le (ptree_interp_split_approx n m t)
    (ptree_hitting_approx (MF := MF) (n + m) (observe (PTree.interp handler t))).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold ptree_interp_split_approx; rewrite observe_interp;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite unfold_source; setoid_rewrite unfold_target; cbn [observe Nat.add].
  - setoid_rewrite ret_equiv. cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    apply (proj1 (unfold_target m (RetF r))).
  - eapply sem_le_trans; [apply sem_bind_zero_order|apply sem_zero_le].
  - setoid_rewrite ret_equiv.
    cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    exact (proj1 (unfold_target m
      (TauF (PTree.bind (handler e) (fun x => PTree.interp handler (k x)))))).
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply sem_bind_zero_order|apply sem_zero_le].
  - setoid_rewrite ret_equiv. cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    apply (proj1 (unfold_target m (RetF r))).
  - apply IH.
  - setoid_rewrite ret_equiv.
    cbn [ptree_interp_head_approx ptree_interp_head_tree observe].
    eapply sem_le_trans with (nu := ptree_hitting_approx (MF := MF) (S n + m)
      (TauF (PTree.bind (handler e) (fun x => PTree.interp handler (k x))))).
    + apply ptree_hitting_mono. lia.
    + exact (proj1 (unfold_target (S n + m)
        (TauF (PTree.bind (handler e) (fun x => PTree.interp handler (k x)))))).
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x. apply IH.
Qed.

Theorem ptree_interp_cofinal_all {A} (t : ptree E MN A) :
  ptree_interp_cofinal (MF := MF) handler t.
Proof.
  intro out. apply sem_lub_cofinal.
  - apply ptree_hitting_increasing.
  - intro n. unfold ptree_interp_diagonal_approx.
    eapply sem_le_trans; [apply sem_bind_le_mu; apply ptree_hitting_increasing|].
    apply sem_bind_le_k. intro h. apply ptree_hitting_increasing.
  - intro n. exists n. apply ptree_interp_hitting_le_diagonal.
  - intro n. exists (n + n). apply ptree_interp_split_le_hitting.
Qed.
End Scheduling.
