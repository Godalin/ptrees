(** Backend-independent finite scheduling. The hypotheses below concern only
    measure operations and approximation, never observable equality. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BindScheduling.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}.

Hypothesis bind_ret_order : forall A B (x : A) (k : A -> MF B),
  sem_le (sem_bind (sem_ret x) k) (k x) /\
  sem_le (k x) (sem_bind (sem_ret x) k).
Hypothesis bind_zero_order : forall A B (k : A -> MF B),
  sem_le (sem_bind sem_zero k) sem_zero.
Hypothesis mixed_assoc_order : forall A B C (mu : MN A)
    (k : A -> MF B) (h : B -> MF C),
  sem_le (sem_bind (mixed_bind mu k) h)
    (mixed_bind mu (fun x => sem_bind (k x) h)) /\
  sem_le (mixed_bind mu (fun x => sem_bind (k x) h))
    (sem_bind (mixed_bind mu k) h).
Hypothesis mixed_bind_mono : forall A B (mu : MN A) (k h : A -> MF B),
  (forall x, sem_le (k x) (h x)) ->
  sem_le (mixed_bind mu k) (mixed_bind mu h).

Local Definition equiv {A} (x y : MF A) := sem_le x y /\ sem_le y x.
Local Instance equiv_equivalence A : Equivalence (@equiv A).
Proof.
  split.
  - intro x; split; apply sem_le_refl.
  - intros x y [Hxy Hyx]; split; assumption.
  - intros x y z [Hxy Hyx] [Hyz Hzy]; split; eapply sem_le_trans; eassumption.
Qed.
Local Instance le_equiv_Proper A : Proper (equiv ==> equiv ==> iff) (@sem_le MF FI FO A).
Proof.
  intros x x' [Hxx' Hx'x] y y' [Hyy' Hy'y]; split; intro H.
  - eapply sem_le_trans; [exact Hx'x|].
    eapply sem_le_trans; [exact H|exact Hyy'].
  - eapply sem_le_trans; [exact Hxx'|].
    eapply sem_le_trans; [exact H|exact Hy'y].
Qed.
Local Instance bind_equiv_Proper A B :
  Proper (equiv ==> pointwise_relation A equiv ==> equiv) (@sem_bind MF FI A B).
Proof.
  intros mu nu [Hmn Hnm] k h Hkh; split.
  - eapply sem_le_trans; [apply sem_bind_le_mu; exact Hmn|].
    apply sem_bind_le_k; intro x; exact (proj1 (Hkh x)).
  - eapply sem_le_trans; [apply sem_bind_le_mu; exact Hnm|].
    apply sem_bind_le_k; intro x; exact (proj2 (Hkh x)).
Qed.
Local Instance mixed_equiv_Proper A B (mu : MN A) :
  Proper (pointwise_relation A equiv ==> equiv) (@mixed_bind MN MF MX A B mu).
Proof.
  intros k h H; split; apply mixed_bind_mono; intro x;
    [exact (proj1 (H x))|exact (proj2 (H x))].
Qed.

Local Lemma ret_equiv A B (x : A) (k : A -> MF B) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply bind_ret_order. Qed.
Local Lemma mixed_assoc_equiv A B C (mu : MN A)
    (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h)
    (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_assoc_order. Qed.

Local Lemma hitting_unfold {A} n (t : ptree' E MN A) :
  equiv (ptree_hitting_approx (MF := MF) n t)
    (match t with
     | RetF a => sem_ret (FHRet a)
     | VisF _ e k => sem_ret (FHVis e k)
     | TauF u => match n with O => sem_zero
                    | S m => ptree_hitting_approx m (observe u) end
     | ProbF _ mu k => mixed_bind mu (fun x => match n with
          O => sem_zero | S m => ptree_hitting_approx m (observe (k x)) end)
     end).
Proof.
  destruct t as [r|u|X e c|X mu c]; unfold ptree_hitting_approx, stable_hitting_approx,
    ptree_primitive_kernel.
  - etransitivity; [apply ret_equiv|].
    rewrite stable_target_stableE. reflexivity.
  - destruct n; apply bind_ret_order.
  - etransitivity; [apply ret_equiv|].
    rewrite stable_target_stableE. reflexivity.
  - transitivity (mixed_bind mu (fun x => sem_bind
        (sem_ret (SHInternal (observe (c x))))
        (stable_target_approx (@ptree_primitive_kernel E MN MF FI MX A) n))).
    + apply mixed_assoc_order.
    + apply mixed_equiv_Proper. intro x.
      destruct n; apply bind_ret_order.
Qed.

Definition ptree_bind_split_approx {A B} n m
    (t : ptree E MN A) (k : A -> ptree E MN B) :=
  sem_bind (ptree_hitting_approx (MF := MF) n (observe t))
    (ptree_head_bind_approx m k).

Theorem ptree_bind_global_le_diagonal {A B} n
    (t : ptree E MN A) (k : A -> ptree E MN B) :
  sem_le (ptree_hitting_approx (MF := MF) n (observe (PTree.bind t k)))
    (ptree_bind_split_approx n n t k).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold ptree_bind_split_approx; rewrite observe_bind;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite hitting_unfold; cbn [observe].
  - setoid_rewrite ret_equiv. cbn [ptree_head_bind_approx].
    apply (proj2 (hitting_unfold 0 (observe (k r)))).
  - apply sem_zero_le.
  - setoid_rewrite ret_equiv. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_mono. intro x.
    apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [ptree_head_bind_approx].
    apply (proj2 (hitting_unfold (S n) (observe (k r)))).
  - eapply sem_le_trans; [apply IH|].
    apply sem_bind_le_k; intro head.
    apply ptree_head_bind_approx_mono; lia.
  - setoid_rewrite ret_equiv. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_mono. intro x.
    eapply sem_le_trans; [apply IH|].
    apply sem_bind_le_k; intro head.
    apply ptree_head_bind_approx_mono; lia.
Qed.

Theorem ptree_bind_split_le_global {A B} n m
    (t : ptree E MN A) (k : A -> ptree E MN B) :
  sem_le (ptree_bind_split_approx n m t k)
    (ptree_hitting_approx (MF := MF) (n + m) (observe (PTree.bind t k))).
Proof.
  revert t; induction n as [|n IH]; intro t;
    unfold ptree_bind_split_approx; rewrite observe_bind;
    remember (observe t) as ot eqn:Hobs; destruct ot;
    setoid_rewrite hitting_unfold; cbn [observe Nat.add].
  - setoid_rewrite ret_equiv. cbn [ptree_head_bind_approx].
    apply (proj1 (hitting_unfold m (observe (k r)))).
  - eapply sem_le_trans; [apply bind_zero_order|apply sem_zero_le].
  - setoid_rewrite ret_equiv. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_mono. intro x.
    eapply sem_le_trans; [apply bind_zero_order|apply sem_zero_le].
  - setoid_rewrite ret_equiv. cbn [ptree_head_bind_approx].
    eapply sem_le_trans; [|apply (proj1 (hitting_unfold (S n + m) (observe (k r))))].
    apply ptree_hitting_mono; lia.
  - apply IH.
  - setoid_rewrite ret_equiv. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_mono. intro x; apply IH.
Qed.

Hypothesis lub_cofinal : forall A (c d : nat -> MF A) out,
  sem_increasing c -> sem_increasing d ->
  (forall n, exists m, sem_le (c n) (d m)) ->
  (forall n, exists m, sem_le (d n) (c m)) ->
  (sem_lub c out <-> sem_lub d out).

Theorem ptree_bind_cofinal_all {A B}
    (t : ptree E MN A) (k : A -> ptree E MN B) :
  ptree_bind_cofinal (MF := MF) t k.
Proof.
  intro out. apply lub_cofinal.
  - apply ptree_hitting_increasing.
  - intro n. apply ptree_bind_diagonal_mono; lia.
  - intro n; exists n; apply ptree_bind_global_le_diagonal.
  - intro n; exists (n + n); apply ptree_bind_split_le_global.
Qed.
End BindScheduling.
