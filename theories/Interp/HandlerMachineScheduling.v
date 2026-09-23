(** Primitive handler machine / actual interpreter scheduling. No relation
    assumption or interpreter-preservation premise occurs in this bridge. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel BindScheduling.
From PTree.Interp Require Import HandlerMachine.
Set Implicit Arguments.
Unset Strict Implicit.

Section PrimitiveScheduling.
Context {E F MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Variable handler : forall X, E X -> ptree F MN X.
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance mixed_equiv A B (mu : MN A) :
  Proper (pointwise_relation A (@equiv B) ==> @equiv B)
    (@mixed_bind MN MF MX A B mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.
Local Notation unfold_target := (@BindScheduling.hitting_unfold F MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Local Lemma ret_equiv A B (x : A) (k : A -> MF B) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.

Definition handler_primitive_approx {A} n (c : @handler_config E F MN A) :=
  stable_hitting_approx (handler_primitive_kernel handler) n c.
Definition handler_tree_approx {A} n (c : @handler_config E F MN A) :=
  ptree_hitting_approx (MF := MF) n (observe (handler_config_tree handler c)).

Definition handler_residual_approx {A} n (c : @handler_config E F MN A) :=
  match n with O => sem_zero | S m => handler_primitive_approx m c end.

Lemma handler_primitive_source_unfold {A} n (t : ptree E MN A) :
  equiv (handler_primitive_approx n (SourceConfig t))
    (match observe t with
     | RetF a => sem_ret (FHRet a)
     | TauF u => handler_residual_approx n (SourceConfig u)
     | @VisF _ _ _ _ X e k => handler_residual_approx n (HandlerConfig (handler e) k)
     | @ProbF _ _ _ _ X mu k => mixed_bind mu (fun x => handler_residual_approx n (SourceConfig (k x)))
     end).
Proof.
  unfold handler_primitive_approx, stable_hitting_approx, handler_primitive_kernel.
  destruct (observe t) as [a|u|X e k|X mu k].
  - etransitivity; [apply ret_equiv|]. rewrite stable_target_stableE. reflexivity.
  - etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
  - etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
  - etransitivity; [apply mixed_bind_assoc_order|].
    apply mixed_equiv. intro x. etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
Qed.

Lemma handler_primitive_active_unfold {A X} n (active : ptree F MN X)
    (k : X -> ptree E MN A) :
  equiv (handler_primitive_approx n (HandlerConfig active k))
    (match observe active with
     | RetF x => handler_residual_approx n (SourceConfig (k x))
     | TauF u => handler_residual_approx n (HandlerConfig u k)
     | @VisF _ _ _ _ Y e d => sem_ret
         (FHVis e (fun y => PTree.bind (d y) (fun x => PTree.interp handler (k x))))
     | @ProbF _ _ _ _ Y mu d => mixed_bind mu (fun y => handler_residual_approx n (HandlerConfig (d y) k))
     end).
Proof.
  unfold handler_primitive_approx, stable_hitting_approx, handler_primitive_kernel.
  destruct (observe active) as [x|u|Y e d|Y mu d].
  - etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
  - etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
  - etransitivity; [apply ret_equiv|]. rewrite stable_target_stableE. reflexivity.
  - etransitivity; [apply mixed_bind_assoc_order|].
    apply mixed_equiv. intro y. etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
Qed.

Lemma handler_primitive_mono {A} n m (c : @handler_config E F MN A) :
  n <= m -> sem_le (handler_primitive_approx n c) (handler_primitive_approx m c).
Proof. apply stable_hitting_mono. Qed.

Theorem handler_primitive_le_tree {A} n (c : @handler_config E F MN A) :
  sem_le (handler_primitive_approx n c) (handler_tree_approx n c).
Proof.
  revert c. induction n as [|n IH]; intros [t|X active k];
    unfold handler_tree_approx; cbn [handler_config_tree].
  - setoid_rewrite handler_primitive_source_unfold. rewrite observe_interp.
    destruct (observe t); setoid_rewrite unfold_target; cbn [handler_residual_approx observe].
    + apply sem_le_refl.
    + apply sem_zero_le.
    + apply sem_zero_le.
    + apply mixed_bind_le_k. intro x. apply sem_le_refl.
  - setoid_rewrite handler_primitive_active_unfold. rewrite observe_bind.
    destruct (observe active); cbn [handler_residual_approx observe].
    + apply sem_zero_le.
    + setoid_rewrite unfold_target. apply sem_zero_le.
    + setoid_rewrite unfold_target. apply sem_le_refl.
    + setoid_rewrite unfold_target. apply mixed_bind_le_k. intro x. apply sem_le_refl.
  - setoid_rewrite handler_primitive_source_unfold. rewrite observe_interp.
    destruct (observe t); setoid_rewrite unfold_target; cbn [handler_residual_approx observe].
    + apply sem_le_refl.
    + apply IH.
    + apply IH.
    + apply mixed_bind_le_k. intro x. apply IH.
  - setoid_rewrite handler_primitive_active_unfold. rewrite observe_bind.
    destruct (observe active); cbn [handler_residual_approx observe].
    + eapply sem_le_trans; [apply IH|]. apply ptree_hitting_mono. lia.
    + setoid_rewrite unfold_target. apply IH.
    + setoid_rewrite unfold_target. apply sem_le_refl.
    + setoid_rewrite unfold_target. apply mixed_bind_le_k. intro x. apply IH.
Qed.

Lemma handler_tree_le_primitive_phases {A} n :
  (forall t : ptree E MN A,
    sem_le (handler_tree_approx n (SourceConfig t))
      (handler_primitive_approx (2*n+1) (SourceConfig t))) /\
  (forall X (active : ptree F MN X) (k : X -> ptree E MN A),
    sem_le (handler_tree_approx n (HandlerConfig active k))
      (handler_primitive_approx (2*n+2) (HandlerConfig active k))).
Proof.
  induction n as [|n [IHsource IHhandler]].
  - assert (Hs : forall t : ptree E MN A,
      sem_le (handler_tree_approx 0 (SourceConfig t))
        (handler_primitive_approx 1 (SourceConfig t))).
    { intro t. unfold handler_tree_approx. cbn [handler_config_tree].
      rewrite observe_interp. setoid_rewrite handler_primitive_source_unfold.
      destruct (observe t); setoid_rewrite unfold_target; cbn [handler_residual_approx observe].
      - apply sem_le_refl.
      - apply sem_zero_le.
      - apply sem_zero_le.
      - apply mixed_bind_le_k. intro x. apply sem_zero_le. }
    split; [exact Hs|]. intros X active k.
    unfold handler_tree_approx. cbn [handler_config_tree]. rewrite observe_bind.
    setoid_rewrite handler_primitive_active_unfold.
    destruct (observe active); cbn [handler_residual_approx observe].
    + apply Hs.
    + setoid_rewrite unfold_target. apply sem_zero_le.
    + setoid_rewrite unfold_target. apply sem_le_refl.
    + setoid_rewrite unfold_target. apply mixed_bind_le_k. intro x. apply sem_zero_le.
  - assert (Hs : forall t : ptree E MN A,
      sem_le (handler_tree_approx (S n) (SourceConfig t))
        (handler_primitive_approx (2*S n+1) (SourceConfig t))).
    { intro t. replace (2*S n+1) with (S (2*n+2)) by lia.
      unfold handler_tree_approx. cbn [handler_config_tree]. rewrite observe_interp.
      setoid_rewrite handler_primitive_source_unfold.
      destruct (observe t); setoid_rewrite unfold_target; cbn [handler_residual_approx observe].
      - apply sem_le_refl.
      - eapply sem_le_trans; [apply IHsource|]. apply handler_primitive_mono. lia.
      - apply IHhandler.
      - apply mixed_bind_le_k. intro x.
        eapply sem_le_trans; [apply IHsource|]. apply handler_primitive_mono. lia. }
    split; [exact Hs|]. intros X active k.
    replace (2*S n+2) with (S (2*S n+1)) by lia.
    unfold handler_tree_approx. cbn [handler_config_tree]. rewrite observe_bind.
    setoid_rewrite handler_primitive_active_unfold.
    destruct (observe active); cbn [handler_residual_approx observe].
    + apply Hs.
    + setoid_rewrite unfold_target.
      eapply sem_le_trans; [apply IHhandler|]. apply handler_primitive_mono. lia.
    + setoid_rewrite unfold_target. apply sem_le_refl.
    + setoid_rewrite unfold_target. apply mixed_bind_le_k. intro x.
      eapply sem_le_trans; [apply IHhandler|]. apply handler_primitive_mono. lia.
Qed.

Theorem handler_tree_le_primitive {A} n (c : @handler_config E F MN A) :
  sem_le (handler_tree_approx n c) (handler_primitive_approx (2*n+2) c).
Proof.
  destruct c as [t|X active k].
  - eapply sem_le_trans; [apply (proj1 (handler_tree_le_primitive_phases n))|].
    apply handler_primitive_mono. lia.
  - apply (proj2 (handler_tree_le_primitive_phases n)).
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.

(** Same complete limits, not a conclusion obtained from observable
    equality implying approximation order (which is false in FreeOmega). *)
Theorem handler_primitive_hitting_iff {A} (c : @handler_config E F MN A) out :
  stable_hitting (handler_primitive_kernel handler) c out <->
  ptree_stable_hitting (MF := MF) (observe (handler_config_tree handler c)) out.
Proof.
  unfold stable_hitting, ptree_stable_hitting, stable_hitting.
  apply sem_lub_cofinal.
  - apply stable_hitting_increasing.
  - apply ptree_hitting_increasing.
  - intro n. exists n. apply handler_primitive_le_tree.
  - intro n. exists (2*n+2). apply handler_tree_le_primitive.
Qed.
End PrimitiveScheduling.
