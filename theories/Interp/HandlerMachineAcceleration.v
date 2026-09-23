(** Complete-frontier phases are an acceleration of the physical handler
    machine. Finite schedules are compared in approximation order; no
    observable-equality-to-order reflection is used. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel BindScheduling.
From PTree.Interp Require Import HandlerMachine HandlerMachineScheduling.
Set Implicit Arguments.
Unset Strict Implicit.

Section Acceleration.
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
Local Notation hit_unfold := (fun G => @BindScheduling.hitting_unfold G MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Local Lemma ret_equiv A B (x : A) (k : A -> MF B) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma zero_equiv A B (k : A -> MF B) :
  equiv (sem_bind sem_zero k) sem_zero.
Proof. split; [apply sem_bind_zero_order|apply sem_zero_le]. Qed.
Local Lemma mixed_assoc_equiv A B C (mu : MN A) (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h) (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

(** Only finite native-generated frontiers need order-level associativity.
    It is derived, not added as an arbitrary-MF capability. *)
Lemma finite_head_bind_assoc {G A B C} n (t : ptree' G MN A)
    (k : stable_head G MN A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (sem_bind (ptree_hitting_approx (MF := MF) n t) k) h)
    (sem_bind (ptree_hitting_approx (MF := MF) n t) (fun x => sem_bind (k x) h)).
Proof.
  revert t. induction n as [|n IH]; intros [a|u|X e c|X mu c];
    setoid_rewrite (hit_unfold G); cbn [observe].
  - setoid_rewrite ret_equiv. reflexivity.
  - repeat setoid_rewrite zero_equiv. reflexivity.
  - setoid_rewrite ret_equiv. reflexivity.
  - repeat setoid_rewrite mixed_assoc_equiv. apply mixed_equiv. intro x.
    repeat setoid_rewrite zero_equiv. reflexivity.
  - setoid_rewrite ret_equiv. reflexivity.
  - apply IH.
  - setoid_rewrite ret_equiv. reflexivity.
  - repeat setoid_rewrite mixed_assoc_equiv. apply mixed_equiv. intro x. apply IH.
Qed.

Definition handler_phase_kernel {A} m (c : @handler_config E F MN A) :
    MF (stable_target (@handler_config E F MN A) (stable_head F MN A)) :=
  match c with
  | SourceConfig t => sem_bind (ptree_hitting_approx (MF := MF) m (observe t))
      (fun h => sem_ret (source_front_result handler h))
  | @HandlerConfig _ _ _ _ X active k =>
      sem_bind (ptree_hitting_approx (MF := MF) m (observe active))
        (fun h => sem_ret (handler_front_result handler k h))
  end.

Definition handler_phase_grid {A} n m (c : @handler_config E F MN A) :=
  stable_hitting_approx (handler_phase_kernel m) n c.

Definition handler_phase_split {A} j n m (c : @handler_config E F MN A) :=
  match c with
  | SourceConfig t => sem_bind (ptree_hitting_approx (MF := MF) j (observe t))
      (fun h => stable_target_approx (handler_phase_kernel m) n (source_front_result handler h))
  | @HandlerConfig _ _ _ _ X active k =>
      sem_bind (ptree_hitting_approx (MF := MF) j (observe active))
        (fun h => stable_target_approx (handler_phase_kernel m) n (handler_front_result handler k h))
  end.

Lemma handler_phase_grid_split {A} n m (c : @handler_config E F MN A) :
  equiv (handler_phase_grid n m c) (handler_phase_split m n m c).
Proof.
  destruct c as [t|X active k]; unfold handler_phase_grid, stable_hitting_approx,
    handler_phase_kernel, handler_phase_split.
  all: etransitivity; [apply finite_head_bind_assoc|].
  all: apply BindScheduling.bind_equiv_Proper;
      [reflexivity|intro h; apply ret_equiv].
Qed.

Lemma handler_phase_split_inner_mono {A} j j' n m (c : @handler_config E F MN A) :
  j <= j' -> sem_le (handler_phase_split j n m c) (handler_phase_split j' n m c).
Proof.
  intro H. destruct c; unfold handler_phase_split;
    apply sem_bind_le_mu; apply ptree_hitting_mono; exact H.
Qed.

Lemma handler_phase_split_outer_step {A} j n m (c : @handler_config E F MN A) :
  sem_le (handler_phase_split j n m c) (handler_phase_split j (S n) m c).
Proof.
  destruct c; unfold handler_phase_split;
    apply sem_bind_le_k; intro h; apply stable_target_approx_increasing.
Qed.

Definition handler_phase_after {A} n m (c : @handler_config E F MN A) :=
  match n with O => sem_zero | S r => handler_phase_grid r m c end.

Local Lemma phase_internalE {A} n m (c : @handler_config E F MN A) :
  stable_target_approx (handler_phase_kernel m) n (SHInternal c) =
    handler_phase_after n m c.
Proof. destruct n; reflexivity. Qed.

Lemma handler_phase_split_le_primitive {A} j n m bound
    (Hpost : forall c : @handler_config E F MN A,
      sem_le (handler_phase_after n m c) (handler_primitive_approx handler bound c)) :
  forall c : @handler_config E F MN A,
  sem_le (handler_phase_split j n m c) (handler_primitive_approx handler (j+bound+1) c).
Proof.
  induction j as [|j IH]; intros [t|X active k];
    replace (0+bound+1) with (S bound) by lia;
    try replace (S j+bound+1) with (S (S j+bound)) by lia.
  - unfold handler_phase_split. setoid_rewrite (hit_unfold E).
    setoid_rewrite handler_primitive_source_unfold.
    destruct (observe t); cbn [handler_residual_approx source_front_result].
    + setoid_rewrite ret_equiv. cbn [source_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + setoid_rewrite zero_equiv. apply sem_zero_le.
    + setoid_rewrite ret_equiv. cbn [source_front_result]. rewrite phase_internalE. apply Hpost.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      setoid_rewrite zero_equiv. apply sem_zero_le.
  - unfold handler_phase_split. setoid_rewrite (hit_unfold F).
    setoid_rewrite handler_primitive_active_unfold.
    destruct (observe active); cbn [handler_residual_approx handler_front_result].
    + setoid_rewrite ret_equiv. cbn [handler_front_result]. rewrite phase_internalE. apply Hpost.
    + setoid_rewrite zero_equiv. apply sem_zero_le.
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      setoid_rewrite zero_equiv. apply sem_zero_le.
  - unfold handler_phase_split. setoid_rewrite (hit_unfold E).
    setoid_rewrite handler_primitive_source_unfold.
    destruct (observe t); cbn [handler_residual_approx source_front_result].
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + eapply sem_le_trans; [apply (IH (SourceConfig _))|]. apply handler_primitive_mono. lia.
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite phase_internalE. eapply sem_le_trans; [apply Hpost|]. apply handler_primitive_mono. lia.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      eapply sem_le_trans; [apply (IH (SourceConfig _))|]. apply handler_primitive_mono. lia.
  - unfold handler_phase_split. setoid_rewrite (hit_unfold F).
    setoid_rewrite handler_primitive_active_unfold.
    destruct (observe active); cbn [handler_residual_approx handler_front_result].
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite phase_internalE. eapply sem_le_trans; [apply Hpost|]. apply handler_primitive_mono. lia.
    + eapply sem_le_trans; [apply (IH (HandlerConfig _ k))|]. apply handler_primitive_mono. lia.
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      eapply sem_le_trans; [apply (IH (HandlerConfig _ k))|]. apply handler_primitive_mono. lia.
Qed.

Theorem handler_phase_grid_le_primitive {A} n m (c : @handler_config E F MN A) :
  sem_le (handler_phase_grid n m c)
    (handler_primitive_approx handler ((n+1)*(m+1)) c).
Proof.
  revert c. induction n as [|n IH]; intro c; setoid_rewrite handler_phase_grid_split.
  - replace ((0+1)*(m+1)) with (m+0+1) by lia.
    apply handler_phase_split_le_primitive. intro d. apply sem_zero_le.
  - replace ((S n+1)*(m+1)) with (m+(n+1)*(m+1)+1) by lia.
    apply handler_phase_split_le_primitive. exact IH.
Qed.

Lemma handler_primitive_le_phase_split {A} n m :
  n <= m ->
  forall c : @handler_config E F MN A,
  sem_le (handler_primitive_approx handler n c) (handler_phase_split n n m c).
Proof.
  induction n as [|n IH]; intro Hnm; intros [t|X active k].
  - setoid_rewrite handler_primitive_source_unfold. unfold handler_phase_split.
    setoid_rewrite (hit_unfold E).
    destruct (observe t); cbn [handler_residual_approx source_front_result].
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + apply sem_zero_le.
    + apply sem_zero_le.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x. apply sem_zero_le.
  - setoid_rewrite handler_primitive_active_unfold. unfold handler_phase_split.
    setoid_rewrite (hit_unfold F).
    destruct (observe active); cbn [handler_residual_approx handler_front_result].
    + apply sem_zero_le.
    + apply sem_zero_le.
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x. apply sem_zero_le.
  - setoid_rewrite handler_primitive_source_unfold. unfold handler_phase_split.
    setoid_rewrite (hit_unfold E).
    destruct (observe t); cbn [handler_residual_approx source_front_result].
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + eapply sem_le_trans; [apply (IH ltac:(lia) (SourceConfig _))|]. apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
    + setoid_rewrite ret_equiv. cbn [source_front_result]. rewrite phase_internalE.
      cbn [handler_phase_after].
      setoid_rewrite handler_phase_grid_split.
      eapply sem_le_trans; [apply (IH ltac:(lia) (HandlerConfig _ _))|].
      apply handler_phase_split_inner_mono. lia.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      eapply sem_le_trans; [apply (IH ltac:(lia) (SourceConfig _))|]. apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
  - setoid_rewrite handler_primitive_active_unfold. unfold handler_phase_split.
    setoid_rewrite (hit_unfold F).
    destruct (observe active); cbn [handler_residual_approx handler_front_result].
    + setoid_rewrite ret_equiv. cbn [handler_front_result]. rewrite phase_internalE.
      cbn [handler_phase_after].
      setoid_rewrite handler_phase_grid_split.
      eapply sem_le_trans; [apply (IH ltac:(lia) (SourceConfig _))|].
      apply handler_phase_split_inner_mono. lia.
    + eapply sem_le_trans; [apply (IH ltac:(lia) (HandlerConfig _ k))|]. apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
    + setoid_rewrite ret_equiv. cbn [source_front_result handler_front_result]. rewrite stable_target_stableE. apply sem_le_refl.
    + setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
      eapply sem_le_trans; [apply (IH ltac:(lia) (HandlerConfig _ k))|]. apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
Qed.
Lemma handler_primitive_le_phase_grid {A} n (c : @handler_config E F MN A) :
  sem_le (handler_primitive_approx handler n c) (handler_phase_grid n n c).
Proof. setoid_rewrite handler_phase_grid_split. apply handler_primitive_le_phase_split. lia. Qed.

Local Lemma target_kernel_mono {S A}
    (k l : S -> MF (stable_target S A))
    (Hkl : forall s, sem_le (k s) (l s)) n target :
  sem_le (stable_target_approx k n target) (stable_target_approx l n target).
Proof.
  revert target. induction n as [|n IH]; intros [a|s]; cbn [stable_target_approx];
    try apply sem_le_refl.
  eapply sem_le_trans; [apply sem_bind_le_mu; apply Hkl|].
  apply sem_bind_le_k. exact IH.
Qed.

Lemma handler_phase_kernel_increasing {A} (c : @handler_config E F MN A) :
  sem_increasing (fun m => handler_phase_kernel m c).
Proof.
  intro m. destruct c; unfold handler_phase_kernel; apply sem_bind_le_mu;
    apply ptree_hitting_increasing.
Qed.

Lemma handler_phase_grid_inner_increasing {A} n (c : @handler_config E F MN A) :
  sem_increasing (fun m => handler_phase_grid n m c).
Proof.
  intro m. unfold handler_phase_grid, stable_hitting_approx.
  eapply sem_le_trans; [apply sem_bind_le_mu; apply handler_phase_kernel_increasing|].
  apply sem_bind_le_k. intro target. apply target_kernel_mono.
  intro d. apply handler_phase_kernel_increasing.
Qed.

Lemma handler_phase_grid_outer_increasing {A} m (c : @handler_config E F MN A) :
  sem_increasing (fun n => handler_phase_grid n m c).
Proof. apply stable_hitting_increasing. Qed.

Lemma handler_phase_diagonal_increasing {A} (c : @handler_config E F MN A) :
  sem_increasing (fun n => handler_phase_grid n n c).
Proof.
  intro n. eapply sem_le_trans; [apply handler_phase_grid_inner_increasing|].
  apply handler_phase_grid_outer_increasing.
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.

Theorem handler_phase_diagonal_hitting_iff {A} (c : @handler_config E F MN A) out :
  sem_lub (fun n => handler_phase_grid n n c) out <->
  stable_hitting (handler_primitive_kernel handler) c out.
Proof.
  unfold stable_hitting. apply sem_lub_cofinal.
  - apply handler_phase_diagonal_increasing.
  - apply stable_hitting_increasing.
  - intro n. exists ((n+1)*(n+1)). apply handler_phase_grid_le_primitive.
  - intro n. exists n. apply handler_primitive_le_phase_grid.
Qed.

Context `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Lemma handler_phase_kernel_lub {A} (c : @handler_config E F MN A) :
  sem_lub (fun m => handler_phase_kernel m c) (handler_machine_kernel handler c).
Proof.
  destruct c; unfold handler_phase_kernel, handler_machine_kernel.
  all: apply sem_bind_lub; [apply ptree_hitting_increasing|apply handler_complete_front_hitting].
Qed.

Local Lemma target_kernel_lub {S A}
    (ks : nat -> S -> MF (stable_target S A)) (k : S -> MF (stable_target S A))
    (Hi : forall s, sem_increasing (fun m => ks m s))
    (Hl : forall s, sem_lub (fun m => ks m s) (k s)) n target :
  sem_lub (fun m => stable_target_approx (ks m) n target) (stable_target_approx k n target).
Proof.
  revert target. induction n as [|n IH]; intros [a|s]; cbn [stable_target_approx];
    try apply sem_lub_constant.
  apply sem_bind_diagonal_lub.
  - apply Hi.
  - intros t m. apply target_kernel_mono. intro d. apply Hi.
  - apply Hl.
  - apply IH.
Qed.

Lemma handler_phase_grid_row_lub {A} n (c : @handler_config E F MN A) :
  sem_lub (fun m => handler_phase_grid n m c)
    (stable_hitting_approx (handler_machine_kernel handler) n c).
Proof.
  unfold handler_phase_grid, stable_hitting_approx. apply sem_bind_diagonal_lub.
  - apply handler_phase_kernel_increasing.
  - intros t m. apply target_kernel_mono. intro d. apply handler_phase_kernel_increasing.
  - apply handler_phase_kernel_lub.
  - intro t. apply target_kernel_lub;
      [apply handler_phase_kernel_increasing|apply handler_phase_kernel_lub].
Qed.

(** A complete macro-machine witness is a witness of the actual interpreter.
    Both schedules are compared through finite approximants and cofinality;
    no semantic-equality reflection or handler-preservation premise is used. *)
Theorem handler_machine_hitting_sound {A} (c : @handler_config E F MN A) out :
  stable_hitting (handler_machine_kernel handler) c out ->
  ptree_stable_hitting (MF := MF) (observe (handler_config_tree handler c)) out.
Proof.
  intro H. apply (proj1 (handler_primitive_hitting_iff (Directed := Directed) handler c out)).
  apply (proj1 (handler_phase_diagonal_hitting_iff c out)).
  eapply (sem_lub_double_diagonal (SI := FI) (SO := FO))
    with (grid := fun n m => handler_phase_grid n m c)
         (row_out := fun n => stable_hitting_approx (handler_machine_kernel handler) n c).
  - intro n. apply handler_phase_grid_inner_increasing.
  - intro m. apply handler_phase_grid_outer_increasing.
  - intro n. apply handler_phase_grid_row_lub.
  - exact H.
Qed.
End Acceleration.
