(** Direct iteration machine: loop states are ordinary semantic states,
    never responses of an auxiliary visible event. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms RelationClasses Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel BindScheduling.
From PTree.Interp Require Import HandlerMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.

Section Machine.
Context {E MN MF : Type -> Type} `{FI : SemanticMeasure MF}
  `{MX : MixedMeasure MN MF}.
Context {I A : Type}.
Variable step : I -> ptree E MN (I+A).

Definition iter_finish (v : I+A) : ptree E MN A :=
  match v with inl i => Tau (PTree.iter step i) | inr a => Ret a end.
Definition iter_active (t : ptree E MN (I+A)) := PTree.bind t iter_finish.

Definition iter_head_result (h : stable_head E MN (I+A)) :
    stable_target (ptree E MN (I+A)) (stable_head E MN A) :=
  match h with
  | FHRet (inl i) => SHInternal (step i)
  | FHRet (inr a) => SHStable (FHRet a)
  | @FHVis _ _ _ X e k => SHStable (FHVis e (fun x => iter_active (k x)))
  end.

Definition iter_primitive_kernel (t : ptree E MN (I+A)) :
    MF (stable_target (ptree E MN (I+A)) (stable_head E MN A)) :=
  match observe t with
  | RetF v => sem_ret (iter_head_result (FHRet v))
  | TauF u => sem_ret (SHInternal u)
  | @VisF _ _ _ _ X e k => sem_ret (iter_head_result (FHVis e k))
  | @ProbF _ _ _ _ X mu k => mixed_bind mu (fun x => sem_ret (SHInternal (k x)))
  end.
End Machine.

Section Scheduling.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Context {I A : Type} (step : I -> ptree E MN (I+A)).
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance iter_mixed_equiv X Y (mu : MN X) :
  Proper (pointwise_relation X (@equiv Y) ==> @equiv Y)
    (@mixed_bind MN MF MX X Y mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.
Local Notation hit_unfold := (@BindScheduling.hitting_unfold E MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Local Lemma ret_equiv X Y (x : X) (k : X -> MF Y) :
  equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma zero_equiv X Y (k : X -> MF Y) :
  equiv (sem_bind sem_zero k) sem_zero.
Proof. split; [apply sem_bind_zero_order|apply sem_zero_le]. Qed.
Local Lemma mixed_assoc_equiv X Y Z (mu : MN X) (k : X -> MF Y) (h : Y -> MF Z) :
  equiv (sem_bind (mixed_bind mu k) h) (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

Definition iter_primitive_approx n t :=
  stable_hitting_approx (iter_primitive_kernel step) n t.
Definition iter_after n t := match n with O => sem_zero | S m => iter_primitive_approx m t end.

Lemma iter_primitive_unfold n t :
  equiv (iter_primitive_approx n t)
    (match observe t with
     | RetF (inl i) => iter_after n (step i)
     | RetF (inr a) => sem_ret (FHRet a)
     | TauF u => iter_after n u
     | @VisF _ _ _ _ X e k => sem_ret (FHVis e (fun x => iter_active step (k x)))
     | @ProbF _ _ _ _ X mu k => mixed_bind mu (fun x => iter_after n (k x))
     end).
Proof.
  unfold iter_primitive_approx, stable_hitting_approx, iter_primitive_kernel.
  destruct (observe t) as [[i|a]|u|X e k|X mu k]; cbn [iter_head_result].
  all: try (etransitivity; [apply ret_equiv|]; destruct n; reflexivity).
  etransitivity; [apply mixed_bind_assoc_order|].
  apply iter_mixed_equiv. intro x.
  etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
Qed.

Lemma iter_primitive_tree n t :
  equiv (iter_primitive_approx n t)
    (ptree_hitting_approx (MF := MF) n (observe (iter_active step t))).
Proof.
  revert t. induction n as [|n IH]; intro t.
  all: setoid_rewrite iter_primitive_unfold.
  all: unfold iter_active; rewrite observe_bind.
  all: destruct (observe t) as [[i|a]|u|X e k|X mu k];
    cbn [iter_finish observe]; setoid_rewrite hit_unfold; cbn [iter_after].
  all: try reflexivity.
  - exact (IH (step i)).
  - apply IH.
  - apply iter_mixed_equiv. intro x. apply IH.
Qed.
End Scheduling.

Section Acceleration.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Context {I A : Type} (step : I -> ptree E MN (I+A)).
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Existing Instance iter_mixed_equiv.
Local Notation hit_unfold := (@BindScheduling.hitting_unfold E MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).

Definition iter_phase_kernel m t :=
  sem_bind (ptree_hitting_approx (MF := MF) m (observe t))
    (fun h => sem_ret (iter_head_result step h)).
Definition iter_phase_grid n m t := stable_hitting_approx (iter_phase_kernel m) n t.
Definition iter_phase_split j n m t :=
  sem_bind (ptree_hitting_approx (MF := MF) j (observe t))
    (fun h => stable_target_approx (iter_phase_kernel m) n (iter_head_result step h)).
Definition iter_phase_after n m t :=
  match n with O => sem_zero | S r => iter_phase_grid r m t end.

Lemma iter_phase_grid_split n m t :
  equiv (iter_phase_grid n m t) (iter_phase_split m n m t).
Proof.
  unfold iter_phase_grid, stable_hitting_approx, iter_phase_kernel, iter_phase_split.
  etransitivity; [apply finite_head_bind_assoc|].
  apply BindScheduling.bind_equiv_Proper; [reflexivity|intro h; apply ret_equiv].
Qed.

Lemma iter_phase_split_inner_mono j j' n m t :
  j <= j' -> sem_le (iter_phase_split j n m t) (iter_phase_split j' n m t).
Proof. intro H. apply sem_bind_le_mu. apply ptree_hitting_mono. exact H. Qed.
Lemma iter_phase_split_outer_step j n m t :
  sem_le (iter_phase_split j n m t) (iter_phase_split j (S n) m t).
Proof. apply sem_bind_le_k. intro h. apply stable_target_approx_increasing. Qed.
Local Lemma phase_internalE n m t :
  stable_target_approx (iter_phase_kernel m) n (SHInternal t) = iter_phase_after n m t.
Proof. destruct n; reflexivity. Qed.

Lemma iter_phase_split_le_primitive j n m bound
    (Hpost : forall t, sem_le (iter_phase_after n m t) (iter_primitive_approx step bound t)) :
  forall t, sem_le (iter_phase_split j n m t) (iter_primitive_approx step (j+bound+1) t).
Proof.
  induction j as [|j IH]; intro t;
    replace (0+bound+1) with (S bound) by lia;
    try replace (S j+bound+1) with (S (S j+bound)) by lia.
  all: unfold iter_phase_split; setoid_rewrite hit_unfold; setoid_rewrite iter_primitive_unfold.
  all: destruct (observe t) as [[i|a]|u|X e k|X mu k];
    cbn [iter_after iter_head_result].
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite phase_internalE. exact (Hpost (step i)).
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite zero_equiv. apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    setoid_rewrite zero_equiv. apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite phase_internalE.
    eapply sem_le_trans; [apply Hpost|]. apply stable_hitting_mono. lia.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - eapply sem_le_trans; [apply IH|]. apply stable_hitting_mono. lia.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply IH|]. apply stable_hitting_mono. lia.
Qed.

Lemma iter_phase_grid_le_primitive n m t :
  sem_le (iter_phase_grid n m t) (iter_primitive_approx step ((n+1)*(m+1)) t).
Proof.
  revert t. induction n as [|n IH]; intro t; setoid_rewrite iter_phase_grid_split.
  - replace ((0+1)*(m+1)) with (m+0+1) by lia.
    apply iter_phase_split_le_primitive. intro u. apply sem_zero_le.
  - replace ((S n+1)*(m+1)) with (m+(n+1)*(m+1)+1) by lia.
    apply iter_phase_split_le_primitive. exact IH.
Qed.

Lemma iter_primitive_le_phase_split n m :
  n <= m -> forall t, sem_le (iter_primitive_approx step n t) (iter_phase_split n n m t).
Proof.
  induction n as [|n IH]; intro Hnm; intro t.
  all: setoid_rewrite iter_primitive_unfold; unfold iter_phase_split; setoid_rewrite hit_unfold.
  all: destruct (observe t) as [[i|a]|u|X e k|X mu k]; cbn [iter_after iter_head_result].
  - apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x. apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite phase_internalE. cbn [iter_phase_after].
    setoid_rewrite iter_phase_grid_split.
    eapply sem_le_trans; [apply (IH ltac:(lia))|].
    apply iter_phase_split_inner_mono. lia.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - eapply sem_le_trans; [apply (IH ltac:(lia))|].
    apply iter_phase_split_outer_step.
  - setoid_rewrite ret_equiv. cbn [iter_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc_equiv. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply (IH ltac:(lia))|]. apply iter_phase_split_outer_step.
Qed.

Lemma iter_primitive_le_phase_grid n t :
  sem_le (iter_primitive_approx step n t) (iter_phase_grid n n t).
Proof. setoid_rewrite iter_phase_grid_split. apply iter_primitive_le_phase_split. lia. Qed.

Lemma iter_phase_kernel_increasing t : sem_increasing (fun m => iter_phase_kernel m t).
Proof. intro m. apply sem_bind_le_mu. apply ptree_hitting_increasing. Qed.
Lemma iter_phase_grid_inner_increasing n t : sem_increasing (fun m => iter_phase_grid n m t).
Proof.
  intro m. unfold iter_phase_grid, stable_hitting_approx.
  eapply sem_le_trans; [apply sem_bind_le_mu; apply iter_phase_kernel_increasing|].
  apply sem_bind_le_k. intro target. apply HandlerMachineAcceleration.target_kernel_mono.
  intro u. apply iter_phase_kernel_increasing.
Qed.
Lemma iter_phase_grid_outer_increasing m t : sem_increasing (fun n => iter_phase_grid n m t).
Proof. apply stable_hitting_increasing. Qed.
Lemma iter_phase_diagonal_increasing t : sem_increasing (fun n => iter_phase_grid n n t).
Proof.
  intro n. eapply sem_le_trans; [apply iter_phase_grid_inner_increasing|].
  apply iter_phase_grid_outer_increasing.
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.
Lemma iter_phase_diagonal_tree t out :
  sem_lub (fun n => iter_phase_grid n n t) out <->
  ptree_stable_hitting (MF := MF) (observe (iter_active step t)) out.
Proof.
  unfold ptree_stable_hitting, stable_hitting. apply sem_lub_cofinal.
  - apply iter_phase_diagonal_increasing.
  - apply ptree_hitting_increasing.
  - intro n. exists ((n+1)*(n+1)).
    eapply sem_le_trans; [apply iter_phase_grid_le_primitive|].
    apply (proj1 (iter_primitive_tree step _ t)).
  - intro n. exists n. eapply sem_le_trans.
    + apply (proj2 (iter_primitive_tree step n t)).
    + apply iter_primitive_le_phase_grid.
Qed.

Context `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Definition iter_machine_kernel t :=
  sem_bind (handler_complete_front t) (fun h => sem_ret (iter_head_result step h)).
Lemma iter_phase_kernel_lub t :
  sem_lub (fun m => iter_phase_kernel m t) (iter_machine_kernel t).
Proof.
  apply sem_bind_lub; [apply ptree_hitting_increasing|apply handler_complete_front_hitting].
Qed.
Lemma iter_phase_grid_row_lub n t :
  sem_lub (fun m => iter_phase_grid n m t)
    (stable_hitting_approx iter_machine_kernel n t).
Proof.
  unfold iter_phase_grid, stable_hitting_approx. apply sem_bind_diagonal_lub.
  - apply iter_phase_kernel_increasing.
  - intros target m. apply HandlerMachineAcceleration.target_kernel_mono.
    intro u. apply iter_phase_kernel_increasing.
  - apply iter_phase_kernel_lub.
  - intro target. apply HandlerMachineAcceleration.target_kernel_lub;
      [apply iter_phase_kernel_increasing|apply iter_phase_kernel_lub].
Qed.

Theorem iter_machine_hitting_sound t out :
  stable_hitting iter_machine_kernel t out ->
  ptree_stable_hitting (MF := MF) (observe (iter_active step t)) out.
Proof.
  intro H. apply (proj1 (iter_phase_diagonal_tree t out)).
  eapply (sem_lub_double_diagonal (SI := FI) (SO := FO))
    with (grid := fun n m => iter_phase_grid n m t)
         (row_out := fun n => stable_hitting_approx iter_machine_kernel n t).
  - intro n. apply iter_phase_grid_inner_increasing.
  - intro m. apply iter_phase_grid_outer_increasing.
  - intro n. apply iter_phase_grid_row_lub.
  - exact H.
Qed.
End Acceleration.
