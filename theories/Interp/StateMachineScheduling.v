(** State updates do not commute past events. They are carried in machine
    configurations, while only finite internal Tau/Prob segments accelerate. *)
Set Universe Polymorphism.
From Coq Require Import Morphisms RelationClasses Lia.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel BindScheduling.
From PTree.Interp Require Import State StateMachine HandlerMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.

Section Scheduling.
Context {St : Type} {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI} `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Local Notation cfg A := (@state_config St E MN A).
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.le_equiv_Proper.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.
#[local] Instance mixed_equiv A B (mu : MN A) :
  Proper (pointwise_relation A (@equiv B) ==> @equiv B) (@mixed_bind MN MF MX A B mu).
Proof. apply BindScheduling.mixed_equiv_Proper. exact (@mixed_bind_le_k MN MF FI MX FO MO). Qed.
Local Notation hit_unfold := (fun G => @BindScheduling.hitting_unfold G MN MF FI MX FO Ord
  (@sem_bind_ret_order MF FI FO BO) (@mixed_bind_assoc_order MN MF FI MX FO MO)
  (@mixed_bind_le_k MN MF FI MX FO MO)).
Local Lemma ret_equiv A B (x : A) (k : A -> MF B) : equiv (sem_bind (sem_ret x) k) (k x).
Proof. apply sem_bind_ret_order. Qed.
Local Lemma zero_equiv A B (k : A -> MF B) : equiv (sem_bind sem_zero k) sem_zero.
Proof. split; [apply sem_bind_zero_order|apply sem_zero_le]. Qed.
Local Lemma mixed_assoc A B C (mu : MN A) (k : A -> MF B) (h : B -> MF C) :
  equiv (sem_bind (mixed_bind mu k) h) (mixed_bind mu (fun x => sem_bind (k x) h)).
Proof. apply mixed_bind_assoc_order. Qed.

Definition state_primitive_approx {A} n (c : cfg A) :=
  stable_hitting_approx state_primitive_kernel n c.
Definition state_after {A} n (c : cfg A) :=
  match n with O => sem_zero | S m => state_primitive_approx m c end.

Lemma state_primitive_unfold {A} n s (t : ptree (stateE St +' E) MN A) :
  equiv (state_primitive_approx n (s,t))
    (match observe t with
     | RetF a => sem_ret (FHRet (s,a))
     | TauF u => state_after n (s,u)
     | @VisF _ _ _ _ X e k => match e with
         | inl1 se => let '(s',x) := state_response se s in state_after n (s',k x)
         | inr1 fe => sem_ret (FHVis fe (fun x => run_state (k x) s)) end
     | @ProbF _ _ _ _ X mu k => mixed_bind mu (fun x => state_after n (s,k x))
     end).
Proof.
  unfold state_primitive_approx, stable_hitting_approx, state_primitive_kernel.
  destruct (observe t) as [a|u|X e k|X mu k].
  - etransitivity; [apply ret_equiv|]. rewrite stable_target_stableE. reflexivity.
  - etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
  - etransitivity; [apply ret_equiv|]. destruct e as [se|fe]; cbn [state_head_result].
    + destruct (state_response se s); destruct n; reflexivity.
    + rewrite stable_target_stableE. reflexivity.
  - etransitivity; [apply mixed_assoc|]. apply mixed_equiv. intro x.
    etransitivity; [apply ret_equiv|]. destruct n; reflexivity.
Qed.

Theorem state_primitive_tree_approx {A} n (c : cfg A) :
  equiv (state_primitive_approx n c)
    (ptree_hitting_approx (MF := MF) n (observe (run_state (snd c) (fst c)))).
Proof.
  revert c. induction n as [|n IH]; intros [s t]; cbn [fst snd];
    setoid_rewrite state_primitive_unfold; rewrite observe_run_state;
    destruct (observe t) as [a|u|X e k|X mu k];
    try (setoid_rewrite (hit_unfold E); cbn [state_after]; reflexivity).
  - destruct e as [se|fe]; [destruct (state_response se s)|];
      setoid_rewrite (hit_unfold E); cbn [state_after]; reflexivity.
  - setoid_rewrite (hit_unfold E). apply IH.
  - destruct e as [se|fe]; [destruct (state_response se s)|];
      setoid_rewrite (hit_unfold E); cbn [state_after]; [apply IH|reflexivity].
  - setoid_rewrite (hit_unfold E). apply mixed_equiv. intro x. apply IH.
Qed.

Definition state_phase_kernel {A} m (c : cfg A) :=
  sem_bind (ptree_hitting_approx (MF := MF) m (observe (snd c)))
    (fun h => sem_ret (state_head_result (fst c) h)).
Definition state_phase_grid {A} n m (c : cfg A) := stable_hitting_approx (state_phase_kernel m) n c.
Definition state_phase_split {A} j n m (c : cfg A) :=
  sem_bind (ptree_hitting_approx (MF := MF) j (observe (snd c)))
    (fun h => stable_target_approx (state_phase_kernel m) n (state_head_result (fst c) h)).
Definition state_phase_after {A} n m (c : cfg A) :=
  match n with O => sem_zero | S r => state_phase_grid r m c end.
Local Lemma phase_internalE {A} n m (c : cfg A) :
  stable_target_approx (state_phase_kernel m) n (SHInternal c) = state_phase_after n m c.
Proof. destruct n; reflexivity. Qed.

Lemma state_phase_grid_split {A} n m (c : cfg A) :
  equiv (state_phase_grid n m c) (state_phase_split m n m c).
Proof.
  unfold state_phase_grid, stable_hitting_approx, state_phase_kernel, state_phase_split.
  etransitivity; [apply finite_head_bind_assoc|].
  apply BindScheduling.bind_equiv_Proper; [reflexivity|intro h; apply ret_equiv].
Qed.

Lemma state_phase_split_le_primitive {A} j n m bound
    (Hpost : forall c : cfg A, sem_le (state_phase_after n m c) (state_primitive_approx bound c)) :
  forall c : cfg A, sem_le (state_phase_split j n m c) (state_primitive_approx (j+bound+1) c).
Proof.
  induction j as [|j IH]; intros [s t];
    replace (0+bound+1) with (S bound) by lia;
    try replace (S j+bound+1) with (S (S j+bound)) by lia;
    unfold state_phase_split; cbn [fst snd];
    setoid_rewrite (hit_unfold (stateE St +' E)); setoid_rewrite state_primitive_unfold;
    destruct (observe t) as [a|u|X e k|X mu k]; cbn [state_after].
  - setoid_rewrite ret_equiv. cbn [state_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite zero_equiv. apply sem_zero_le.
  - setoid_rewrite ret_equiv. destruct e as [se|fe]; cbn [state_head_result].
    + destruct (state_response se s) as [s' x].
      destruct n; apply Hpost.
    + rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc. apply mixed_bind_le_k. intro x.
    setoid_rewrite zero_equiv. apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [state_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - eapply sem_le_trans; [apply (IH (s,u))|]. apply stable_hitting_mono. lia.
  - setoid_rewrite ret_equiv. destruct e as [se|fe]; cbn [state_head_result].
    + destruct (state_response se s) as [s' x]. destruct n;
        (eapply sem_le_trans; [apply Hpost|apply stable_hitting_mono; lia]).
    + rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply (IH (s,k x))|]. apply stable_hitting_mono. lia.
Qed.

Theorem state_phase_grid_le_primitive {A} n m (c : cfg A) :
  sem_le (state_phase_grid n m c) (state_primitive_approx ((n+1)*(m+1)) c).
Proof.
  revert c. induction n as [|n IH]; intro c; setoid_rewrite state_phase_grid_split.
  - replace ((0+1)*(m+1)) with (m+0+1) by lia.
    apply state_phase_split_le_primitive. intro d. apply sem_zero_le.
  - replace ((S n+1)*(m+1)) with (m+(n+1)*(m+1)+1) by lia.
    apply state_phase_split_le_primitive. exact IH.
Qed.

Lemma state_primitive_le_phase_split {A} n m : n <= m -> forall c : cfg A,
  sem_le (state_primitive_approx n c) (state_phase_split n n m c).
Proof.
  induction n as [|n IH]; intro Hnm; intros [s t];
    setoid_rewrite state_primitive_unfold; unfold state_phase_split; cbn [fst snd];
    setoid_rewrite (hit_unfold (stateE St +' E));
    destruct (observe t) as [a|u|X e k|X mu k]; cbn [state_after].
  - setoid_rewrite ret_equiv. cbn [state_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - apply sem_zero_le.
  - setoid_rewrite ret_equiv. destruct e as [se|fe]; cbn [state_head_result].
    + destruct (state_response se s). apply sem_zero_le.
    + rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc. apply mixed_bind_le_k. intro x. apply sem_zero_le.
  - setoid_rewrite ret_equiv. cbn [state_head_result]. rewrite stable_target_stableE. apply sem_le_refl.
  - eapply sem_le_trans; [apply (IH ltac:(lia) (s,u))|].
    apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
  - setoid_rewrite ret_equiv. destruct e as [se|fe]; cbn [state_head_result].
    + destruct (state_response se s) as [s' x]. rewrite (phase_internalE (S n) m (s',k x)). cbn [state_phase_after].
      setoid_rewrite state_phase_grid_split.
      eapply sem_le_trans; [apply (IH ltac:(lia) (s',k x))|].
      apply sem_bind_le_mu. apply ptree_hitting_mono. lia.
    + rewrite stable_target_stableE. apply sem_le_refl.
  - setoid_rewrite mixed_assoc. apply mixed_bind_le_k. intro x.
    eapply sem_le_trans; [apply (IH ltac:(lia) (s,k x))|].
    apply sem_bind_le_k. intro h. apply stable_target_approx_increasing.
Qed.

Lemma state_phase_kernel_increasing {A} (c : cfg A) :
  sem_increasing (fun m => state_phase_kernel m c).
Proof. intro m. apply sem_bind_le_mu. apply ptree_hitting_increasing. Qed.
Lemma state_phase_grid_inner_increasing {A} n (c : cfg A) :
  sem_increasing (fun m => state_phase_grid n m c).
Proof.
  intro m. unfold state_phase_grid, stable_hitting_approx.
  eapply sem_le_trans; [apply sem_bind_le_mu; apply state_phase_kernel_increasing|].
  apply sem_bind_le_k. intro t. apply HandlerMachineAcceleration.target_kernel_mono.
  intro d. apply state_phase_kernel_increasing.
Qed.
Lemma state_phase_diagonal_increasing {A} (c : cfg A) :
  sem_increasing (fun n => state_phase_grid n n c).
Proof.
  intro n. eapply sem_le_trans; [apply state_phase_grid_inner_increasing|]. apply stable_hitting_increasing.
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}.

Lemma state_phase_kernel_lub {A} (c : cfg A) :
  sem_lub (fun m => state_phase_kernel m c) (state_machine_kernel c).
Proof. apply sem_bind_lub; [apply ptree_hitting_increasing|apply handler_complete_front_hitting]. Qed.

Lemma state_phase_grid_row_lub {A} n (c : cfg A) :
  sem_lub (fun m => state_phase_grid n m c) (stable_hitting_approx state_machine_kernel n c).
Proof.
  unfold state_phase_grid, stable_hitting_approx. apply sem_bind_diagonal_lub.
  - apply state_phase_kernel_increasing.
  - intros t m. apply HandlerMachineAcceleration.target_kernel_mono. intro d. apply state_phase_kernel_increasing.
  - apply state_phase_kernel_lub.
  - intro t. apply HandlerMachineAcceleration.target_kernel_lub;
      [apply state_phase_kernel_increasing|apply state_phase_kernel_lub].
Qed.

Theorem state_machine_hitting_sound {A} (c : cfg A) out :
  stable_hitting state_machine_kernel c out ->
  ptree_stable_hitting (MF := MF) (observe (run_state (snd c) (fst c))) out.
Proof.
  intro H. assert (Hdiag : sem_lub (fun n => state_phase_grid n n c) out).
  { eapply (sem_lub_double_diagonal (SI := FI) (SO := FO))
      with (grid := fun n m => state_phase_grid n m c)
           (row_out := fun n => stable_hitting_approx state_machine_kernel n c).
    - intro n. apply state_phase_grid_inner_increasing.
    - intros m n. apply stable_hitting_increasing.
    - intro n. apply state_phase_grid_row_lub.
    - exact H. }
  assert (Hphysical : stable_hitting state_primitive_kernel c out).
  { assert (HC : sem_lub (fun n => state_phase_grid n n c) out <->
        stable_hitting state_primitive_kernel c out).
    { unfold stable_hitting. apply sem_lub_cofinal.
      - apply state_phase_diagonal_increasing.
      - apply stable_hitting_increasing.
      - intro n. exists ((n+1)*(n+1)). apply state_phase_grid_le_primitive.
      - intro n. exists n. setoid_rewrite state_phase_grid_split.
        apply state_primitive_le_phase_split. lia. }
    exact (proj1 HC Hdiag). }
  unfold ptree_stable_hitting, stable_hitting in *.
  assert (HC : sem_lub (fun n => state_primitive_approx n c) out <->
      sem_lub (fun n => ptree_hitting_approx (MF := MF) n
        (observe (run_state (snd c) (fst c)))) out).
  { apply sem_lub_cofinal.
    - apply stable_hitting_increasing.
    - apply ptree_hitting_increasing.
    - intro n. exists n. apply (proj1 (state_primitive_tree_approx n c)).
    - intro n. exists n. apply (proj2 (state_primitive_tree_approx n c)). }
  exact (proj1 HC Hphysical).
Qed.
End Scheduling.
