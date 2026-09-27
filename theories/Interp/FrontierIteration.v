(** Complete-step iteration summaries over an arbitrary frontier backend.
    Ret(inl i) retries; Ret(inr a) and Vis are absorbing observations.
    Visible continuations retain the actual recursive program. No event-free
    signature, totality, native representability, or global frontier choice
    operation is needed. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import Shallow PrimitiveStableHitting UnifiedFrontier PTreeKernel BindScheduling.
From PTree.Interp Require Import IterationMachine HandlerMachineAcceleration.
Set Implicit Arguments.
Unset Strict Implicit.

Section Summary.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {I A : Type} (step : I -> ptree E MN (I+A)).

Definition iteration_summary_target (h : stable_head E MN (I+A)) :
    stable_target I (stable_head E MN A) :=
  match h with
  | FHRet (inl i) => SHInternal i
  | FHRet (inr a) => SHStable (FHRet a)
  | @FHVis _ _ _ X e k =>
      SHStable (FHVis e (fun x => iter_active step (k x)))
  end.

Definition iteration_summary_kernel
    (front : I -> MF (stable_head E MN (I+A))) i :=
  sem_bind (front i) (fun h => sem_ret (iteration_summary_target h)).

Definition iteration_summary_round front n i :=
  stable_hitting_approx (iteration_summary_kernel front) n i.

Definition iteration_summary front i out :=
  sem_lub (fun n => iteration_summary_round front n i) out.

Context `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{BO : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MO : @MixedMeasureBindOrderLaws MN MF FI MX FO}.
Local Notation equiv := (@BindScheduling.equiv MF FI FO).
#[local] Existing Instance BindScheduling.equiv_equivalence.
#[local] Existing Instance BindScheduling.bind_equiv_Proper.

(** Client analysis can unfold complete rounds without primitive fuel.
    Round zero already keeps stable exits; only retries consume a round. *)
Lemma iteration_summary_round_unfold
    `{FC : @SemanticMeasureCoreLaws MF FI}
    `{FB : @SemanticMeasureBindLaws MF FI} front n i :
  sem_eq (iteration_summary_round front n i)
    (sem_bind (front i) (fun h =>
      match h with
      | FHRet (inl j) => match n with
          | O => sem_zero | S m => iteration_summary_round front m j end
      | FHRet (inr a) => sem_ret (FHRet a)
      | @FHVis _ _ _ X e k => sem_ret (FHVis e (fun x => iter_active step (k x)))
      end)).
Proof.
  unfold iteration_summary_round, stable_hitting_approx, iteration_summary_kernel.
  eapply sem_eq_trans; [apply sem_bind_assoc|].
  apply sem_bind_ae_proper.
  eapply sem_ae_mono; [|apply sem_ae_true]. intros h _.
  eapply sem_eq_trans; [apply sem_bind_ret_l|].
  destruct h as [[j|a]|X e k]; destruct n; apply sem_eq_refl.
Qed.

Definition iteration_summary_grid n m i :=
  iteration_summary_round
    (fun j => ptree_hitting_approx (MF := MF) m (observe (step j))) n i.

Lemma iteration_summary_round_increasing front i :
  sem_increasing (fun n => iteration_summary_round front n i).
Proof. apply stable_hitting_increasing. Qed.

Lemma iteration_summary_grid_machine n m i :
  equiv (iteration_summary_grid n m i) (iter_phase_grid step n m (step i)).
Proof.
  revert i; induction n as [|n IH]; intro i;
    unfold iteration_summary_grid, iteration_summary_round,
      iteration_summary_kernel, iter_phase_grid, iter_phase_kernel,
      stable_hitting_approx.
  all: etransitivity; [apply finite_head_bind_assoc|];
    symmetry; etransitivity; [apply finite_head_bind_assoc|]; symmetry;
    apply BindScheduling.bind_equiv_Proper; [reflexivity|intro h].
  all: etransitivity; [apply sem_bind_ret_order|];
    symmetry; etransitivity; [apply sem_bind_ret_order|]; symmetry.
  all: destruct h as [[j|a]|X e k];
    cbn [iteration_summary_target iter_head_result stable_target_approx];
    try reflexivity.
  apply IH.
Qed.

Lemma iteration_summary_grid_inner_increasing n i :
  sem_increasing (fun m => iteration_summary_grid n m i).
Proof.
  intro m. unfold iteration_summary_grid, iteration_summary_round,
    stable_hitting_approx.
  eapply sem_le_trans; [apply sem_bind_le_mu; apply sem_bind_le_mu;
    apply ptree_hitting_increasing|].
  apply sem_bind_le_k. intro target.
  apply HandlerMachineAcceleration.target_kernel_mono. intro j.
  apply sem_bind_le_mu. apply ptree_hitting_increasing.
Qed.

Lemma iteration_summary_grid_outer_increasing m i :
  sem_increasing (fun n => iteration_summary_grid n m i).
Proof. apply iteration_summary_round_increasing. Qed.

Lemma iteration_summary_grid_diagonal_increasing i :
  sem_increasing (fun n => iteration_summary_grid n n i).
Proof.
  intro n. eapply sem_le_trans; [apply iteration_summary_grid_inner_increasing|].
  apply iteration_summary_grid_outer_increasing.
Qed.

Context `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}.

Lemma iteration_summary_grid_hitting i out :
  sem_lub (fun n => iteration_summary_grid n n i) out <->
  ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) out.
Proof.
  change (sem_lub (fun n => iteration_summary_grid n n i) out <-> ptree_stable_hitting (MF := MF)
    (observe (iter_active step (step i))) out).
  rewrite <- (iter_phase_diagonal_tree step (step i) out).
  apply sem_lub_cofinal.
  - apply iteration_summary_grid_diagonal_increasing.
  - apply iter_phase_diagonal_increasing.
  - intro n. exists n. apply (proj1 (iteration_summary_grid_machine n n i)).
  - intro n. exists n. apply (proj2 (iteration_summary_grid_machine n n i)).
Qed.

Context `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{Fubini : @SemanticOmegaFubiniLaws MF FI FO}.
Variable front : I -> MF (stable_head E MN (I+A)).
Hypothesis Hfront : forall i,
  ptree_stable_hitting (MF := MF) (observe (step i)) (front i).

Lemma iteration_summary_kernel_lub i :
  sem_lub (fun m => iteration_summary_kernel
    (fun j => ptree_hitting_approx (MF := MF) m (observe (step j))) i)
    (iteration_summary_kernel front i).
Proof. apply sem_bind_lub; [apply ptree_hitting_increasing|apply Hfront]. Qed.

Lemma iteration_summary_grid_row_lub n i :
  sem_lub (fun m => iteration_summary_grid n m i)
    (iteration_summary_round front n i).
Proof.
  unfold iteration_summary_grid, iteration_summary_round, stable_hitting_approx.
  apply sem_bind_diagonal_lub.
  - intro m. apply sem_bind_le_mu. apply ptree_hitting_increasing.
  - intros target m. apply HandlerMachineAcceleration.target_kernel_mono.
    intro j. apply sem_bind_le_mu. apply ptree_hitting_increasing.
  - apply iteration_summary_kernel_lub.
  - intro target. apply HandlerMachineAcceleration.target_kernel_lub.
    + intros j m. apply sem_bind_le_mu. apply ptree_hitting_increasing.
    + apply iteration_summary_kernel_lub.
Qed.

(** Exact witness, not merely a coupling: front describes the actual step,
    including its actual visible continuations. The limit lives in MF. *)
Theorem iteration_summary_hitting i out :
  iteration_summary front i out ->
  ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) out.
Proof.
  intro H. apply (proj1 (iteration_summary_grid_hitting i out)).
  eapply (sem_lub_double_diagonal (SI := FI) (SO := FO))
    with (grid := fun n m => iteration_summary_grid n m i)
         (row_out := fun n => iteration_summary_round front n i).
  - intro n. apply iteration_summary_grid_inner_increasing.
  - intro m. apply iteration_summary_grid_outer_increasing.
  - intro n. apply iteration_summary_grid_row_lub.
  - exact H.
Qed.

Theorem iteration_summary_exists i :
  exists out, iteration_summary front i out /\
    ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) out.
Proof.
  destruct (sem_lub_exists (iteration_summary_round_increasing front i))
    as [out Hout].
  exists out; split; [exact Hout|apply iteration_summary_hitting; exact Hout].
Qed.

(** An independently obtained complete witness has the same semantic
    measure as the summary; this is not Coq equality of frontier syntax. *)
Theorem iteration_summary_hitting_eq i out actual :
  iteration_summary front i out ->
  ptree_stable_hitting (MF := MF) (observe (PTree.iter step i)) actual ->
  sem_eq actual out.
Proof.
  intros Hout Hactual. eapply ptree_stable_hitting_unique;
    [exact Hactual|apply iteration_summary_hitting; exact Hout].
Qed.
End Summary.
