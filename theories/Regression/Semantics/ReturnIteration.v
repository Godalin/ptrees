(** The return-only bridge has an S shift, permits missing mass/divergence,
    and does not require the ambient signature to be empty. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Interp Require Import FrontierIteration ReturnIteration.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure BindOrder.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
Set Implicit Arguments.

Variant eventE : Type -> Type := Ask : eventE bool.
Local Notation MN := SubEnumQ.
Local Notation MF := (FreeOmega MN).
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := SubEnumQ_SemanticOmega)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Section GeneralKernel.
Variable step : nat -> ptree eventE MN (nat+bool).
Variable K : nat -> MF (nat+bool).
Example shifted_round n i :
  @sem_eq MF FI _
    (iteration_summary_round (FI := FI) (FO := FO) step (iteration_return_front K) n i)
    (iteration_return_map (E := eventE) (MN := MN) (sem_iter_approx (MI := FI) (MO := FO) K (S n) i)).
Proof. apply iteration_summary_round_return_only; typeclasses eauto. Qed.

Example return_only_program i out
    (Hstep : forall j, hits (step j) (iteration_return_front K j))
    (Hiter : sem_iter (MI := FI) (MO := FO) K i out) :
  exists hs, hits (PTree.iter step i) hs /\
    @sem_eq MF FI _ hs (iteration_return_map out).
Proof. eapply ptree_iter_return_only; try typeclasses eauto; eassumption. Qed.

Variable native : nat -> MN (nat+bool).
Example native_compatibility i hs out :
  iteration_summary (FI := FI) (FO := FO) step (iteration_native_front native) i hs ->
  mixed_iter (FI := FI) (FO := FO) native i out ->
  @sem_eq MF FI _ hs (iteration_return_map out).
Proof. apply (iteration_summary_mixed_iter (NI := NI)); typeclasses eauto. Qed.
End GeneralKernel.

Definition immediate (_ : nat) : MF (nat+bool) := FORet (inr true).
Definition immediate_step (_ : nat) : ptree eventE MN (nat+bool) := Ret (inr true).
Example classical_round_zero_is_bottom i :
  sem_iter_approx (MI := FI) (MO := FO) immediate 0 i = FOZero.
Proof. reflexivity. Qed.
Example frontier_round_zero_already_returns i :
  iteration_summary_round (FI := FI) (FO := FO) immediate_step
    (iteration_return_front (FI := FI) immediate) 0 i = FORet (FHRet true).
Proof. reflexivity. Qed.

Definition retry (i : nat) : MF (nat+bool) := FORet (inl (S i)).
Lemma retry_approx_zero n i : sem_iter_approx (MI := FI) (MO := FO) retry n i = FOZero.
Proof. revert i; induction n; intro i; [reflexivity|apply IHn]. Qed.
Example endless_retry_is_zero i : sem_iter (MI := FI) (MO := FO) retry i FOZero.
Proof.
  eapply sem_lub_chain_proper with (chain := fun _ => FOZero).
  - intro n. rewrite retry_approx_zero. apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.
(** Fixed-point equations alone do not characterize divergence: the
    endlessly retrying loop also has this spurious, nonleast solution. *)
Example endless_retry_has_other_fixed_point i :
  sem_iter_step (MI := FI) retry (fun _ => FORet true) i = FORet true.
Proof. reflexivity. Qed.
Definition lost (_ : nat) : MF (nat+bool) := FOZero.
Lemma lost_approx_zero n i : sem_iter_approx (MI := FI) (MO := FO) lost n i = FOZero.
Proof. destruct n; reflexivity. Qed.
Example lost_kernel_is_zero i : sem_iter (MI := FI) (MO := FO) lost i FOZero.
Proof.
  eapply sem_lub_chain_proper with (chain := fun _ => FOZero).
  - intro n. rewrite lost_approx_zero. apply sem_eq_refl.
  - apply sem_lub_constant.
Qed.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.
