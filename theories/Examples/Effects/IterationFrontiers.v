(** Role: supporting program/semantic example, not a flagship claim. *)
(** Complete, return-only and absorbing frontier iteration contracts.
    Preserve partial mass, inhabited signatures, empty responses and the S shift. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Interp Require Import FrontierIteration ReturnIteration.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.BindOrder.
Require PTree.Eq.UnifiedFrontier PTree.Eq.PrimitiveStableHitting PTree.Eq.PTreeKernel.
Require PTree.Interp.IterationMachine PTree.Interp.FrontierIteration.
Require PTree.Prob.FreeOmega.Definition.
Require PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.BindOrder.
Require PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Interp.FreeOmega.AbsorbingIteration.
Module FrontierIteration.
(** Complete MF steps, not a native return-kernel profile. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.BindOrder.
Import PTree.Eq.UnifiedFrontier PTree.Eq.PrimitiveStableHitting PTree.Eq.PTreeKernel.
Import PTree.Interp.IterationMachine PTree.Interp.FrontierIteration.

(** The generic owner loads no completion or concrete probability model. *)

Import PTree.Prob.FreeOmega.Definition.
Import PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.BindOrder.
Import PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Interp.FreeOmega.AbsorbingIteration.
Set Implicit Arguments.

Variant probeE : Type → Type := At : nat → probeE bool | Dead : probeE Empty_set.
Local Notation tree := (ptree probeE SubEnumQ).
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Section UnboundedMixedStep.
(** Any subprobability coin is permitted: there is no totality or positive
    success assumption. The step can search through arbitrarily many indices
    before exposing a retry, a return, or an offered event. *)
Variable coin : SubEnumQ bool.
CoFixpoint search (n : nat) : tree (nat + nat) :=
  Prob coin (fun b =>
    if b then Prob coin (fun c => Ret (if c then inl (S n) else inr n))
    else Prob coin (fun c =>
      if c then Vis (At n) (fun answer : bool => Ret (if answer then inl n else inr n))
      else Tau (search (S n)))).

(** This is a full MF-valued frontier, retaining the entire visible
    continuation. No finite native state/result distribution is supplied. *)
Definition search_front n : MF (stable_head probeE SubEnumQ (nat + nat)) :=
  FOLub (fun fuel => ptree_hitting_approx (FI := FI) (FO := FO)
    fuel (observe (search n))).

Lemma search_front_hitting n : hits (search n) (search_front n).
Proof. apply free_omega_qlift_refl. intros h. reflexivity. Qed.

Example unbounded_mixed_summary n :
  hits (PTree.iter search n) (complete_iteration_frontier search search_front n).
Proof. apply complete_iteration_hitting. exact search_front_hitting. Qed.

Example retry_is_internal n :
  iteration_summary_target search (FHRet (inl n)) = SHInternal n.
Proof. reflexivity. Qed.
Example return_is_absorbing n :
  iteration_summary_target search (FHRet (inr n)) = SHStable (FHRet n).
Proof. reflexivity. Qed.
Example visible_continuation_is_recursive n :
  iteration_summary_target search
    (FHVis (At n) (fun b : bool => Ret (if b then inl n else inr n))) =
  SHStable (FHVis (At n) (fun b : bool =>
    iter_active search (Ret (if b then inl n else inr n)))).
Proof. reflexivity. Qed.
Example empty_response_is_absorbing :
  iteration_summary_target search
    (FHVis Dead (fun x : Empty_set => match x with end)) =
  SHStable (FHVis Dead (fun x : Empty_set =>
    iter_active search (match x with end))).
Proof. reflexivity. Qed.
End UnboundedMixedStep.

Example zero_coin_allowed n :
  hits (PTree.iter (search subenumQ_zero) n)
    (complete_iteration_frontier (search subenumQ_zero)
      (search_front subenumQ_zero) n).
Proof. apply unbounded_mixed_summary. Qed.

Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

End FrontierIteration.

Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega PTree.Prob.Interface.KleisliIteration.
Require PTree.Eq.UnifiedFrontier PTree.Eq.PTreeKernel.
Require PTree.Interp.FrontierIteration PTree.Interp.ReturnIteration.
Require PTree.Prob.FreeOmega.Definition.
Require PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.BindOrder.
Require PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Module ReturnIteration.
(** The return-only bridge has an S shift, permits missing mass/divergence,
    and does not require the ambient signature to be empty. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Omega PTree.Prob.Interface.KleisliIteration.
Import PTree.Eq.UnifiedFrontier PTree.Eq.PTreeKernel.
Import PTree.Interp.FrontierIteration PTree.Interp.ReturnIteration.
Import PTree.Prob.FreeOmega.Definition.
Import PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.BindOrder.
Import PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Set Implicit Arguments.

Variant eventE : Type → Type := Ask : eventE bool.
Local Notation MN := SubEnumQ.
Local Notation MF := (FreeOmega MN).
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := SubEnumQ_SemanticOmega)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Section GeneralKernel.
Variable step : nat → ptree eventE MN (nat+bool).
Variable K : nat → MF (nat+bool).
Example shifted_round n i :
  @sem_eq MF FI _
    (iteration_summary_round (FI := FI) (FO := FO) step (iteration_return_front K) n i)
    (iteration_return_map (E := eventE) (MN := MN) (sem_iter_approx (MI := FI) (MO := FO) K (S n) i)).
Proof. apply iteration_summary_round_return_only; typeclasses eauto. Qed.

Example return_only_program i out
    (Hstep : ∀ j, hits (step j) (iteration_return_front K j))
    (Hiter : sem_iter (MI := FI) (MO := FO) K i out) :
  ∃ hs, hits (PTree.iter step i) hs ∧
    @sem_eq MF FI _ hs (iteration_return_map out).
Proof. eapply ptree_iter_return_only; try typeclasses eauto; eassumption. Qed.

Variable native : nat → MN (nat+bool).
Example native_compatibility i hs out :
  iteration_summary (FI := FI) (FO := FO) step (iteration_native_front native) i hs →
  mixed_iter (FI := FI) (FO := FO) native i out →
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
Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

End ReturnIteration.

Require PTree.Core.PTreeDefinition.
Require PTree.PTreeFacts.
Require PTree.Eq.Backend.SubEnumQ.
Require PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.AE PTree.Prob.Interface.Omega.
Require PTree.Prob.FreeOmega.Definition.
Require PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure.
Require PTree.Eq.PTreeKernel PTree.Eq.UnifiedFrontier.
Require PTree.Eq.FreeOmega.Hitting.
Require PTree.Interp.FreeOmega.IterationSummary.
Module IterationSummary.
(** Silent rounds in an inhabited event signature; no AST, finite-state,
    or finite full-result-limit premise. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import PTree.Core.PTreeDefinition.
Import PTree.PTreeFacts.
Import PTree.Eq.Backend.SubEnumQ.
Import PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.AE PTree.Prob.Interface.Omega.
Import PTree.Prob.FreeOmega.Definition.
Import PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure.
Import PTree.Eq.PTreeKernel PTree.Eq.UnifiedFrontier.
Import PTree.Eq.FreeOmega.Hitting.
Import PTree.Interp.FreeOmega.IterationSummary.
Set Implicit Arguments.

Variant questionE : Type → Type := Question : questionE bool.
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation NO := SubEnumQ_SemanticOmega.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Section ArbitraryKernel.
Variable kernel : nat → SubEnumQ (nat + (nat * bool)).
Definition delayed_round i : ptree questionE SubEnumQ (nat + (nat * bool)) :=
  Tau (Prob (kernel i) (fun x => Ret x)).

Example delayed_kernel_summary i :
  hits (PTree.iter delayed_round i) (iteration_frontier kernel i).
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  intro j. apply stable_hitting_tau.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.

Definition only_bit (h : stable_head questionE SubEnumQ (nat * bool)) :=
  match h with FHRet sb => Some (snd sb) | FHVis _ _ _ => None end.

(** Only the bit projection has a supplied native limit, not the nat/bit
    joint distribution. The state and returned nat remain unbounded. *)
Example projected_limit i (out : SubEnumQ (option bool)) :
  sem_lub (fun n => iteration_observation_round kernel
    (fun sb => Some (snd sb)) n i) out →
  free_omega_observes only_bit (iteration_frontier kernel i) out.
Proof. apply iteration_frontier_observes. reflexivity. Qed.

Example observer_rejects_visible k : only_bit (FHVis Question k) = None.
Proof. reflexivity. Qed.
End ArbitraryKernel.

(** Zero is a legitimate partial kernel; the summary does not assert totality. *)
Example zero_mass_summary :
  hits (PTree.iter (delayed_round (fun _ => sem_zero)) 0)
    (iteration_frontier (fun _ : nat => @sem_zero SubEnumQ NI NO (nat + (nat * bool))%type) 0).
Proof. apply delayed_kernel_summary. Qed.

(** Every round returns a retry, but the loop never returns a value. *)
Definition retry_kernel (i : nat) : SubEnumQ (nat + bool) := sem_ret (inl (S i)).
Example endless_retry_summary i :
  hits (PTree.iter (fun j => (Ret (inl (S j)) : ptree questionE SubEnumQ (nat + bool))) i)
    (iteration_frontier retry_kernel i).
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  intro j. apply stable_hitting_native_ret.
Qed.

Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

End IterationSummary.

Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.AE PTree.Prob.Interface.Omega.
Require PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Prob.FreeOmega.Definition.
Require PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.PTreeKernel PTree.Eq.UnifiedFrontier PTree.Eq.PStruct PTree.Eq.PEutt.
Require PTree.Eq.FreeOmega.Base PTree.Eq.FreeOmega.Hitting PTree.Eq.FreeOmega.Bind.
Require PTree.Interp.FreeOmega.AbsorbingIteration.
Module AbsorbingIteration.
(** Boundary probes for first-observation absorption, not new case analysis. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.AE PTree.Prob.Interface.Omega.
Import PTree.Prob.Backend.SubEnumQ.Representation PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Prob.FreeOmega.Definition.
Import PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.PTreeKernel PTree.Eq.UnifiedFrontier PTree.Eq.PStruct PTree.Eq.PEutt.
Import PTree.Eq.FreeOmega.Base PTree.Eq.FreeOmega.Hitting PTree.Eq.FreeOmega.Bind.
Import PTree.Interp.FreeOmega.AbsorbingIteration.
Set Implicit Arguments.

Variant deadE : Type → Type := DeadA : deadE Empty_set | DeadB : deadE Empty_set.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Definition dead_exit (_ : unit) : ptree deadE SubEnumQ bool :=
  Vis DeadA (fun x : Empty_set => match x with end).
Definition dead_front (_ : unit) :=
  FORet (FHVis DeadA (fun x : Empty_set => match x with end)) :
    FreeOmega SubEnumQ (stable_head deadE SubEnumQ bool).

Section Kernels.
(** No totality premise: includes zero-mass and partial native kernels. *)
Variable kernel : nat → SubEnumQ (nat + unit).
Definition round i : ptree deadE SubEnumQ (nat + unit) := Prob (kernel i) (fun v => Ret v).
Lemma round_hits i : hits (round i) (FOSample (kernel i) (fun v => FORet (FHRet v))).
Proof.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros v _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.
Lemma dead_exit_hits b : hits (dead_exit b) (dead_front b).
Proof. apply (stable_hitting_vis (FI := FI) (FO := FO)). Qed.

Example empty_response_frontier i :
  hits (PTree.bind (PTree.iter round i) dead_exit)
    (absorbing_frontier kernel dead_front i).
Proof. eapply absorbing_iteration_summary; [exact round_hits|exact dead_exit_hits]. Qed.

Example actual_eventful_loop_exists i : ∃ out,
  hits (PTree.iter (pstruct_iter_natural_step round dead_exit) i) out ∧
  @sem_lift (FreeOmega SubEnumQ) FI _ _
    (stable_head_rel eq (peutt (FI := FI) (FO := FO) eq))
    out (absorbing_frontier kernel dead_front i).
Proof. eapply absorbing_iteration_exists; [exact round_hits|exact dead_exit_hits]. Qed.
End Kernels.

Example zero_kernel_allowed :
  hits (PTree.bind (PTree.iter (round (fun _ => subenumQ_zero)) 0) dead_exit)
    (absorbing_frontier (fun _ : nat => @subenumQ_zero (nat + unit)%type) dead_front 0).
Proof. apply empty_response_frontier. Qed.

(** No response is executed to form the offered-event head. *)
Example dead_event_is_visible : dead_front tt = FORet (FHVis DeadA (fun x : Empty_set => match x with end)).
Proof. reflexivity. Qed.
Example distinct_dead_heads :
  (FHVis DeadA (fun x : Empty_set => match x with end) : stable_head deadE SubEnumQ bool) ≠
  FHVis DeadB (fun x : Empty_set => match x with end).
Proof. discriminate. Qed.

Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

End AbsorbingIteration.
