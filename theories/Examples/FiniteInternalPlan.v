Set Universe Polymorphism.
From Coq Require Import Arith.PeanoNat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternal FiniteInternalPlan UnifiedFrontier PTreeKernel.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalPlanHitting.

Set Implicit Arguments.

Section NonuniformPlan.
Context {E MN : Type -> Type} {R : Type}.
Local Notation tree := (ptree E MN R).

Fixpoint delay_plan (n : nat) (t : tree) : finite_internal_plan (tau_prefix n t) :=
  match n with
  | 0 => FIPStop t
  | S m => FIPTau (delay_plan m t)
  end.

Fixpoint delay_path (n : nat) (t : tree) : internal_plan_path (delay_plan n t) :=
  match n with 0 => tt | S m => delay_path m t end.

Lemma delay_path_steps n t : internal_plan_steps (delay_plan n t) (delay_path n t) = n.
Proof. induction n; cbn; congruence. Qed.

Lemma delay_path_residual n t :
  internal_plan_residual (delay_plan n t) (delay_path n t) = t.
Proof. induction n; cbn; congruence. Qed.

Definition nonuniform_plan (mu : MN nat) (k : nat -> tree) :
    finite_internal_plan (Prob mu (fun n => tau_prefix n (k n))) :=
  FIPProb mu (fun n => delay_plan n (k n)).

(** Every path is finite, while path lengths over the syntax have no common
    bound.  This is not a claim that every n has positive sampling mass. *)
Example nonuniform_plan_unbounded (mu : MN nat) (k : nat -> tree) bound :
  exists z : internal_plan_path (nonuniform_plan mu k),
    bound < internal_plan_steps (nonuniform_plan mu k) z.
Proof.
  exists (existT (fun n => internal_plan_path (delay_plan n (k n)))
    bound (delay_path bound (k bound))).
  cbn [nonuniform_plan internal_plan_steps].
  rewrite delay_path_steps. apply Nat.lt_succ_diag_r.
Qed.

Example nonuniform_prefix_two (mu : MN nat) (k : nat -> tree) :
  internal_plan_at (nonuniform_plan mu k) 2
    (existT (fun n => internal_plan_path (delay_plan n (k n)))
      3 (delay_path 3 (k 3))) = Tau (Tau (k 3)).
Proof. reflexivity. Qed.

Example nonuniform_residual (mu : MN nat) (k : nat -> tree) n :
  internal_plan_residual (nonuniform_plan mu k)
    (existT (fun n => internal_plan_path (delay_plan n (k n)))
      n (delay_path n (k n))) = k n.
Proof.
  change (internal_plan_residual (delay_plan n (k n)) (delay_path n (k n)) = k n).
  apply delay_path_residual.
Qed.
End NonuniformPlan.

Section NonuniformHitting.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Example nonuniform_hitting_exact (mu : MN nat) (k : nat -> ptree E MN R) fuel :
  free_omega_qlift eq
    (@ptree_hitting_approx E MN (FreeOmega MN) FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R fuel
      (observe (Prob mu (fun n => tau_prefix n (k n)))))
    (internal_plan_budget (nonuniform_plan mu k) fuel).
Proof. apply internal_plan_hitting_approx. Qed.
End NonuniformHitting.

Unset Automatic Proposition Inductives.
Variant planE : Type -> Type := PlanAsk : planE bool.

CoFixpoint plan_spin : ptree planE SubEnum bool := Tau plan_spin.

Definition spin_prefix_plan : finite_internal_plan (Tau plan_spin) := FIPTau (FIPStop plan_spin).

Example spin_prefix_stops_before_divergence :
  internal_plan_steps spin_prefix_plan tt = 1 /\
  internal_plan_residual spin_prefix_plan tt = plan_spin.
Proof. split; reflexivity. Qed.

Definition visible_plan : finite_internal_plan
    (Tau (Vis PlanAsk (fun b => Ret b)) : ptree planE SubEnum bool) :=
  FIPTau (FIPStop (Vis PlanAsk (fun b => Ret b))).

Example visible_boundary_not_executed :
  internal_plan_steps visible_plan tt = 1 /\
  internal_plan_residual visible_plan tt = Vis PlanAsk (fun b => Ret b).
Proof. split; reflexivity. Qed.

Example visible_budget_zero :
  free_omega_qlift eq (internal_plan_budget visible_plan 0) FOZero.
Proof. apply FOQLSampleZero. Qed.

Example visible_budget_one :
  free_omega_qlift eq (internal_plan_budget visible_plan 1)
    (FORet (FHVis PlanAsk (fun b => Ret b))).
Proof.
  apply (@FOQLSampleRetL SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
  - apply sem_ae_ret_iff.
  - apply FOQLStructural, FOLRet. reflexivity.
Qed.

(** Completing a path may lose mass in a later subprobability sample.
    Hence projecting COMPLETED paths back to time zero is not the law of
    the primitive time-zero state.  Any online scheduler must account for
    this instead of claiming a mass-preserving prefix projection. *)
Definition killed_plan :
    finite_internal_plan (Prob (@subenum_zero bool) (fun _ => Ret true) : ptree planE SubEnum bool) :=
  FIPProb (@subenum_zero bool) (fun _ => FIPStop (Ret true)).

Example killed_plan_is_valid :
  @finite_internal planE SubEnum (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    FreeOmegaMixedMeasure bool
    (Prob (@subenum_zero bool) (fun _ => Ret true))
    (FOSample (@subenum_zero bool) (fun _ => FORet (Ret true))).
Proof. exact (internal_plan_frontier_valid killed_plan). Qed.

Example completed_paths_do_not_preserve_prefix_mass :
  ~ sem_same_mass
      (subenum_bind (internal_plan_measure killed_plan) (fun _ => subenum_ret true))
      (subenum_ret true).
Proof.
  intro Hmass.
  change (@sem_same_mass SubEnum SubEnum_SemanticMeasure bool bool
    subenum_zero (subenum_ret true)) in Hmass.
  assert (Hzero : @sem_ae SubEnum SubEnum_SemanticMeasure bool subenum_zero
    (fun _ => False)).
  { intros w x Hempty. contradiction. }
  pose proof (sem_lift_ae_transport_r Hmass Hzero) as Hret.
  apply (proj1 (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticMeasureDiracAELaws bool true
    (fun y => exists x : bool, True /\ False))) in Hret.
  destruct Hret as [x [_ Hfalse]]. exact Hfalse.
Qed.
