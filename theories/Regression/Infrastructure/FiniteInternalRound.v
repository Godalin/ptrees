(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Arith Require Import PeanoNat.
From Coq Require Import Lia.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq.Internal Require Import FiniteInternalPlan.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalRound.
From PTree.Regression.Infrastructure Require Import FiniteInternalPlan.

Set Implicit Arguments.

(** Stable guards do not execute external interaction or consume a step. *)
Example return_round_cost :
  internal_round_steps (FIPStop (Ret true : ptree planE SubEnum bool))
    (existT _ tt tt) = 0.
Proof. reflexivity. Qed.

Example visible_round_cost :
  internal_round_steps visible_plan (existT _ tt tt) = 1.
Proof. reflexivity. Qed.

Example visible_round_target :
  native_sample_value (internal_plan_round_native visible_plan) (existT _ tt tt) =
    SHStable (FHVis PlanAsk (fun b => Ret b)).
Proof. reflexivity. Qed.

Example visible_round_before_boundary :
  free_omega_qlift eq FOZero (internal_round_budget visible_plan 0).
Proof. exact (internal_round_hitting_approx visible_plan 0). Qed.

Example visible_round_at_boundary :
  free_omega_qlift eq (FORet (FHVis PlanAsk (fun b => Ret b)))
    (internal_round_budget visible_plan 1).
Proof. exact (internal_round_hitting_approx visible_plan 1). Qed.

(** A Tau guard really adds one step, even when it returns to a diverging
    residual.  No AST premise is needed for the round law. *)
Example divergent_round_cost :
  internal_round_steps spin_prefix_plan (existT _ tt tt) = 2.
Proof. reflexivity. Qed.

Example divergent_round_target :
  native_sample_value (internal_plan_round_native spin_prefix_plan) (existT _ tt tt) =
    SHInternal plan_spin.
Proof. reflexivity. Qed.

Example divergent_round_budget fuel :
  free_omega_qlift eq
    (@ptree_hitting_approx planE SubEnum (FreeOmega SubEnum)
      (FreeOmegaObservableSemanticMeasure
        (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool fuel
      (observe (Tau plan_spin)))
    (internal_round_budget spin_prefix_plan fuel).
Proof. apply internal_round_hitting_approx. Qed.

(** Sampling in the guard also consumes one step.  A zero-mass guard
    remains zero-mass; it is not silently replaced by a total sample. *)
Definition zero_guard_plan : finite_internal_plan
    (Prob (@subenum_zero bool) (fun b => Ret b) : ptree planE SubEnum bool) :=
  FIPStop (Prob (@subenum_zero bool) (fun b => Ret b)).

Example zero_guard_cost :
  internal_round_steps zero_guard_plan (existT _ tt true) = 1.
Proof. reflexivity. Qed.

Example zero_guard_measure_raw :
  subenum_raw (native_sample_measure (internal_plan_round_native zero_guard_plan)) = nil.
Proof. reflexivity. Qed.

Section NonuniformRound.
Context {E MN : Type -> Type} `{NI : SemanticMeasure MN} {R : Type}.

Definition nonuniform_round_path (mu : MN nat) (k : nat -> ptree E MN R) (n : nat) :
  native_sample_type (internal_plan_round_native (nonuniform_plan mu (fun n => Tau (k n)))).
Proof.
  refine (existT _ (existT _ n (delay_path n (Tau (k n)))) _).
  change (native_sample_type (internal_guard_native
    (internal_plan_residual (delay_plan n (Tau (k n))) (delay_path n (Tau (k n)))))).
  rewrite delay_path_residual. exact tt.
Defined.

(** Branch n spends n+1 steps in compression and another in its Tau
    guard.  There is no common bound on these syntactic path costs. *)
Example nonuniform_round_cost (mu : MN nat) (k : nat -> ptree E MN R) n :
  internal_round_steps (nonuniform_plan mu (fun n => Tau (k n)))
    (nonuniform_round_path mu k n) = S (S n).
Proof.
  change (S (internal_plan_steps (delay_plan n (Tau (k n)))
      (delay_path n (Tau (k n)))) + internal_guard_steps
    (internal_plan_residual (delay_plan n (Tau (k n)))
      (delay_path n (Tau (k n)))) = S (S n)).
  rewrite delay_path_steps, delay_path_residual.
  change (S n + 1 = S (S n)). lia.
Qed.
End NonuniformRound.
