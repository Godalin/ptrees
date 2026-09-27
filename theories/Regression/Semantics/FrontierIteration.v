(** Complete MF steps, not a native return-kernel profile. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Interp Require Import IterationMachine FrontierIteration.

(** The generic owner loads no completion or concrete probability model. *)
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure BindOrder.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
From PTree.Interp.FreeOmega Require Import AbsorbingIteration.
Set Implicit Arguments.

Variant probeE : Type -> Type := At : nat -> probeE bool | Dead : probeE Empty_set.
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

Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.
