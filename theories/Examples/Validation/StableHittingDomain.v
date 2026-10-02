(** Role: external mathematical-model example, not a reasoning dependency. *)
(** DS4 contracts: arbitrary hitting witnesses become valid automatically;
    visible interaction, divergence and native mass loss stay distinct. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Compatibility.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnumQ.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Variant domainE : Type → Type := Tick : domainE unit.
Local Notation tree := (ptree domainE SubEnumQ unit).
CoFixpoint silent_forever : tree := Tau silent_forever.
CoFixpoint silent_counter (n : nat) : tree := Tau (silent_counter (S n)).
CoFixpoint visible_forever : tree := Vis Tick (fun _ => visible_forever).
Definition native_loss : tree := Prob (@subenumQ_zero unit) (fun _ => Ret tt).

Section Tests.
Variable R : realType.
Local Notation D := (@ptree_domain_hitting R domainE unit).
Local Notation FI := (@FreeOmegaObservableSemanticMeasure SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation FO := (@FreeOmegaObservableSemanticOmega SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation hits := (@ptree_stable_hitting domainE SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure FO unit).

Example silent_hitting_bottom : oval_eq (D (observe silent_forever)) (oval_bottom R).
Proof. apply ptree_domain_hitting_spin. reflexivity. Qed.

(** The invariant endpoint also covers changing states, not just a
    definition whose observation is Tau of itself. *)
Example changing_silent_state_bottom n :
  oval_eq (D (observe (silent_counter n))) (oval_bottom R).
Proof.
  apply ptree_domain_hitting_zero.
  eapply (ptree_stable_hitting_tau_closed_zero (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with
    (P := fun t => exists m, t = silent_counter m).
  - intros t [m ->]. exists (silent_counter (S m)).
    split; [reflexivity|exists (S m); reflexivity].
  - exists n. reflexivity.
Qed.

Example native_loss_hitting_bottom : oval_eq (D (observe native_loss)) (oval_bottom R).
Proof. exact: ptree_domain_hitting_prob_zero. Qed.

(** This infinite service always reaches the NEXT visible head immediately.
    Stable mass one does not assert whole-program termination. *)
Example infinite_visible_service_mass_one : oval_mass (D (observe visible_forever)) = 1.
Proof. exact: ptree_domain_hitting_vis_mass. Qed.

Example ret_noncanonical_witness_valid :
  free_omega_admissible R (@FORet SubEnumQ (stable_head domainE SubEnumQ unit) (FHRet tt)).
Proof.
  apply (@stable_hitting_admissible R domainE unit (RetF tt)).
  apply (ptree_stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.

Example ret_noncanonical_witness_sound :
  free_omega_domain_denotes (@FORet SubEnumQ (stable_head domainE SubEnumQ unit) (FHRet tt))
    (D (RetF tt)).
Proof.
  apply (@stable_hitting_denotational_adequacy R domainE unit (RetF tt)).
  apply (ptree_stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.
End Tests.

(** The real recursive client supplies neither admissibility nor almost-sure
    termination nor an event-free signature. Arbitrary-witness theorem signatures
    are checked directly at their production owners. *)
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.FreeOmega.Validation Require Import Model StableHitting.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnumR.

Section RealTests.
Variable R : realType.
Local Notation MN := (SubEnumR R).
Local Notation native := (fun X => @subenumR_domain R X).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation hits := (@ptree_stable_hitting _ MN (FreeOmega MN)
  FI FreeOmegaMixedMeasure FO _).

Variable p : R.
Hypotheses (Hp : 0 <= p) (Hp1 : p <= 1).

(** p = 0 is allowed: infinite retry is still a valid subprobability.
    On success this program exposes an actual visible head. *)
CoFixpoint real_retry : ptree domainE MN unit :=
  Prob (subenumR_coin Hp Hp1) (fun b =>
    if b then Vis Tick (fun _ => Ret tt) else Tau real_retry).

Example real_recursive_frontier_auto :
  ∃ out, hits (observe real_retry) out ∧
    free_omega_modelable native out ∧
    free_omega_model_denotes native out
      (subenumR_ptree_domain_hitting (observe real_retry)).
Proof.
  exists (ptree_canonical_hitting (observe real_retry)).
  have H : hits (observe real_retry) (ptree_canonical_hitting (observe real_retry))
    by apply ptree_canonical_hitting_spec.
  split; [exact H|]. split.
  - exact: subenumR_stable_hitting_modelable H.
  - exact: subenumR_stable_hitting_denotational_adequacy H.
Qed.

(** Native mass loss is not an invalid raw term either. *)
Example real_native_loss_auto :
  free_omega_modelable native
    (ptree_canonical_hitting (ProbF (@subenumR_zero R unit)
      (fun _ => (Ret tt : ptree domainE MN unit)))).
Proof. apply ptree_canonical_hitting_modelable. Qed.

Example real_noncanonical_witness_auto :
  free_omega_modelable native
    (@FORet MN (stable_head domainE MN unit) (FHRet tt)).
Proof.
  apply (@subenumR_stable_hitting_modelable R domainE unit (RetF tt)).
  apply (ptree_stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.
End RealTests.
