(** DS4 contracts: arbitrary hitting witnesses become valid automatically;
    visible interaction, divergence and native mass loss stay distinct. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Admissibility.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnumQ.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Variant domainE : Type -> Type := Tick : domainE unit.
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

Example arbitrary_witness_valid t out :
  hits (observe t) out -> free_omega_admissible R out.
Proof. exact: stable_hitting_admissible. Qed.

Example arbitrary_witness_denotes t out :
  hits (observe t) out -> free_omega_domain_denotes out (D (observe t)).
Proof. exact: stable_hitting_denotational_adequacy. Qed.

Example return_is_dirac : oval_eq (D (RetF tt)) (oval_ret R (FHRet tt)).
Proof. exact: ptree_domain_hitting_ret. Qed.

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
