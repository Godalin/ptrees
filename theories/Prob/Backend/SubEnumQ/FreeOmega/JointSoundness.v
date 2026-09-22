(** Final DS5a external joint realization for FreeOmega SubEnumQ.
    Only endpoints require admissibility. The all-raw bidual bridge handles
    derivations through invalid intermediates; this file never unfolds qlift. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import Admissibility CouplingSoundness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Soundness.
Variable R : realType.
Local Notation qlift := (@free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

Theorem free_omega_qlift_sound {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_coupled T (free_omega_domain Ht) (free_omega_domain Hu).
Proof.
  intro H; destruct (free_omega_qlift_countable_constraints Ht Hu H) as [HL [HM HD]].
  exact (oval_bidual_coupled HL HM HD).
Qed.

(** Recover DS3 bounded equality through general joint realization. No claim
    identifies the existential joint with the separately constructed diagonal. *)
Theorem free_omega_qlift_eq_sound_via_joint {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift eq t u -> oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof.
  intro H; apply (proj1 (oval_eq_coupled_iff _ _)).
  exact (free_omega_qlift_sound Ht Hu H).
Qed.

(** The realized joint has exactly the original subprobability mass;
    its complement-of-relation observable has expectation zero. *)
Theorem free_omega_qlift_joint_mass_support {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> exists J : OmegaVal R (A * B),
    oval_joint T (free_omega_domain Ht) (free_omega_domain Hu) J /\
    oval_mass J = oval_mass (free_omega_domain Ht) /\
    oval_mass J = oval_mass (free_omega_domain Hu) /\
    oval_eval J (oval_indicator R (fun z => ~ T (fst z) (snd z))) = 0.
Proof.
  intro H; destruct (free_omega_qlift_sound Ht Hu H) as [J HJ].
  exists J; split; first exact HJ.
  split; first exact (proj1 HJ (fun _ => 1) (@oval_test_one R A)).
  split; first exact (proj1 (proj2 HJ) (fun _ => 1) (@oval_test_one R B)).
  exact (oval_joint_off_relation_zero HJ).
Qed.
End Soundness.
