(** Backend-specific external joint realization. The generic all-raw bidual
    bridge handles qlift derivations, including invalid intermediate terms.
    Only endpoints need modelability. No qlift induction or new capability. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import CountableSupport RelationalValidation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section JointRealization.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Theorem subenumR_qlift_sound {A B} (T : A -> B -> Prop)
    (t : FreeOmega (SubEnumR R) A) (u : FreeOmega (SubEnumR R) B)
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u -> oval_coupled T (free_omega_model Ht) (free_omega_model Hu).
Proof.
  intro H.
  exact (oval_bidual_coupled (subenumR_free_omega_model_countable Ht)
    (subenumR_free_omega_model_countable Hu) (subenumR_qlift_bidual Ht Hu H)).
Qed.

Theorem subenumR_qlift_joint_mass_support {A B} (T : A -> B -> Prop)
    (t : FreeOmega (SubEnumR R) A) (u : FreeOmega (SubEnumR R) B)
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u -> exists J : OmegaVal R (A * B),
    oval_joint T (free_omega_model Ht) (free_omega_model Hu) J /\
    oval_mass J = oval_mass (free_omega_model Ht) /\
    oval_mass J = oval_mass (free_omega_model Hu) /\
    oval_eval J (oval_indicator R (fun z => ~ T (fst z) (snd z))) = 0.
Proof.
  intro H; destruct (subenumR_qlift_sound Ht Hu H) as [J HJ].
  exists J; split; first exact HJ.
  split; first exact (proj1 HJ (fun _ => 1) (@oval_test_one R A)).
  split; first exact (proj1 (proj2 HJ) (fun _ => 1) (@oval_test_one R B)).
  exact (oval_joint_off_relation_zero HJ).
Qed.

Theorem subenumR_qlift_eq_sound_via_joint {A}
    (t u : FreeOmega (SubEnumR R) A)
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift eq t u -> oval_eq (free_omega_model Ht) (free_omega_model Hu).
Proof.
  intro H; apply (proj1 (oval_eq_coupled_iff _ _)).
  exact (subenumR_qlift_sound Ht Hu H).
Qed.
End JointRealization.
