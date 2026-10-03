(** Backend-specific external joint realization for FreeOmega SubEnumQ.
    Only endpoints require admissibility. The all-raw bidual bridge handles
    derivations through invalid intermediates; this file never unfolds qlift. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Domain.
From PTree.Prob.FreeOmega.Validation Require Import Model.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import CountableSupport Validation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Soundness.
Variable R : realType.
Local Notation qlift := (@free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Preferred endpoint: generic modelability, backend enumerable support,
    and the shared countable transport theorem. Legacy DS names live only in Compatibility;
    this module does not load the specialized evaluator. *)
Theorem subenumQ_qlift_sound {A B} (T : A → B → Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_modelable (λ X, @subenumQ_domain R X) t)
    (Hu : free_omega_modelable (λ X, @subenumQ_domain R X) u) :
  qlift T t u → oval_coupled T (free_omega_model Ht) (free_omega_model Hu).
Proof.
  intro H.
  exact (oval_bidual_coupled (subenumQ_free_omega_model_countable Ht)
    (subenumQ_free_omega_model_countable Hu) (subenumQ_generic_qlift_bidual Ht Hu H)).
Qed.

(** Recover DS3 bounded equality through general joint realization. No claim
    identifies the existential joint with the separately constructed diagonal. *)
Theorem subenumQ_qlift_eq_sound_via_joint {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_modelable (λ X, @subenumQ_domain R X) t) (Hu : free_omega_modelable (λ X, @subenumQ_domain R X) u) :
  qlift eq t u → oval_eq (free_omega_model Ht) (free_omega_model Hu).
Proof.
  intro H; apply (proj1 (oval_eq_coupled_iff _ _)).
  exact (subenumQ_qlift_sound Ht Hu H).
Qed.

(** The realized joint has exactly the original subprobability mass;
    its complement-of-relation observable has expectation zero. *)
Theorem subenumQ_qlift_joint_mass_support {A B} (T : A → B → Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_modelable (λ X, @subenumQ_domain R X) t) (Hu : free_omega_modelable (λ X, @subenumQ_domain R X) u) :
  qlift T t u → ∃ J : OmegaVal R (A * B),
    oval_joint T (free_omega_model Ht) (free_omega_model Hu) J ∧
    oval_mass J = oval_mass (free_omega_model Ht) ∧
    oval_mass J = oval_mass (free_omega_model Hu) ∧
    oval_eval J (oval_indicator R (λ z, ¬ T (fst z) (snd z))) = 0.
Proof.
  intro H; destruct (subenumQ_qlift_sound Ht Hu H) as [J HJ].
  exists J; split; first exact HJ.
  split; first exact (proj1 HJ (λ _, 1) (@oval_test_one R A)).
  split; first exact (proj1 (proj2 HJ) (λ _, 1) (@oval_test_one R B)).
  exact (oval_joint_off_relation_zero HJ).
Qed.
End Soundness.
