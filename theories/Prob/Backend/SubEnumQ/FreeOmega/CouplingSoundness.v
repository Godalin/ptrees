(** Role: External relational soundness bridge, preserving raw intermediates.
    General qlift supplies dual/Hall constraints on admissible endpoints.
    These are NOT yet a general joint-realization theorem. Equality does
    have an explicit joint and agrees with DS3. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  Admissibility UpperRelational UpperQuotient QuotientSoundness CountableSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Soundness.
Variable R : realType.
Local Notation qlift := (@free_omega_qlift SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

(** Apply the all-raw theorem once. No induction on a qlift derivation,
    and no admissibility premise on any FOQLComp intermediate. *)
Theorem free_omega_qlift_domain_bidual {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_bidual T (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: free_omega_qlift_upper_birel. Qed.

Theorem free_omega_qlift_countable_constraints {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u ->
  oval_countably_supported (free_omega_domain Ht) /\
  oval_countably_supported (free_omega_domain Hu) /\
  oval_bidual T (free_omega_domain Ht) (free_omega_domain Hu).
Proof.
  intro H; split; first exact: free_omega_domain_countable.
  split; first exact: free_omega_domain_countable.
  exact (free_omega_qlift_domain_bidual Ht Hu H).
Qed.

Theorem free_omega_qlift_domain_mass {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> oval_mass (free_omega_domain Ht) = oval_mass (free_omega_domain Hu).
Proof. intro H; apply (@oval_bidual_mass R A B T); exact (free_omega_qlift_domain_bidual Ht Hu H). Qed.

Theorem free_omega_qlift_domain_hall {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift T t u -> forall P,
    oval_eval (free_omega_domain Ht) (oval_indicator R P) <=
    oval_eval (free_omega_domain Hu) (oval_indicator R (oval_rel_image T P)).
Proof. intro H; apply oval_dual_hall; exact (proj1 (free_omega_qlift_domain_bidual Ht Hu H)). Qed.

Theorem free_omega_qlift_eq_joint {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  qlift eq t u ->
  oval_joint eq (free_omega_domain Ht) (free_omega_domain Hu)
    (oval_bind (free_omega_domain Ht) (fun x => oval_ret R (x,x))).
Proof. intro H; apply oval_eq_joint; exact (free_omega_qlift_eq_sound Ht Hu H). Qed.

Theorem free_omega_qlift_eq_joint_agrees_ds3 {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  oval_coupled eq (free_omega_domain Ht) (free_omega_domain Hu) <->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: oval_eq_coupled_iff. Qed.
End Soundness.
