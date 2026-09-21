(** DS5a.3: arbitrary-carrier and final qlift joint realization. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
From PTree.Prob.Backend.Common Require Import CountableCoupling.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Lemma dirac_countable (R : realType) {A} (x : A) : oval_countably_supported (oval_ret R x).
Proof.
  exists (fun _ => Some x); intros f g Hf Hg Hfg; apply Hfg; exists O; reflexivity.
Qed.

Lemma bottom_countable (R : realType) A : oval_countably_supported (@oval_bottom R A).
Proof. exists (fun _ => None); intros f g Hf Hg Hfg; reflexivity. Qed.

Example empty_carrier_joint (R : realType) :
  oval_coupled (fun (_ : Empty_set) (_ : bool) => False) (oval_bottom R) (oval_bottom R).
Proof.
  apply oval_bidual_coupled; [exact: bottom_countable|exact: bottom_countable|].
  split; intros f g Hf Hg Hfg; exact: lexx.
Qed.

Section LargeCarriers.
Universe u v.
Variable R : realType.
(** Values are themselves types, on independently quantified universes. *)
Example type_carrier_joint (A : Type@{u}) (B : Type@{v}) :
  oval_coupled (fun (_ : Type@{u}) (_ : Type@{v}) => True) (oval_ret R A) (oval_ret R B).
Proof.
  apply oval_bidual_coupled; [exact: dirac_countable|exact: dirac_countable|].
  split; intros f g Hf Hg Hfg; apply Hfg; exact I.
Qed.
End LargeCarriers.

Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  Admissibility JointSoundness.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Regression.Probability Require Import
  FreeOmegaDomain FreeOmegaQuotientDomain FreeOmegaRelationalDomain CountableTransport.

Section Tests.
Variable R : realType.

Example duplicate_invalid_codes_joint :
  oval_coupled (fun (_ : unit) b => b = true) (oval_ret R tt) (oval_ret R true).
Proof.
  apply (@oval_bidual_coupled_on_enumerations R unit bool (fun _ b => b = true)
    (oval_ret R tt) (oval_ret R true) repeated_unit repeated_bool).
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - intros f g Hf Hg Hfg; apply Hfg; exists 1%N; reflexivity.
  - split; intros f g Hf Hg Hfg; apply Hfg; reflexivity.
Qed.

(** The existing evidence really uses FOQLComp with alternating_bool as its
    invalid intermediate on another carrier. Only the final endpoints are valid. *)
Example heterogeneous_joint_through_invalid :
  oval_coupled returns_true (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R bool true)).
Proof. apply free_omega_qlift_sound; exact heterogeneous_invalid_middle. Qed.

Example invalid_middle_stays_invalid : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Example equality_joint_recovers_ds3 :
  oval_eq (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R unit tt)).
Proof. apply free_omega_qlift_eq_sound_via_joint; exact equality_through_invalid_middle. Qed.

Example empty_endpoint_qlift_joint :
  oval_coupled (fun (_ : Empty_set) (_ : bool) => False)
    (free_omega_domain (@admissible_zero R Empty_set))
    (free_omega_domain (@admissible_zero R bool)).
Proof. apply free_omega_qlift_sound; apply FOQLStructural, FOLZero. Qed.

Definition partial_bool : FreeOmega SubEnum bool :=
  FOSample domain_fair (fun b => if b then FORet true else FOZero).
Definition partial_nat : FreeOmega SubEnum nat :=
  FOSample domain_fair (fun b => if b then FORet 7%N else FOZero).
Lemma partial_bool_valid : free_omega_admissible R partial_bool.
Proof. apply admissible_sample; intros []; [apply admissible_ret|apply admissible_zero]. Qed.
Lemma partial_nat_valid : free_omega_admissible R partial_nat.
Proof. apply admissible_sample; intros []; [apply admissible_ret|apply admissible_zero]. Qed.
Lemma partial_heterogeneous_qlift :
  free_omega_qlift (fun b n => b = true /\ n = 7%N) partial_bool partial_nat.
Proof.
  apply FOQLStructural, FOLSample with (S := eq).
  - exact (@sem_lift_refl SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureCoreLaws bool eq domain_fair (fun b => @Logic.eq_refl bool b)).
  - intros b c ->; destruct c; [apply FOLRet; auto|apply FOLZero].
Qed.

Example partial_joint_keeps_mass_and_support :
  exists J, oval_joint (fun b n => b = true /\ n = 7%N)
    (free_omega_domain partial_bool_valid) (free_omega_domain partial_nat_valid) J /\
    oval_mass J = oval_mass (free_omega_domain partial_bool_valid) /\
    oval_mass J = oval_mass (free_omega_domain partial_nat_valid) /\
    oval_eval J (oval_indicator R (fun z => ~ (fst z = true /\ snd z = 7%N))) = 0.
Proof. apply free_omega_qlift_joint_mass_support; exact partial_heterogeneous_qlift. Qed.

Example geometric_quotient_joint :
  oval_coupled eq (free_omega_domain (geometric_valid R))
    (free_omega_domain (geometric_valid R)).
Proof. apply free_omega_qlift_sound, free_omega_qlift_refl; intro n; reflexivity. Qed.

(** Soundness does not turn a raw qlift derivation into endpoint validity. *)
Example qlift_alone_still_not_admissible :
  free_omega_qlift eq alternating_bool alternating_bool /\
  ~ free_omega_admissible R alternating_bool.
Proof.
  split; [apply free_omega_qlift_refl; intro b; reflexivity|exact: alternating_bool_not_admissible].
Qed.
End Tests.

Section LargeFreeOmegaCarriers.
Universe u v.
Variable R : realType.
Example type_valued_qlift_joint (A : Type@{u}) (B : Type@{v}) :
  oval_coupled (fun (_ : Type@{u}) (_ : Type@{v}) => True)
    (free_omega_domain (@admissible_ret R Type@{u} A))
    (free_omega_domain (@admissible_ret R Type@{v} B)).
Proof. apply free_omega_qlift_sound; apply FOQLStructural, FOLRet; exact I. Qed.
End LargeFreeOmegaCarriers.
