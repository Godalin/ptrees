(** Backend realization contracts, not a second audit of raw qlift cases.
    Real-weight unbounded retry is related to its Boolean-complement output;
    the realized joint is therefore genuinely relational, not just diagonal. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.StructuralMeasure
  PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import CountableSupport JointRealization.
From PTree.Regression.Backend Require Import SubEnumR SubEnumRRelational.
Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Contracts.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).
Definition retry_left := FOLub (real_retry R).
Definition retry_right := free_omega_bind retry_left (fun b => FORet (negb b)).
Definition complement (b c : bool) := c = negb b.

Lemma retry_left_modelable : free_omega_modelable native retry_left.
Proof. exact: real_unbounded_retry_valid. Qed.
Lemma retry_right_modelable : free_omega_modelable native retry_right.
Proof. apply modelable_bind; [exact retry_left_modelable|intro b; apply modelable_ret]. Qed.

Lemma retry_complement_qlift : free_omega_qlift complement retry_left retry_right.
Proof.
  apply FOQLLub=> n; apply FOQLStructural.
  induction n as [|n IH]; cbn [real_retry free_omega_bind].
  - apply FOLZero.
  - eapply FOLSample; [apply sem_lift_refl; intros x; reflexivity|].
    intros x y ->; destruct y; [apply FOLRet; reflexivity|exact IH].
Qed.

Example real_retry_external_joint :
  oval_coupled complement (free_omega_model retry_left_modelable)
    (free_omega_model retry_right_modelable).
Proof. apply subenumR_qlift_sound; exact retry_complement_qlift. Qed.

Example real_retry_joint_exact_mass_support : exists J : OmegaVal R (bool * bool),
  oval_joint complement (free_omega_model retry_left_modelable)
    (free_omega_model retry_right_modelable) J /\
  oval_mass J = oval_mass (free_omega_model retry_left_modelable) /\
  oval_mass J = oval_mass (free_omega_model retry_right_modelable) /\
  oval_eval J (oval_indicator R (fun z => ~ complement (fst z) (snd z))) = 0.
Proof. apply subenumR_qlift_joint_mass_support; exact retry_complement_qlift. Qed.

Example real_retry_equality_via_joint :
  oval_eq (free_omega_model retry_left_modelable) (free_omega_model retry_left_modelable).
Proof.
  apply subenumR_qlift_eq_sound_via_joint.
  apply FOQLStructural, free_omega_lift_refl; intros x; reflexivity.
Qed.

(** A cover does not certify probability validity. *)
Example invalid_real_lub_still_enumerable :
  free_omega_ae (oval_enumerated (subenumR_free_omega_enumerate (real_alternating R)))
    (real_alternating R) /\ ~ free_omega_modelable native (real_alternating R).
Proof. split; [apply subenumR_free_omega_enumerate_covers|exact: real_alternating_invalid]. Qed.

Definition partial_term := FOSample (duplicated_half R) (fun b => FORet b).
Lemma partial_term_modelable : free_omega_modelable native partial_term.
Proof. apply modelable_sample=> b; apply modelable_ret. Qed.
Lemma partial_term_mass : oval_mass (free_omega_model partial_term_modelable) = (1 : R)/2.
Proof.
  change ((1 : R)/4 * 1 + ((1 : R)/4 * 1 + (0*1+0)) = 1/2).
  rewrite !mulr1 !add0r !addr0 -mulr2n -mulr_natl mulrA mulr1.
  have H4 : (4 : R) = 2 * 2 by rewrite -natrM.
  by rewrite H4 invfM mulrA mulfV ?pnatr_eq0 // mul1r.
Qed.
Example real_partial_joint_not_normalized : exists J : OmegaVal R (bool * bool),
  oval_joint eq (free_omega_model partial_term_modelable)
    (free_omega_model partial_term_modelable) J /\ oval_mass J = (1 : R)/2.
Proof.
  have Hq : free_omega_qlift eq partial_term partial_term.
  { apply FOQLStructural, free_omega_lift_refl; intros x; reflexivity. }
  destruct (subenumR_qlift_joint_mass_support partial_term_modelable partial_term_modelable Hq)
    as [J [HJ [Hm _]]].
  exists J; split; [exact HJ|by rewrite Hm partial_term_mass].
Qed.
End Contracts.

Section LargeCarriers.
Universe u v.
Variable R : realType.
Example real_joint_large_heterogeneous (A : Type@{u}) (B : Type@{v}) :
  oval_coupled (fun (_ : Type@{u}) (_ : Type@{v}) => True)
    (free_omega_model (modelable_ret (fun X => @subenumR_domain R X) A))
    (free_omega_model (modelable_ret (fun X => @subenumR_domain R X) B)).
Proof. apply subenumR_qlift_sound; apply FOQLStructural, FOLRet; exact I. Qed.
End LargeCarriers.
