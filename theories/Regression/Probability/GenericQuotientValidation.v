(** Contracts for native-independent raw quotient validation. In particular,
    an invalid composition middle must never become a validity obligation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Coupling.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation
  PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure
  PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Continuity Observation Quotient.
Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
Fail Check PTree.Prob.Backend.SubEnumR.Representation.SubEnumR.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import Validation RelationalValidation.
From PTree.Regression.Backend Require Import SubEnumR SubEnumRRelational.
Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RealContracts.
Variable R : realType.
Local Notation M := (SubEnumR R).
Local Notation native := (fun X => @subenumR_domain R X).
Definition real_constant_unit : FreeOmega M unit := FOLub (fun _ => FORet tt).
Definition real_returns_true (_ : unit) (b : bool) := b = true.

Lemma real_invalid_to_ret :
  free_omega_qlift (fun (_ : bool) (_ : unit) => True) (real_alternating R) (FORet tt).
Proof.
  eapply FOQLComp with (mid := real_constant_unit) (T := fun _ _ => True) (U := eq).
  - apply FOQLLub=> n; apply FOQLStructural; constructor; exact I.
  - apply FOQLSym, FOQLLubConstantR, FOQLStructural; constructor; reflexivity.
  - intros x [] _; exact I.
Qed.

Lemma real_heterogeneous_invalid_middle :
  free_omega_qlift real_returns_true real_constant_unit (FORet true).
Proof.
  eapply FOQLComp with (mid := real_alternating R)
    (T := fun (_ : unit) (_ : bool) => True) (U := fun (_ : bool) b => b = true).
  - apply FOQLLub=> n; apply FOQLStructural; constructor; exact I.
  - eapply FOQLComp with (mid := FORet tt)
      (T := fun (_ : bool) (_ : unit) => True) (U := fun (_ : unit) b => b = true).
    + exact real_invalid_to_ret.
    + apply FOQLStructural, FOLRet; reflexivity.
    + intros x b [y [_ Hb]]; exact Hb.
  - intros x b [y [_ Hb]]; exact Hb.
Qed.

Example generic_real_middle_is_invalid : ~ free_omega_modelable native (real_alternating R).
Proof. exact: real_alternating_invalid. Qed.
Example generic_real_raw_constraints_through_invalid :
  model_upper_birel native real_returns_true real_constant_unit (FORet true).
Proof. apply subenumR_qlift_bidual_raw; exact real_heterogeneous_invalid_middle. Qed.
Lemma real_constant_valid : free_omega_modelable native real_constant_unit.
Proof. apply modelable_lub; [intro n; apply modelable_ret|intros n f Hf; exact: lexx]. Qed.
Example generic_real_endpoint_dual_through_invalid :
  oval_bidual real_returns_true (free_omega_model real_constant_valid)
    (free_omega_model (modelable_ret native true)).
Proof. apply subenumR_qlift_bidual; exact real_heterogeneous_invalid_middle. Qed.

Example generic_real_equality_is_not_validity :
  free_omega_qlift eq (real_alternating R) (real_alternating R) /\
  ~ free_omega_modelable native (real_alternating R).
Proof. split; [apply FOQLStructural, free_omega_lift_refl; intros x; reflexivity|exact: real_alternating_invalid]. Qed.

Example generic_real_missing_mass_preserved :
  ~ free_omega_qlift eq (@FOZero M unit) (FORet tt).
Proof.
  intro H; have Hr := proj2 (subenumR_qlift_bidual_raw H).
  have Hbad := Hr _ _ (oval_test_one R) (oval_test_one R) (fun x y _ => lexx (1 : R)).
  change (is_true ((1 : R) <= 0)) in Hbad.
  by rewrite ler10 in Hbad.
Qed.

Lemma real_crossed_qlift (mu : M bool) :
  free_omega_qlift eq (FOSample mu (fun b => FORet b))
    (FOSample (subenumR_map negb mu) (fun b => FORet (negb b))).
Proof.
  apply FOQLStructural; eapply FOLSample; [exact (subenumR_lift_map negb mu)|].
  intros x y Hxy; constructor; rewrite -Hxy negbK; reflexivity.
Qed.
Example generic_real_crossed_sqrt_tests f : oval_test f ->
  free_omega_model_upper native (FOSample (real_sqrt_coin R) (fun b => FORet b)) f =
  free_omega_model_upper native
    (FOSample (subenumR_map negb (real_sqrt_coin R)) (fun b => FORet (negb b))) f.
Proof. intro Hf; apply subenumR_qlift_eq_upper; [apply real_crossed_qlift|exact Hf]. Qed.

(** This mass is 1/2, not normalized to 1 by the quotient bridge. *)
Example generic_real_partial_sample_mass :
  free_omega_model_upper native (FOSample (duplicated_half R) (fun b => FORet b))
    (fun _ => 1) = (1 : R) / 2.
Proof.
  cbn [free_omega_model_upper]; change ((1 : R)/4 * 1 + ((1 : R)/4 * 1 + (0*1+0)) = 1/2).
  rewrite !mulr1 !add0r !addr0 -mulr2n -mulr_natl mulrA mulr1.
  have H4 : (4 : R) = 2 * 2 by rewrite -natrM.
  by rewrite H4 invfM mulrA mulfV ?pnatr_eq0 // mul1r.
Qed.

(** Exercise Observe itself, with a genuine Lub observation. *)
Lemma real_delayed_hitting :
  free_omega_observes (fun b => b) (real_delayed_dirac R) (subenumR_ret R true).
Proof.
  eapply FOOObserveLub with (outs := fun n => match n with O => subenumR_zero R | S _ => subenumR_ret R true end).
  - intros [|n]; constructor.
  - intros f Hf; split.
    + intros [|n]; [|exact: lexx].
      change (is_true (0 <= 1 * f true + 0)); rewrite mul1r addr0; exact (proj1 (Hf true)).
    + intros b Hb; exact (Hb 1%nat).
  - intros [|n]; [apply FOApproxZero|apply FOApproxRet; reflexivity].
Qed.
Example generic_real_lub_observation_tests f : oval_test f ->
  free_omega_model_upper native (real_delayed_dirac R) f = f true.
Proof.
  intro Hf; transitivity (oval_eval (subenumR_domain (subenumR_ret R true)) f).
  - eapply model_observes_upper; [exact (@subenumR_domain_ret R)|exact (@subenumR_domain_zero R)|
      exact (@subenumR_domain_bind R)|exact (@subenumR_native_model_lift R)|
      exact (@subenumR_native_model_lub R)|exact real_delayed_hitting|exact Hf].
  - exact (@subenumR_domain_ret R bool true f Hf).
Qed.

Definition real_nullable_chain (b : bool) (n : nat) : FreeOmega M bool :=
  if b then FORet true else FORet (if Nat.even n then false else true).
Lemma real_null_sample_lub_qlift :
  free_omega_qlift eq
    (FOSample (real_certain_coin R) (fun _ => FORet true))
    (FOLub (fun n => FOSample (real_certain_coin R) (fun b => real_nullable_chain b n))).
Proof.
  eapply FOQLSampleLub with (Good := fun b => b = true).
  - intros p b [H|[H|[]]] Hnz; inversion H; subst; [reflexivity|].
    exfalso; apply Hnz; exact: subrr.
  - intros b -> n; apply FOApproxRet; reflexivity.
  - intros b ->; change (free_omega_qlift eq (@FORet M bool true) (FOLub (fun _ => FORet true))).
    apply FOQLLubConstantR, FOQLStructural, FOLRet; reflexivity.
Qed.
Example generic_real_null_nonmonotone_chain :
  ~ free_omega_modelable native (FOLub (real_nullable_chain false)) /\
  free_omega_modelable native
    (FOLub (fun n => FOSample (real_certain_coin R) (fun b => real_nullable_chain b n))).
Proof.
  split; [exact: real_alternating_invalid|].
  apply (proj1 (subenumR_qlift_eq_modelable real_null_sample_lub_qlift)).
  apply modelable_sample=> b; apply modelable_ret.
Qed.

Example generic_real_retry_equality_transports_validity :
  free_omega_modelable native (FOLub (fun _ => FOLub (real_retry R))).
Proof.
  apply (proj1 (subenumR_qlift_eq_modelable
    (FOQLLubConstantR (FOQLStructural (free_omega_lift_refl (FOLub (real_retry R)) (fun x => Logic.eq_refl x)))))).
  exact: real_unbounded_retry_valid.
Qed.
End RealContracts.

Section HighUniverse.
Universe u v.
Variable R : realType.
Example generic_real_large_carriers (A : Type@{u}) (B : Type@{v}) :
  model_upper_birel (fun X => @subenumR_domain R X)
    (fun (_ : Type@{u}) (_ : Type@{v}) => True) (FORet A) (FORet B).
Proof. apply subenumR_qlift_bidual_raw; apply FOQLStructural, FOLRet; exact I. Qed.
End HighUniverse.

From PTree.Prob.Backend.SubEnum.FreeOmega Require Import RelationalValidation GenericValidation UpperQuotient.
From PTree.Regression.Fixtures Require Import FreeOmegaSamples.
Section RationalAgreement.
Variable R : realType.
Example generic_rational_tests_agree_with_DS5 {A B} (T : A -> B -> Prop) t u :
  free_omega_qlift T t u ->
  free_omega_upper_birel R T t u /\
  model_upper_birel (fun X => @PTree.Prob.Backend.SubEnum.Domain.subenum_domain R X) T t u.
Proof. intro H; split; [exact (free_omega_qlift_upper_birel R H)|exact (subenum_qlift_bidual_raw R H)]. Qed.
End RationalAgreement.
